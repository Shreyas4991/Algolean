/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM
public import Std.Tactic.Do

/-!
# Verifying strict WordRAM programs

Open `scoped WordRAM.Spec Std.WP` to use the existing cost-aware `ModelStateM` handler.
Assertions observe the accumulated cost, physical machine state, and remaining interpreter fuel.
The initial cost is arbitrary. Fuel is separate from RAM time and space.

The failure postcondition must be false to establish completion within the supplied fuel budget.
`Spec.execute` uses `ModelStateM.wp_le_wp_runStateM` to extract that successful execution;
`Spec.completes` then gives the model's existing completion relation.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.Spec

open Cslib Cslib.FreeM Std.WP

/-- Reuse the joint state-and-cost handler, including the interpreter's fuel and failure. -/
scoped instance costHandler :
    HasHandler (WordRAM w k) (RAMCost w → ExecutionState w k → Prop) (Unit → Prop) :=
  timeAndSpaceCost.hasCostHandler

open scoped Algolean.Algorithms.WordRAM.Spec

/-- Query verification observes the exact joint execution or its failure postcondition. -/
@[simp] theorem costHandler_apply (q : WordRAM w k α)
    (post : α → RAMCost w → ExecutionState w k → Prop) (epost : Unit → Prop)
    (initial : RAMCost w) (s : ExecutionState w k) :
    (HasHandler.handler q).apply post epost initial s =
      match WordRAM.execute s.fuel (FreeM.lift q) s.machine with
      | none => epost ()
      | some (result, final) => post result.ret (initial + result.tell) final := by
  change wp (timeAndSpaceCost.runQuery q) post epost initial s = _
  simp only [AddWriterT.wp_apply_state_option,
    FuelExecMonad.Interpreter.runQuery_eq_execute, AddWriterT.run_mk]
  cases hr : WordRAM.execute s.fuel (FreeM.lift q) s.machine <;> simp_all [WordRAM.execute]

/-- A verified triple with a false failure postcondition supplies a successful run at this fuel. -/
theorem execute {p : Prog (WordRAM w k) α}
    {pre : RAMCost w → ExecutionState w k → Prop}
    {post : α → RAMCost w → ExecutionState w k → Prop}
    (h : Triple p pre post (fun _ => False))
    {initial : RAMCost w} {s : RAMState w k} {fuel : Nat} (hp : pre initial ⟨s, fuel⟩) :
    ∃ result final, WordRAM.execute fuel p s = some (result, final) ∧
      post result.ret (initial + result.tell) final := by
  have hw := timeAndSpaceCost.wp_le_wp_runStateM p post (fun _ => False)
    initial ⟨s, fuel⟩ (h.le_wp initial ⟨s, fuel⟩ hp)
  rw [AddWriterT.wp_apply_state_option] at hw
  cases hr : (p.runStateM timeAndSpaceCost).run ⟨s, fuel⟩ with
  | none => simp only [hr] at hw
  | some pair => exact ⟨pair.1, pair.2, hr, by simpa only [hr] using hw⟩

/-- A total verification proof yields the existing completion relation and its postcondition. -/
theorem completes {p : Prog (WordRAM w k) Unit}
    {pre : RAMCost w → ExecutionState w k → Prop}
    {post : Unit → RAMCost w → ExecutionState w k → Prop}
    (h : Triple p pre post (fun _ => False)) {initial : RAMCost w} {s : RAMState w k}
    {fuel : Nat} (hp : pre initial ⟨s, fuel⟩) :
    ∃ cost final, Completes p s cost final.machine ∧ post () (initial + cost) final := by
  obtain ⟨result, final, hr, hpost⟩ := execute h hp
  exact ⟨result.tell, final, completes_of_execute hr, by simpa using hpost⟩

/-- Primitive instructions consume one fuel unit and add their exact cost. The existing step
semantics supplies their register, flag, and memory updates by simplification. -/
@[spec] theorem primitive_spec (q : WordRAM w k Unit)
    (primitive : ∀ s, (step q pure s).program = pure ())
    (post : Unit → RAMCost w → ExecutionState w k → Prop) (epost : Unit → Prop) :
    Triple (FreeM.lift q : Prog (WordRAM w k) Unit)
      (fun initial s => 0 < s.fuel ∧ post () (initial + (step q pure s.machine).cost)
        ⟨(step q pure s.machine).machine, s.fuel - 1⟩) post epost := by
  apply Triple.intro
  rintro initial ⟨ram, fuel⟩ ⟨hf, hp⟩
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    change (HasHandler.handler q).apply post epost initial ⟨ram, fuel + 1⟩
    rw [costHandler_apply]
    have hstep : WordRAM.execute (fuel + 1) (FreeM.lift q) ram = _ :=
      FuelExecMonad.execute_lift_succ (I := interpreter w k) fuel q ram
    rw [hstep]
    simpa only [primitive, FuelExecMonad.execute_pure, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, add_zero, Nat.add_one_sub_one] using hp

/-- A branch consumes one unit of interpreter fuel and verifies only its selected body. -/
@[spec] theorem branch_spec (op : CmpOp) (yes no : Prog (WordRAM w k) Unit)
    (post : Unit → RAMCost w → ExecutionState w k → Prop) (epost : Unit → Prop) :
    Triple (branch op yes no)
      (fun initial s => 0 < s.fuel ∧
        wp (if s.machine.Flags op then yes else no) post epost initial
          {s with fuel := s.fuel - 1}) post epost := by
  apply Triple.intro
  rintro initial ⟨ram, fuel⟩ ⟨hf, hp⟩
  cases fuel with
  | zero => contradiction
  | succ fuel =>
    have hp' : wp (if ram.Flags op then yes else no) post epost initial ⟨ram, fuel⟩ := by
      simpa using hp
    have hw := timeAndSpaceCost.wp_le_wp_runStateM
      (if ram.Flags op then yes else no) post epost initial ⟨ram, fuel⟩ hp'
    rw [AddWriterT.wp_apply_state_option] at hw
    change (HasHandler.handler (WordRAM.branchCode op (Internal.instructions yes)
      (Internal.instructions no))).apply post epost initial ⟨ram, fuel + 1⟩
    rw [costHandler_apply]
    rw [← branch, execute_branch_succ,
      ← apply_ite (fun p => WordRAM.execute fuel p ram)]
    cases hr : WordRAM.execute fuel (if ram.Flags op then yes else no) ram
    all_goals
      simp only [WordRAM.execute, FuelExecMonad.execute] at hr
      simpa only [hr] using hw

/-- A loop invariant records accumulated resources, machine state, and the remaining fuel. -/
@[spec_invariant_type] def Invariant (w k : Nat) := RAMCost w → ExecutionState w k → Prop

/-- Verify a loop within its supplied fuel budget. The invariant reserves one fuel unit for
each test. The body starts after that test and must reestablish the invariant before the next
test. The exit rule accounts for the final test. Shared execution lemmas supply the decreasing
fuel measure; no additional machine instructions or cost are introduced. -/
@[spec] theorem while_spec (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (inv : Invariant w k) (post : Unit → RAMCost w → ExecutionState w k → Prop)
    (enough : ∀ cost s, inv cost s → 0 < s.fuel)
    (exit : ∀ cost s, inv cost s → s.machine.Flags op = false →
      post () cost { s with fuel := s.fuel - 1 })
    (body_spec : Triple body
      (fun cost s => inv cost { s with fuel := s.fuel + 1 } ∧ s.machine.Flags op = true)
      (fun _ cost s => inv cost s) (fun _ => False)) :
    Triple (whileLoop op body) (fun cost s => inv cost s) post (fun _ => False) := by
  have run (fuel : Nat) : ∀ initial ram, inv initial ⟨ram, fuel⟩ →
      ∃ cost final, WordRAM.execute fuel (whileLoop op body) ram = some (⟨(), cost⟩, final) ∧
        post () (initial + cost) final := by
    induction fuel using Nat.strong_induction_on with
    | h fuel ih =>
      intro initial ram hinv
      have hf := enough initial ⟨ram, fuel⟩ hinv
      cases fuel with
      | zero => contradiction
      | succ fuel =>
        by_cases hflag : ram.Flags op = true
        · have hp : inv initial {machine := ram, fuel := fuel + 1} ∧ ram.Flags op = true :=
            ⟨hinv, hflag⟩
          obtain ⟨⟨⟨⟩, a⟩, middle, ha, hmiddle⟩ := execute body_spec hp
          have hle := (FuelExecMonad.execute_trim_fuel fuel body ram ⟨(), a⟩ middle ha).1
          obtain ⟨b, final, hb, hpost⟩ :=
            ih middle.fuel (by omega) (initial + a) middle.machine hmiddle
          refine ⟨a + b, final, ?_, ?_⟩
          · simp [hflag, WordRAM.execute, ha, hb]
          · simpa [add_assoc] using hpost
        · have hexit : ram.Flags op = false := by simpa using hflag
          exact ⟨0, ⟨ram, fuel⟩, by simp [hexit],
            by simpa using exit initial ⟨ram, fuel + 1⟩ hinv hexit⟩
  apply Triple.intro
  intro initial s hinv
  change (HasHandler.handler (WordRAM.whileCode op (Internal.instructions body))).apply
    post (fun _ => False) initial s
  rw [costHandler_apply, ← whileLoop]
  obtain ⟨cost, final, hr, hpost⟩ := run s.fuel initial s.machine hinv
  simpa only [hr] using hpost

end Algolean.Algorithms.WordRAM.Spec
