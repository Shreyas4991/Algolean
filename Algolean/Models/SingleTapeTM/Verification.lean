/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.While

/-!
# Verifying single-tape Turing machine programs

* `Spec.completes` and `Spec.runs` let `vcgen` prove the existing correctness statements.
* The rules for writing, moving, and changing the state retain exact time and space costs.
* The conditional rule checks the selected branch. The loop rule proves that a natural number
  assigned to the current state gets smaller after every iteration, so the loop must finish.

Open `scoped Std.WP TMQuery.Spec` to use these rules. The handler comes from
`ModelStateM.costHandler` for `TMModel`. It hides a finite interpreter fuel budget and requires
a successful run. The theorem `handler_apply` relates this shared handler to `Completes`.
Interpreter fuel remains separate from time and space costs.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Spec

open Cslib Cslib.Turing Cslib.FreeM Std.WP Lean.Order

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This hides fuel in the existing state-and-cost handler and requires a successful run. -/
def handler : LHandler (TMQuery tm) (TMCost → TMState tm → Prop) EStack⟨⟩ where
  trans q := ⟨fun post _ initial s => ∃ fuel,
    ((TMModel tm).costHandler q).apply
      (fun result total final => final.fuel = 0 ∧ post result total final.machine)
      (fun _ => False) initial ⟨s, fuel⟩⟩
  monotone q := by
    intro Q Q' E E' _ hQ initial s
    rintro ⟨fuel, h⟩
    refine ⟨fuel, (TMModel tm).costHandler.monotone q _ _ _ _ (fun _ h => h) ?_ initial ⟨s, fuel⟩ h⟩
    intro result total final hpost
    exact ⟨hpost.1, hQ result total final.machine hpost.2⟩

/-- The shared handler records the same successful instruction executions as `Completes`. -/
@[simp] theorem handler_apply {α : Type} (q : TMQuery tm α)
    (post : α → TMCost → TMState tm → Prop) (initial : TMCost) (s : TMState tm) :
    (handler q).apply post () initial s =
      (∃ cost final, Completes (q.result_type ▸ (FreeM.lift q)) s cost final ∧
        post (q.result_type.symm ▸ ()) (initial + cost) final) := by
  cases q.result_type
  change (∃ fuel, wp ((TMModel tm).runQuery q)
    (fun result total final => final.fuel = 0 ∧ post result total final.machine)
    (fun _ => False) initial ⟨s, fuel⟩) = _
  simp only [AddWriterT.wp_apply_state_option,
    FuelExecMonad.Interpreter.runQuery_eq_execute, AddWriterT.run_mk]
  apply propext
  constructor
  · rintro ⟨fuel, h⟩
    cases hr : FuelExecMonad.execute (TMModel tm) fuel (FreeM.lift q) s with
    | none => simp [hr] at h
    | some pair =>
      obtain ⟨result, final⟩ := pair
      have hp : final.fuel = 0 ∧ post result.ret (initial + result.tell) final.machine := by
        simpa [hr] using h
      refine ⟨result.tell, final.machine, ⟨fuel, ?_⟩, by simpa using hp.2⟩
      cases result with | mk returned cost =>
      cases returned
      cases final with | mk machine remaining =>
      have hz : remaining = 0 := hp.1
      subst remaining
      exact hr
  · rintro ⟨cost, final, ⟨fuel, hc⟩, hp⟩
    refine ⟨fuel, ?_⟩
    have heq : FuelExecMonad.execute (TMModel tm) fuel (FreeM.lift q) s =
        some (⟨(), cost⟩, ⟨final, 0⟩) := hc
    simpa [heq] using (show (0 : Nat) = 0 ∧ post () (initial + cost) final from ⟨rfl, hp⟩)

/-- This lets `vcgen` use successful executions without exposing interpreter fuel. -/
scoped instance costHandler : HasHandler (TMQuery tm) (TMCost → TMState tm → Prop) EStack⟨⟩ :=
  ⟨handler⟩

open scoped Algolean.Algorithms.TMQuery.Spec

private theorem wp_query (q : TMQuery tm Unit)
    (post : Unit → TMCost → TMState tm → Prop) (initial : TMCost) (s : TMState tm) :
    wp (FreeM.lift q : Prog (TMQuery tm) Unit) post () initial s =
      (∃ cost final, Completes (FreeM.lift q) s cost final ∧
        post () (initial + cost) final) := by
  change (handler q).apply post () initial s = _
  exact handler_apply q post initial s

private theorem wp_liftBind (q : TMQuery tm Unit) (next : Unit → Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) (initial : TMCost) (s : TMState tm) :
    wp (FreeM.liftBind q next) post () initial s =
      (∃ cost final, Completes (FreeM.lift q) s cost final ∧
        wp (next ()) post () (initial + cost) final) := by
  change (handler q).apply (fun a => wp (next a) post ()) () initial s = _
  exact handler_apply q (fun a => wp (next a) post ()) initial s

/-- The assertions give a completed execution with exactly the recorded cost. -/
private theorem sound (p : Prog (TMQuery tm) Unit) (post : Unit → TMCost → TMState tm → Prop)
    (initial : TMCost) (s : TMState tm) (h : wp p post () initial s) :
    ∃ delta final, Completes p s delta final ∧ post () (initial + delta) final := by
  induction p generalizing initial s with
  | pure a =>
    cases a
    change post () initial s at h
    exact ⟨0, s, completes_pure s, by simpa using h⟩
  | liftBind q next ih =>
    cases q.result_type
    rw [wp_liftBind] at h
    obtain ⟨a, middle, hc, hp⟩ := h
    obtain ⟨b, final, hr, hpost⟩ := ih () (initial + a) middle hp
    exact ⟨a + b, final, hc.seq hr, by simpa [add_assoc] using hpost⟩

/-- A completed execution establishes its exact result in the verification rules. -/
private theorem complete (p : Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) (initial : TMCost)
    (s final : TMState tm) (cost : TMCost) (hc : Completes p s cost final)
    (hp : post () (initial + cost) final) : wp p post () initial s := by
  induction p generalizing initial s final cost with
  | pure a =>
    cases a
    obtain ⟨rfl, rfl⟩ := hc.unique (completes_pure s)
    change post () initial final
    simpa using hp
  | liftBind q next ih =>
    cases q.result_type
    obtain ⟨fuel, hr⟩ := hc
    change execute fuel ((FreeM.lift q) >>= next) s = _ at hr
    simp only [TMQuery.execute, FuelExecMonad.execute_bind] at hr
    cases hfirst : FuelExecMonad.execute (TMModel tm) fuel (FreeM.lift q) s with
    | none => simp [hfirst] at hr
    | some pair =>
      obtain ⟨first, middle⟩ := pair
      cases hrest : FuelExecMonad.execute (TMModel tm) middle.fuel
          (next first.ret) middle.machine with
      | none => simp [hfirst, hrest] at hr
      | some pair =>
        obtain ⟨rest, result⟩ := pair
        have hr' : first.tell + rest.tell = cost ∧ result = ⟨final, 0⟩ := by
          simpa [hfirst, hrest] using hr
        have hcost := hr'.1
        have hfinal := hr'.2
        have htrim := FuelExecMonad.execute_trim_fuel fuel (FreeM.lift q) s first middle hfirst
        have hq : Completes (FreeM.lift q) s first.tell middle.machine :=
          ⟨fuel - middle.fuel, by simpa using htrim.2⟩
        have hn : Completes (next ()) middle.machine rest.tell final :=
          ⟨middle.fuel, by simpa [hfinal] using hrest⟩
        rw [wp_liftBind]
        exact ⟨first.tell, middle.machine, hq,
          ih () (initial + first.tell) middle.machine final rest.tell hn
            (by simpa [← hcost, add_assoc] using hp)⟩

/-- An existing correctness proof can be used as a specification for a subprogram. -/
theorem of_completes {p : Prog (TMQuery tm) Unit} {s final : TMState tm} {cost : TMCost}
    (h : Completes p s cost final) (initial : TMCost) :
    Triple p (fun accumulated current => accumulated = initial ∧ current = s)
      (fun _ accumulated current => accumulated = initial + cost ∧ current = final) () := by
  apply Triple.intro
  rintro _ _ ⟨rfl, rfl⟩
  exact complete p _ _ _ _ _ h ⟨rfl, rfl⟩

/-- This reuses a completed run when the proof needs only its head-move count. -/
theorem steps {p : Prog (TMQuery tm) Unit} {s final : TMState tm} {cost : TMCost}
    (h : Completes p s cost final) (initial : Nat) :
    Triple p (fun accumulated current => accumulated.steps = initial ∧ current = s)
      (fun _ accumulated current =>
        accumulated.steps = initial + cost.steps ∧ current = final) () := by
  apply Triple.intro
  rintro accumulated current ⟨hi, hs⟩
  subst current
  exact complete p _ accumulated s final cost h (by simp [hi])

/-- A verified program finishes with the stated cost and machine state. -/
theorem completes {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {post : TMCost → TMState tm → Prop}
    (h : Triple p (fun initial current => initial = 0 ∧ current = s)
      (fun _ => post) ()) :
    ∃ delta final, Completes p s delta final ∧ post delta final := by
  have hw := h.le_wp 0 s ⟨rfl, rfl⟩
  simpa using sound p (fun _ => post) 0 s hw

/-- This gives the exact final state and cost from a verification proof. -/
theorem exact_completes {p : Prog (TMQuery tm) Unit} {s final : TMState tm} {cost : TMCost}
    (h : Triple p (fun initial current => initial = 0 ∧ current = s)
      (fun _ accumulated current => accumulated = cost ∧ current = final) ()) :
    Completes p s cost final := by
  obtain ⟨_, _, hc, rfl, rfl⟩ := completes h
  exact hc

/-- A verification proof gives the tape, head position, and time required by `Runs`. -/
theorem runs {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {output : BiTape Γ} {position : ℤ} {time : Nat}
    (h : Triple p (fun initial current => initial = 0 ∧ current = s)
      (fun _ cost final => final.config = ⟨s.config.state, output⟩ ∧
        final.headPos = position ∧ cost.steps = time) ()) :
    Runs p s output position time := by
  obtain ⟨cost, final, hc, ht, hp, hm⟩ := completes h
  exact ⟨cost, final, hc, ht, hp, hm⟩

/-- Writing changes the current cell and leaves the accumulated cost unchanged. -/
@[spec] theorem write_spec (symbol : Option Γ)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (FreeM.lift (.write symbol) : Prog (TMQuery tm) Unit)
      (fun initial s => post () initial (s.write symbol)) post () := by
  apply Triple.intro
  intro initial s h
  rw [wp_query]
  exact ⟨0, s.write symbol, completes_write s symbol, by simpa using h⟩

/-- A move records its exact time and space costs and updates the machine state. -/
@[spec] theorem move_spec (direction : Dir)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (FreeM.lift (.move direction) : Prog (TMQuery tm) Unit)
      (fun initial s => post () (initial + s.moveCost direction) (s.move direction)) post () := by
  apply Triple.intro
  intro initial s h
  rw [wp_query]
  exact ⟨s.moveCost direction, s.move direction, completes_move s direction, h⟩

/-- Changing the control label leaves the tape, head position, and costs unchanged. -/
@[spec] theorem update_spec (label : tm.State)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (FreeM.lift (.update label) : Prog (TMQuery tm) Unit)
      (fun initial s => post () initial {s with config.state := some label}) post () := by
  apply Triple.intro
  intro initial s h
  rw [wp_query]
  exact ⟨0, {s with config.state := some label}, completes_update s label, by simpa using h⟩

/-- A conditional needs a proof only for the branch selected by the current machine state. -/
@[spec] theorem branch_spec (condition : TMCondition tm) (yes no : Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (branch condition yes no)
      (fun initial s => wp (if condition.eval s.config then yes else no) post () initial s)
      post () := by
  apply Triple.intro
  intro initial s h
  obtain ⟨cost, final, hc, hp⟩ := sound _ post initial s h
  unfold branch
  rw [wp_query]
  exact ⟨cost, final, hc.branch, hp⟩

/-- A true condition requires a proof only for the first branch. -/
theorem branch_true_spec (condition : TMCondition tm) (yes no : Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (branch condition yes no)
      (fun initial s => condition.eval s.config = true ∧ wp yes post () initial s) post () := by
  apply Triple.intro
  rintro initial s ⟨hcondition, h⟩
  obtain ⟨cost, final, hc, hp⟩ := sound yes post initial s h
  unfold branch
  rw [wp_query]
  exact ⟨cost, final, Completes.branch (by simpa [hcondition] using hc), hp⟩

/-- A false condition requires a proof only for the second branch. -/
theorem branch_false_spec (condition : TMCondition tm) (yes no : Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (branch condition yes no)
      (fun initial s => condition.eval s.config = false ∧ wp no post () initial s) post () := by
  apply Triple.intro
  rintro initial s ⟨hcondition, h⟩
  obtain ⟨cost, final, hc, hp⟩ := sound no post initial s h
  unfold branch
  rw [wp_query]
  exact ⟨cost, final, Completes.branch (by simpa [hcondition] using hc), hp⟩

/--
Selecting a case runs its action when every test agrees that this is the chosen case.
The action's assertion then proves the result for the whole selection.
-/
theorem select_spec {α : Type} [DecidableEq α] (cases : List α)
    (test : α → TMCondition tm) (action : α → Prog (TMQuery tm) Unit)
    (chosen : α) (hmem : chosen ∈ cases) (post : Unit → TMCost → TMState tm → Prop) :
    Triple (select cases test action)
      (fun initial current =>
        (∀ candidate, (test candidate).eval current.config = decide (candidate = chosen)) ∧
        wp (action chosen) post () initial current) post () := by
  apply Triple.intro
  rintro initial current ⟨htest, hbody⟩
  obtain ⟨cost, final, hc, hp⟩ := sound (action chosen) post initial current hbody
  exact complete _ post initial current final cost
    (select_correct cases test action chosen current final cost hmem htest hc) hp

/-- A loop whose first test is false finishes without changing the state or cost. -/
theorem while_false_spec (condition : TMCondition tm) (body : Prog (TMQuery tm) Unit)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (whileLoop condition body)
      (fun initial s => condition.eval s.config = false ∧ post () initial s) post () := by
  apply Triple.intro
  rintro initial s ⟨hf, hp⟩
  unfold whileLoop
  rw [wp_query]
  exact ⟨0, s, completes_while_false _ _ _ hf, by simpa using hp⟩

/--
This checks one loop test and one iteration. The following iteration is named separately so
an induction hypothesis can verify it without unfolding the loop again.
-/
theorem while_step_spec (condition : TMCondition tm) (body loop : Prog (TMQuery tm) Unit)
    (hloop : loop = whileLoop condition body) (post : Unit → TMCost → TMState tm → Prop) :
    Triple (whileLoop condition body)
      (fun initial s => wp (if condition.eval s.config then do body; loop else pure ())
        post () initial s) post () := by
  apply Triple.intro
  intro initial s h
  obtain ⟨cost, final, ⟨fuel, hc⟩, hp⟩ := sound _ post initial s h
  unfold whileLoop
  rw [wp_query]
  refine ⟨cost, final, ⟨fuel + 1, ?_⟩, hp⟩
  change execute (fuel + 1) (whileLoop condition body) s = _
  by_cases hcondition : condition.eval s.config = true
  · simpa [execute_while_succ, hcondition, hloop] using hc
  · simpa [execute_while_succ, hcondition] using hc

/-- A loop invariant describes the accumulated cost and machine state before each test. -/
@[spec_invariant_type] def Invariant (tm : SingleTapeTM Γ) := TMCost → TMState tm → Prop

/--
The loop preserves its invariant and finishes when its condition becomes false. Each iteration
must make a chosen natural number smaller. This number depends on the current machine state.
The invariant can record exact time and space costs or bounds on them. The chosen number is
used only in the proof and adds no machine instructions.
-/
@[spec] theorem while_spec (condition : TMCondition tm) (body : Prog (TMQuery tm) Unit)
    (inv : Invariant tm) (rank : TMState tm → Nat)
    (step : ∀ n, Triple body
      (fun cost s => inv cost s ∧ condition.eval s.config = true ∧ rank s = n)
      (fun _ cost s => inv cost s ∧ rank s < n) ()) :
    Triple (whileLoop condition body) (fun cost s => inv cost s)
      (fun _ cost s => inv cost s ∧ condition.eval s.config = false) () := by
  have run (n : Nat) : ∀ initial s, inv initial s → rank s = n →
      ∃ cost final, Completes (whileLoop condition body) s cost final ∧
        inv (initial + cost) final ∧ condition.eval final.config = false := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro initial s hinv hrank
      by_cases hcondition : condition.eval s.config = true
      · obtain ⟨a, middle, hc, hmiddle, hlt⟩ :=
          sound body _ initial s ((step n).le_wp initial s ⟨hinv, hcondition, hrank⟩)
        obtain ⟨b, final, hr, hfinal, hexit⟩ :=
          ih (rank middle) hlt (initial + a) middle hmiddle rfl
        exact ⟨a + b, final, hc.while_step hcondition hr,
          by simpa [add_assoc] using hfinal, hexit⟩
      · exact ⟨0, s, completes_while_false _ _ _ (by simpa using hcondition),
          by simpa using hinv, by simpa using hcondition⟩
  apply Triple.intro
  intro initial s hinv
  unfold whileLoop
  rw [wp_query]
  exact run (rank s) initial s hinv rfl

end Algolean.Algorithms.TMQuery.Spec
