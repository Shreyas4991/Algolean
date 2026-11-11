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
* The conditional rule checks the selected branch. The loop rule uses an invariant and a
  decreasing natural-number measure to prove that the loop finishes.

Open `scoped TMQuery.Spec` to use these rules. They use the existing `Completes` relation,
which requires a successful run with finite interpreter fuel. Fuel exhaustion does not count
as success. Interpreter fuel is kept inside the proofs, separately from time and space costs.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Spec

open Cslib Cslib.Turing Cslib.FreeM Std.WP Lean.Order

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- An instruction must finish and establish the requested cost and machine state. -/
def handler : LHandler (TMQuery tm) (TMCost → TMState tm → Prop) EStack⟨⟩ where
  trans q := ⟨fun post _ initial s => ∃ delta final,
    Completes (q.result_type ▸ (FreeM.lift q)) s delta final ∧
      post (q.result_type.symm ▸ ()) (initial + delta) final⟩
  monotone q := by
    intro Q Q' E E' _ hQ initial s
    rintro ⟨delta, final, hc, hpost⟩
    exact ⟨delta, final, hc, hQ _ _ _ hpost⟩

/-- This lets `vcgen` use successful executions without exposing interpreter fuel. -/
scoped instance costHandler : HasHandler (TMQuery tm) (TMCost → TMState tm → Prop) EStack⟨⟩ :=
  ⟨handler⟩

open scoped Algolean.Algorithms.TMQuery.Spec

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
    change ∃ delta final, Completes (FreeM.lift q) s delta final ∧
      wp (next ()) post () (initial + delta) final at h
    obtain ⟨a, middle, hc, hp⟩ := h
    obtain ⟨b, final, hr, hpost⟩ := ih () (initial + a) middle hp
    exact ⟨a + b, final, hc.seq hr, by simpa [add_assoc] using hpost⟩

/-- A verified program finishes with the stated cost and machine state. -/
theorem completes {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {post : TMCost → TMState tm → Prop}
    (h : Triple p (fun initial current => initial = 0 ∧ current = s)
      (fun _ => post) ()) :
    ∃ delta final, Completes p s delta final ∧ post delta final := by
  have hw := h.le_wp 0 s ⟨rfl, rfl⟩
  simpa using sound p (fun _ => post) 0 s hw

/-- This proves an existing `Runs` statement from a cost-aware verification proof. -/
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
  exact ⟨0, s.write symbol, completes_write s symbol, by simpa using h⟩

/-- A move records its exact time and space costs and updates the machine state. -/
@[spec] theorem move_spec (direction : Dir)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (FreeM.lift (.move direction) : Prog (TMQuery tm) Unit)
      (fun initial s => post () (initial + s.moveCost direction) (s.move direction)) post () := by
  apply Triple.intro
  intro initial s h
  exact ⟨s.moveCost direction, s.move direction, completes_move s direction, h⟩

/-- Changing the control label leaves the tape, head position, and costs unchanged. -/
@[spec] theorem update_spec (label : tm.State)
    (post : Unit → TMCost → TMState tm → Prop) :
    Triple (FreeM.lift (.update label) : Prog (TMQuery tm) Unit)
      (fun initial s => post () initial {s with config.state := some label}) post () := by
  apply Triple.intro
  intro initial s h
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
  exact ⟨cost, final, hc.branch, hp⟩

/-- A loop invariant describes the accumulated cost and machine state before each test. -/
@[spec_invariant_type] def Invariant (tm : SingleTapeTM Γ) := TMCost → TMState tm → Prop

/--
The loop preserves its invariant and finishes when its condition becomes false. Each iteration
must decrease a natural-number measure. The invariant can record exact time and space costs
or bounds on them. The measure is used in the proof and adds no machine instructions.
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
  exact run (rank s) initial s hinv rfl

end Algolean.Algorithms.TMQuery.Spec
