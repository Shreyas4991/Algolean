/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Branch composition of single-tape query procedures

Conditions are evaluated inside the machine model. Only the selected branch contributes
execution costs and changes the machine state.

## Main definitions and results

* `TMQuery.Completes.branch` and `TMQuery.Runs.branch` lift the selected branch's contract.
* `TMQuery.Runs.branch_seq` carries the selected branch's contract through a continuation.
* `Component.branch` builds a verified component from proofs for both guarded branches.
* `TMQuery.select` tests a fixed finite list of cases and runs the first matching case.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A branch executes only its selected procedure. -/
theorem Completes.branch {condition : TMCondition tm} {yes no : Prog (TMQuery tm) Unit}
    {s t : TMState tm} {cost : TMCost}
    (h : Completes (if condition.eval s.config then yes else no) s cost t) :
    Completes (branch condition yes no) s cost t := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  split at h <;> simp_all

/-- Lift a selected branch's tape and resource contract to the machine-controlled branch. -/
theorem Runs.branch {condition : TMCondition tm} {yes no : Prog (TMQuery tm) Unit}
    {s : TMState tm} {output : BiTape Symbol} {pos : ℤ} {time : ℕ}
    (h : Runs (if condition.eval s.config then yes else no) s output pos time) :
    Runs (branch condition yes no) s output pos time := by
  obtain ⟨cost, final, hc, ht, hp, hm⟩ := h
  exact ⟨cost, final, hc.branch, ht, hp, hm⟩

/-- Select a branch and then execute its continuation, keeping the shared state and cost. -/
theorem Runs.branch_seq {condition : TMCondition tm} {yes no p : Prog (TMQuery tm) Unit}
    {s : TMState tm} {output : BiTape Symbol} {pos : ℤ} {time : ℕ}
    (h : Runs (do (if condition.eval s.config then yes else no); p) s output pos time) :
    Runs (do TMQuery.branch condition yes no; p) s output pos time := by
  obtain ⟨cost, u, ⟨fuel, hr⟩, hc, hp, ht⟩ := h
  refine ⟨cost, u, ⟨fuel + 1, ?_⟩, hc, hp, ht⟩
  cases hguard : condition.eval s.config <;>
    simpa [FuelExecMonad.execute_bind, execute_branch_succ, hguard] using hr

/--
This constructs a Turing machine program containing nested conditionals. For `cases = [a, b, c]`,
the program first checks `test a` against the current tape and state. If it is true, the program
runs `action a` and skips the remaining tests. Otherwise it checks `test b`, then `test c` if
needed. If all tests are false, it finishes without changing the machine.

The list `cases` and the functions `test` and `action` are supplied when constructing the program.
They are part of that program's definition and are not read from the tape during execution.
Fixing these three arguments gives one finite program that can run on every input length.
For a single machine, they must be chosen independently of the input and its length. Choosing
different lists or instructions for different input lengths would give a family of programs.
-/
def select {α : Type} (cases : List α) (test : α → TMCondition tm)
    (action : α → Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit :=
  match cases with
  | [] => pure ()
  | candidate :: rest => branch (test candidate) (action candidate) (select rest test action)

/--
If `chosen` appears in `cases` and the tests succeed exactly for values equal to `chosen`,
the program runs `action chosen`. It has the same final machine state, head moves, and extra
tape cells as that action.
-/
theorem select_correct {α : Type} [DecidableEq α] (cases : List α)
    (test : α → TMCondition tm) (action : α → Prog (TMQuery tm) Unit)
    (chosen : α) (s final : TMState tm) (cost : TMCost)
    (hmem : chosen ∈ cases)
    (htest : ∀ candidate, (test candidate).eval s.config = decide (candidate = chosen))
    (haction : Completes (action chosen) s cost final) :
    Completes (select cases test action) s cost final := by
  induction cases with
  | nil => simp at hmem
  | cons candidate rest ih =>
    simp only [select]
    apply Completes.branch
    by_cases heq : candidate = chosen
    · subst candidate
      simpa [htest] using haction
    · have hrest : chosen ∈ rest := by simpa [Ne.symm heq] using hmem
      simpa [htest, heq] using ih hrest

/-- If every test fails, selecting from the fixed list leaves the whole machine unchanged. -/
theorem select_none {α : Type} (cases : List α) (test : α → TMCondition tm)
    (action : α → Prog (TMQuery tm) Unit) (s : TMState tm)
    (htest : ∀ candidate ∈ cases, (test candidate).eval s.config = false) :
    Completes (select cases test action) s 0 s := by
  induction cases with
  | nil => exact completes_pure s
  | cons candidate rest ih =>
    unfold select
    apply Completes.branch
    simpa [htest candidate (by simp)] using
      ih (fun a ha => htest a (by simp [ha]))

end TMQuery

end Algolean.Algorithms

namespace Algolean.Algorithms.Component

open Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {ι : Type} {pre : ι → TMState tm → Prop}
variable {post : ι → TMState tm → TMCost → TMState tm → Prop}

/-- Verify each branch under its guard, then select it using a condition inside the model. -/
@[simps program] def branch (condition : TMCondition tm)
    (yes : Component tm (fun i s => pre i s ∧ condition.eval s.config = true) post)
    (no : Component tm (fun i s => pre i s ∧ condition.eval s.config = false) post) :
    Component tm pre post where
  program := do [TMQuery tm]
    ifₜ condition then
      yes.program
    else
      no.program
  correct i s hs := by
    by_cases h : condition.eval s.config = true
    · obtain ⟨cost, final, hc, hp⟩ := yes.correct i s ⟨hs, h⟩
      exact ⟨cost, final, Completes.branch (by simpa [h] using hc), hp⟩
    · obtain ⟨cost, final, hc, hp⟩ := no.correct i s ⟨hs, by simpa using h⟩
      exact ⟨cost, final, Completes.branch (by simpa [h] using hc), hp⟩

end Algolean.Algorithms.Component
