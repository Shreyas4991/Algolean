/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component

/-!
# Branch composition of single-tape query procedures
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
    simpa [execute_bind, execute_branch_succ, hguard] using hr

end TMQuery

end Algolean.Algorithms

namespace Algolean.Algorithms.Component

open Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {ι : Type} {pre : ι → TMState tm → Prop}
variable {post : ι → TMState tm → TMCost → TMState tm → Prop}

/-- Verify each branch under its guard, then select it using a condition inside the model. -/
@[simps program] def branch (condition : TMCondition tm)
    (yes : Component tm (fun i s => pre i s ∧ condition.eval s.config = true) post)
    (no : Component tm (fun i s => pre i s ∧ condition.eval s.config = false) post) :
    Component tm pre post where
  program := TMQuery.branch condition yes.program no.program
  correct i s hs := by
    by_cases h : condition.eval s.config = true
    · obtain ⟨cost, final, hc, hp⟩ := yes.correct i s ⟨hs, h⟩
      exact ⟨cost, final, Completes.branch (by simpa [h] using hc), hp⟩
    · obtain ⟨cost, final, hc, hp⟩ := no.correct i s ⟨hs, by simpa using h⟩
      exact ⟨cost, final, Completes.branch (by simpa [h] using hc), hp⟩

end Algolean.Algorithms.Component
