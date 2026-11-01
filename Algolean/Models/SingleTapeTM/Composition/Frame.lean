/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic

/-!
# Reusing a run with different tape bookkeeping

A program reads only tape symbols and the control state. Changing the head's coordinate,
the record of allocated cells, or the record of head visits does not change which instructions
run, whether the program finishes, its tape result, or its number of head moves. Previously
allocated cells can change how much additional storage the run needs.

These results let a second procedure keep the first procedure's allocated tape and visits.
The final two lemmas also show that unused interpreter fuel can be removed from a completed run.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

theorem step_config_time {s t : TMState tm} (h : s.config = t.config)
    (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) :
    (step q rest s).machine.config = (step q rest t).machine.config ∧
      (step q rest s).code = (step q rest t).code ∧
      (step q rest s).cost.steps = (step q rest t).cost.steps := by
  cases q with
  | move direction => cases direction <;> simp [step, h]
  | _ => simp [step, h]

theorem runCode_config_time (fuel : ℕ) (code : List (TMQuery tm Unit))
    (s t : TMState tm) (h : s.config = t.config) :
    (runCode fuel code s).map (fun (r, u) => (u.machine.config, r.tell.steps, u.fuel)) =
      (runCode fuel code t).map (fun (r, u) => (u.machine.config, r.tell.steps, u.fuel)) := by
  induction fuel generalizing code s t with
  | zero => cases code <;> simp [runCode, h]
  | succ fuel ih =>
    cases code with
    | nil => simp [h]
    | cons q rest =>
      obtain ⟨hc, hcode, htime⟩ := step_config_time h q rest
      have hr := ih (step q rest s).code (step q rest s).machine (step q rest t).machine hc
      rw [hcode] at hr
      cases hs : runCode fuel (step q rest s).code (step q rest s).machine <;>
        cases ht : runCode fuel (step q rest t).code (step q rest t).machine <;>
        simp_all [runCode]

/-- Reuse a successful run on the same configuration with arbitrary accounting metadata. -/
theorem execute_of_config_eq (fuel : ℕ) (p : Prog (TMQuery tm) Unit) {s t : TMState tm}
    (h : s.config = t.config) {result : AddWriter TMCost Unit} {final : ExecutionState tm}
    (hr : execute fuel p s = some (result, final)) :
    ∃ result' final', execute fuel p t = some (result', final') ∧
      final'.machine.config = final.machine.config ∧ result'.tell.steps = result.tell.steps ∧
      final'.fuel = final.fuel := by
  have heq := runCode_config_time fuel (instructions p) s t h
  simp only [← execute_eq_runCode, hr, Option.map_some] at heq
  cases ht : execute fuel p t with
  | none => simp [ht] at heq
  | some pair =>
    obtain ⟨result', final'⟩ := pair
    exact ⟨result', final', rfl, by simpa [ht] using heq.symm⟩

/-- A successful run can use exactly its consumed fuel, without changing its result or cost. -/
theorem runCode_trim_fuel (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    final.fuel ≤ fuel ∧
      runCode (fuel - final.fuel) code s = some (result, ⟨final.machine, 0⟩) := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind [runCode]
    | cons q rest =>
      cases hr : runCodeWith step fuel (step q rest s).code (step q rest s).machine with
      | none => simp [runCode, hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        obtain ⟨hle, htrim⟩ := ih _ _ _ _ (by simpa only [runCode] using hr)
        simp only [runCode] at htrim
        simp only [runCode, runCodeWith, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by lia, ?_⟩
        have hsub : fuel + 1 - u.fuel = (fuel - u.fuel) + 1 := by lia
        simp [hsub, runCode, htrim]

/-- Extract an exact-budget completion from an arbitrary successful interpreter run. -/
theorem completes_of_execute {p : Prog (TMQuery tm) Unit} {fuel : ℕ} {s : TMState tm}
    {result : AddWriter TMCost Unit} {final : ExecutionState tm}
    (h : execute fuel p s = some (result, final)) :
    Completes p s result.tell final.machine := by
  rw [execute_eq_runCode] at h
  have ht := (runCode_trim_fuel fuel _ s result final h).2
  refine ⟨fuel - final.fuel, ?_⟩
  simpa [execute_eq_runCode, AddWriter.ext_iff] using ht

end Algolean.Algorithms.TMQuery
