/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic

/-!
# Frames for single-tape execution

A frame is the surrounding execution information that a procedure carries along without
using it to decide what to do. Here, this means the recorded head coordinate, tape range,
and history of head visits. A program can inspect tape symbols and the control state,
but it cannot inspect these records. Execution updates the records as the head moves.

This matters when procedures run in sequence. The second procedure inherits the first
procedure's head coordinate and cell histories. We want to reuse its correctness proof
without resetting those records or proving the same computation correct again.

For example, a procedure should perform the same computation when the starting head
coordinate is recorded as 37 instead of 0, provided its tape configuration and control state
are the same. It should also work when an earlier procedure has already visited some of the
cells it will use. The results in this file show that the final configuration, number of head
moves, and fuel consumed stay the same. The additional storage cost may change: a cell already
in the tape range does not need to be counted again.

The file also proves that unused fuel can be removed from a successful run. This lets us
describe the completed computation using exactly the fuel it consumed.

## Main results

* `TMQuery.runCode_config_time` shows that head coordinates and cell histories do not affect
  the final configuration or the number of head moves.
* `TMQuery.execute_of_config_eq` reuses a successful run with different head coordinates or
  cell histories.
* `TMQuery.runCode_trim_fuel` removes unused fuel without changing the result or cost.
* `TMQuery.completes_of_execute` proves that a successful run can finish with no fuel left.
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
      grind

/-- Reuse a successful run with the same configuration but different head coordinates or
cell histories. The final configuration, number of head moves, and remaining fuel stay the same. -/
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
      cases hr : runCode fuel (step q rest s).code (step q rest s).machine with
      | none => simp [runCode, hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        obtain ⟨hle, htrim⟩ := ih _ _ _ _ hr
        simp only [runCode, hr] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by lia, ?_⟩
        have hsub : fuel + 1 - u.fuel = (fuel - u.fuel) + 1 := by lia
        simp [hsub, runCode, htrim]

/-- A successful run can finish with no fuel left by starting with exactly the fuel it consumes. -/
theorem completes_of_execute {p : Prog (TMQuery tm) Unit} {fuel : ℕ} {s : TMState tm}
    {result : AddWriter TMCost Unit} {final : ExecutionState tm}
    (h : execute fuel p s = some (result, final)) :
    Completes p s result.tell final.machine := by
  rw [execute_eq_runCode] at h
  have ht := (runCode_trim_fuel fuel _ s result final h).2
  refine ⟨fuel - final.fuel, ?_⟩
  simpa [execute_eq_runCode, AddWriter.ext_iff] using ht

end Algolean.Algorithms.TMQuery
