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

To describe a completed computation using exactly the fuel it consumed, we apply the shared
`FuelExecMonad.execute_trim_fuel` theorem to remove any unused fuel.

## Main results

* `TMQuery.execute_config_time` shows that head coordinates and cell histories do not affect
  the final configuration or the number of head moves.
* `TMQuery.execute_of_config_eq` reuses a successful run with different head coordinates or
  cell histories.
* `TMQuery.completes_of_execute` proves that a successful run can finish with no fuel left.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

theorem step_config_time {s t : TMState tm} (h : s.config = t.config)
    (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β) :
    (step q next s).machine.config = (step q next t).machine.config ∧
      (step q next s).program = (step q next t).program ∧
      (step q next s).cost.steps = (step q next t).cost.steps := by
  cases q with
  | move direction => cases direction <;> simp [step, h]
  | _ => simp [step, h]

/-- Changing the recorded head coordinate or cell histories does not change the computation. -/
theorem execute_config_time (fuel : ℕ) (p : Prog (TMQuery tm) α)
    (s t : TMState tm) (h : s.config = t.config) :
    (execute fuel p s).map (fun (r, u) => (u.machine.config, r.tell.steps, u.fuel)) =
      (execute fuel p t).map (fun (r, u) => (u.machine.config, r.tell.steps, u.fuel)) := by
  induction fuel generalizing p s t with
  | zero =>
    cases p with
    | pure a => simp [h]
    | liftBind q next => simp only [FuelExecMonad.execute_zero_liftBind]
  | succ fuel ih =>
    cases p with
    | pure a => simp [h]
    | liftBind q next =>
      simp only [FuelExecMonad.execute_liftBind_succ]
      obtain ⟨hc, hp, htime⟩ := step_config_time h q next
      have hr := ih (step q next s).program (step q next s).machine (step q next t).machine hc
      rw [hp] at hr
      cases hs : execute fuel (step q next s).program (step q next s).machine <;>
        cases ht : execute fuel (step q next t).program (step q next t).machine <;>
        simp_all
      grind

/-- Reuse a successful run with the same configuration but different head coordinates or
cell histories. The final configuration, number of head moves, and remaining fuel stay the same. -/
theorem execute_of_config_eq (fuel : ℕ) (p : Prog (TMQuery tm) Unit) {s t : TMState tm}
    (h : s.config = t.config) {result : AddWriter TMCost Unit} {final : ExecutionState tm}
    (hr : execute fuel p s = some (result, final)) :
    ∃ result' final', execute fuel p t = some (result', final') ∧
      final'.machine.config = final.machine.config ∧ result'.tell.steps = result.tell.steps ∧
      final'.fuel = final.fuel := by
  have heq := execute_config_time fuel p s t h
  simp only [hr, Option.map_some] at heq
  cases ht : execute fuel p t with
  | none => simp [ht] at heq
  | some pair =>
    obtain ⟨result', final'⟩ := pair
    exact ⟨result', final', rfl, by simpa [ht] using heq.symm⟩

/-- A successful run can finish with no fuel left by starting with exactly the fuel it consumes. -/
theorem completes_of_execute {p : Prog (TMQuery tm) Unit} {fuel : ℕ} {s : TMState tm}
    {result : AddWriter TMCost Unit} {final : ExecutionState tm}
    (h : execute fuel p s = some (result, final)) :
    Completes p s result.tell final.machine := by
  have ht := (FuelExecMonad.execute_trim_fuel fuel p s result final h).2
  refine ⟨fuel - final.fuel, ?_⟩
  simpa [AddWriter.ext_iff] using ht

end Algolean.Algorithms.TMQuery
