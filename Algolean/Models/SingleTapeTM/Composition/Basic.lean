/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM

/-!
# Composition of single-tape query programs

`TMQuery.Completes` records that a program finishes with the stated cost and final state.
When two procedures run in sequence, the fuel required for execution is the sum of the fuel
required by each procedure. Their costs add up too. The second procedure starts with the tape,
control state, head position, tape range, and head visits left by the first procedure.

## Main definitions and results

* `TMState.write`, `TMState.move`, and `TMState.moveCost` describe primitive state changes.
* `TMQuery.Completes` records exact completion; `TMQuery.Completes.unique` proves determinism.
* `TMQuery.Runs` specifies the output tape, head position, and exact number of head moves.
* `TMQuery.Completes.space_eq` and `TMQuery.Runs.space` relate storage to execution costs.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Displacement of one tape-head movement. -/
@[simp] def Dir.offset : Dir → ℤ
  | .Left => -1
  | .Right => 1
  | .Stop => 0

/-- Write at the current head without changing the control state, head position,
or cell histories. -/
@[simps config headPos cellsAllocated cellsVisited]
def TMState.write {tm : SingleTapeTM Symbol} (s : TMState tm)
    (symbol : Option Symbol) : TMState tm :=
  {s with config.BiTape := s.config.BiTape.write symbol}

/-- Move the head, extending the tape range and retaining all head visits. -/
@[simps config headPos cellsAllocated cellsVisited]
def TMState.move {tm : SingleTapeTM Symbol} (s : TMState tm) (dir : Dir) : TMState tm where
  config := {s.config with BiTape := match dir with
    | .Left => s.config.BiTape.moveLeft
    | .Right => s.config.BiTape.moveRight
    | .Stop => s.config.BiTape}
  headPos := s.headPos + dir.offset
  cellsAllocated := insert (s.headPos + dir.offset) s.cellsAllocated
  cellsVisited := insert (s.headPos + dir.offset) s.cellsVisited

/-- A move extends the tape range only when its destination lies outside it. -/
def TMState.moveCost {tm : SingleTapeTM Symbol} (s : TMState tm) (dir : Dir) : TMCost :=
  ⟨1, if s.headPos + dir.offset ∈ s.cellsAllocated then 0 else 1⟩

namespace TMQuery

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- The program finishes with the stated cost and final state, using all the supplied fuel. -/
def Completes (program : Prog (TMQuery tm) Unit) (s : TMState tm)
    (cost : TMCost) (final : TMState tm) : Prop :=
  ∃ fuel, execute fuel program s = some (⟨(), cost⟩, ⟨final, 0⟩)

/-- The empty procedure is the identity for execution and resource costs. -/
@[simp] theorem completes_pure (s : TMState tm) : Completes (pure ()) s 0 s := ⟨0, rfl⟩

/-- A completed run fixes both the physical final state and the cost, independently of fuel. -/
theorem Completes.unique {p : Prog (TMQuery tm) Unit} {s t u : TMState tm} {a b : TMCost}
    (hp : Completes p s a t) (hq : Completes p s b u) : a = b ∧ t = u := by
  obtain ⟨fuel, hp⟩ := hp
  obtain ⟨extra, hq⟩ := hq
  have h₁ := execute_add_fuel fuel extra p s _ _ hp
  have h₂ := execute_add_fuel extra fuel p s _ _ hq
  grind [Nat.add_comm]

/-- Writing changes only the head symbol and costs no head moves or space. -/
theorem completes_write (s : TMState tm) (symbol : Option Symbol) :
    Completes (FreeM.lift (.write symbol)) s 0 (s.write symbol) := by
  refine ⟨1, ?_⟩
  simp [execute_eq_runCode, runCode, step, TMState.write]

/-- Changing the control label leaves the tape and cell histories unchanged and has zero cost. -/
theorem completes_update (s : TMState tm) (label : tm.State) :
    Completes (FreeM.lift (.update label)) s 0 {s with config.state := some label} := by
  exact ⟨1, by simp [execute_eq_runCode, runCode, step]⟩

/-- A primitive move has the exact state-dependent space cost. -/
theorem completes_move (s : TMState tm) (dir : Dir) :
    Completes (FreeM.lift (.move dir)) s (s.moveCost dir) (s.move dir) := by
  refine ⟨1, ?_⟩
  cases dir <;> simp [execute_eq_runCode, runCode, step, TMState.move, TMState.moveCost,
    sub_eq_add_neg] <;> split <;> simp_all

/-- Each head move extends the tape range by at most one cell. -/
theorem step_cellsAllocated_le_steps (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (s : TMState tm) : (step q rest s).cost.cellsAllocated ≤ (step q rest s).cost.steps := by
  cases q with
  | move dir => cases dir <;> grind [step]
  | _ => simp [step]

/-- Additional cells in the tape range are bounded by head moves for every completed procedure. -/
theorem runCode_cellsAllocated_le_steps (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : Algolean.AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    result.tell.cellsAllocated ≤ result.tell.steps := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q code =>
      cases hr : runCode fuel (step q code s).code (step q code s).machine <;> simp_all [runCode]
      have := step_cellsAllocated_le_steps q code s
      grind

/-- Every exact completion bounds additional storage by its head moves. -/
theorem Completes.space_le_time {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) : cost.cellsAllocated ≤ cost.steps := by
  obtain ⟨fuel, h⟩ := h
  rw [execute_eq_runCode] at h
  exact runCode_cellsAllocated_le_steps fuel _ _ _ _ h

/-- Total space includes the initial tape range, even under sequential composition. -/
theorem Completes.space_eq {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) :
    t.cellsAllocated.card = s.cellsAllocated.card + cost.cellsAllocated := by
  obtain ⟨fuel, h⟩ := h
  simpa using (execute_cellsAllocated fuel p s _ _ h).symm

/-- A complete procedure with an exact tape, head position, and time, preserving control state. -/
def Runs (program : Prog (TMQuery tm) Unit) (s : TMState tm)
    (outputTape : BiTape Symbol) (pos : ℤ) (time : ℕ) : Prop :=
  ∃ cost final, Completes program s cost final ∧
    final.config = {s.config with BiTape := outputTape} ∧ final.headPos = pos ∧ cost.steps = time

/-- Any routine contract bounds additional space by its head moves. -/
theorem Runs.space {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {outputTape : BiTape Symbol} {pos : ℤ} {time : ℕ} (h : Runs p s outputTape pos time) :
    ∃ cost final, Completes p s cost final ∧ cost.steps = time ∧ cost.cellsAllocated ≤ time ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + time := by
  obtain ⟨cost, final, hc, _, _, ht⟩ := h
  have := hc.space_le_time
  have := hc.space_eq
  exact ⟨cost, final, hc, ht, by lia, by lia⟩


end TMQuery

end Algolean.Algorithms
