/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM

/-!
# Composition of single-tape query programs

`TMQuery.Completes` records a complete execution with its exact cost and final state.
Sequential composition shares the tape, control state, head position, and visited-cell history.
Fuel witnesses add, as do costs; space is never reset between procedures.
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

/-- Write at the current head, preserving all execution metadata. -/
@[simps config headPos cellsVisited]
def TMState.write {tm : SingleTapeTM Symbol} (s : TMState tm)
    (symbol : Option Symbol) : TMState tm :=
  {s with config.BiTape := s.config.BiTape.write symbol}

/-- Move the head and retain the complete visited-cell history. -/
@[simps config headPos cellsVisited]
def TMState.move {tm : SingleTapeTM Symbol} (s : TMState tm) (dir : Dir) : TMState tm where
  config := {s.config with BiTape := match dir with
    | .Left => s.config.BiTape.moveLeft
    | .Right => s.config.BiTape.moveRight
    | .Stop => s.config.BiTape}
  headPos := s.headPos + dir.offset
  cellsVisited := insert (s.headPos + dir.offset) s.cellsVisited

/-- Exact cost of a move from a state with an existing visited-cell history. -/
def TMState.moveCost {tm : SingleTapeTM Symbol} (s : TMState tm) (dir : Dir) : TMCost :=
  ⟨1, if s.headPos + dir.offset ∈ s.cellsVisited then 0 else 1⟩

namespace TMQuery

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A completed execution, using exactly its witnessed interpreter budget. -/
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

/-- A primitive move has the exact state-dependent space cost. -/
theorem completes_move (s : TMState tm) (dir : Dir) :
    Completes (FreeM.lift (.move dir)) s (s.moveCost dir) (s.move dir) := by
  refine ⟨1, ?_⟩
  cases dir <;> simp [execute_eq_runCode, runCode, step, TMState.move, TMState.moveCost,
    sub_eq_add_neg] <;> split <;> simp_all

/-- Each step visits at most one new cell per head move. -/
theorem step_cellsVisited_le_steps (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (s : TMState tm) : (step q rest s).cost.cellsVisited ≤ (step q rest s).cost.steps := by
  cases q with
  | move dir => cases dir <;> grind [step]
  | _ => simp [step]

/-- New visited cells are bounded by head moves for every completed procedure. -/
theorem runCode_cellsVisited_le_steps (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : Algolean.AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    result.tell.cellsVisited ≤ result.tell.steps := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q code =>
      cases hr : runCode fuel (step q code s).code (step q code s).machine <;> simp_all [runCode]
      have := step_cellsVisited_le_steps q code s
      grind

/-- Every exact completion supplies a time bound on its newly visited cells. -/
theorem Completes.space_le_time {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) : cost.cellsVisited ≤ cost.steps := by
  obtain ⟨fuel, h⟩ := h
  rw [execute_eq_runCode] at h
  exact runCode_cellsVisited_le_steps fuel _ _ _ _ h

/-- Total space includes the initial visited set, even under sequential composition. -/
theorem Completes.space_eq {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) : t.cellsVisited.card = s.cellsVisited.card + cost.cellsVisited := by
  obtain ⟨fuel, h⟩ := h
  simpa using (execute_cellsVisited fuel p s _ _ h).symm

/-- A complete procedure with an exact tape, head position, and time, preserving control state. -/
def Runs (program : Prog (TMQuery tm) Unit) (s : TMState tm)
    (outputTape : BiTape Symbol) (pos : ℤ) (time : ℕ) : Prop :=
  ∃ cost final, Completes program s cost final ∧
    final.config = {s.config with BiTape := outputTape} ∧ final.headPos = pos ∧ cost.steps = time

/-- Any routine contract bounds additional space by its head moves. -/
theorem Runs.space {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {outputTape : BiTape Symbol} {pos : ℤ} {time : ℕ} (h : Runs p s outputTape pos time) :
    ∃ cost final, Completes p s cost final ∧ cost.steps = time ∧ cost.cellsVisited ≤ time ∧
      final.cellsVisited.card ≤ s.cellsVisited.card + time := by
  obtain ⟨cost, final, hc, _, _, ht⟩ := h
  have := hc.space_le_time
  have := hc.space_eq
  exact ⟨cost, final, hc, ht, by lia, by lia⟩


end TMQuery

end Algolean.Algorithms
