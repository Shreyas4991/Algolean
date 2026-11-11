/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Basic
public import Algolean.Models.SingleTapeTM.Composition.While
public import Algolean.Models.SingleTapeTM.Tape

/-!
# Moving across a known gap between occupied cells

* `seekLeftOccupied` moves left across blanks and stops at the first occupied cell.
* `seekRightOccupied` does the same to the right.
* The correctness theorems require an occupied cell in the chosen direction and give the exact
  number of head moves. They preserve every tape cell and the control state.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This moves left while the current cell is blank. An occupied cell must exist to its left.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekLeftOccupied (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (tape =ₜ none) do
    moveₜ .Left

/--
This moves right while the current cell is blank. An occupied cell must exist to its right.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekRightOccupied (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (tape =ₜ none) do
    moveₜ .Right

/-- Crossing `gap + 1` blank cells to the left preserves the tape and stops on the next symbol. -/
theorem seekLeftOccupied_correct (gap : Nat) (symbol : Symbol) (left right : StackTape Symbol)
    (s : TMState tm)
    (htape : s.config.BiTape =
      ⟨none, StackTape.blanks gap (StackTape.cons (some symbol) left), right⟩) :
    Runs (seekLeftOccupied tm) s
      ⟨some symbol, left, StackTape.blanks (gap + 1) right⟩
      (s.headPos - (gap + 1 : Nat)) (gap + 1) := by
  induction gap generalizing right s with
  | zero =>
    unfold seekLeftOccupied
    apply runs_while_step (by simp [htape])
    have hm := move_correct s .Left
    have ht : (s.move .Left).config.BiTape =
        ⟨some symbol, left, StackTape.cons none right⟩ := by
      simp [TMState.move, htape, BiTape.moveLeft]
    have hb : Runs (FreeM.lift (.move .Left)) s
        ⟨some symbol, left, StackTape.cons none right⟩ (s.headPos - 1) 1 := by
      simpa only [ht, Dir.offset, sub_eq_add_neg] using hm
    have hr := hb.seq (q := seekLeftOccupied tm)
      (second := ⟨some symbol, left, StackTape.cons none right⟩)
      (pos₂ := s.headPos - 1) (time₂ := 0) (by
      intro middle hmiddle hpos
      simp [seekLeftOccupied, hmiddle, hpos])
    simpa [seekLeftOccupied] using hr
  | succ gap ih =>
    unfold seekLeftOccupied
    apply runs_while_step (by simp [htape])
    have hm : Runs (FreeM.lift (.move .Left)) s
        ⟨none, StackTape.blanks gap (StackTape.cons (some symbol) left),
          StackTape.cons none right⟩ (s.headPos - 1) 1 := by
      simpa [htape, BiTape.moveLeft, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := seekLeftOccupied tm) (by
      intro middle hmiddle hpos
      simpa [hpos, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        ih (StackTape.cons none right) middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
    convert hr using 1 <;> simp [seekLeftOccupied, sub_eq_add_neg,
      add_comm, add_left_comm]

/-- Crossing `gap + 1` blank cells to the right preserves the tape and stops on the next symbol. -/
theorem seekRightOccupied_correct (gap : Nat) (symbol : Symbol) (left right : StackTape Symbol)
    (s : TMState tm)
    (htape : s.config.BiTape =
      ⟨none, left, StackTape.blanks gap (StackTape.cons (some symbol) right)⟩) :
    Runs (seekRightOccupied tm) s
      ⟨some symbol, StackTape.blanks (gap + 1) left, right⟩
      (s.headPos + (gap + 1 : Nat)) (gap + 1) := by
  induction gap generalizing left s with
  | zero =>
    unfold seekRightOccupied
    apply runs_while_step (by simp [htape])
    have hm : Runs (FreeM.lift (.move .Right)) s
        ⟨some symbol, StackTape.cons none left, right⟩ (s.headPos + 1) 1 := by
      simpa [htape, BiTape.moveRight] using move_correct s .Right
    have hr := hm.seq (q := seekRightOccupied tm)
      (second := ⟨some symbol, StackTape.cons none left, right⟩)
      (pos₂ := s.headPos + 1) (time₂ := 0) (by
      intro middle hmiddle hpos
      simp [seekRightOccupied, hmiddle, hpos])
    simpa [seekRightOccupied] using hr
  | succ gap ih =>
    unfold seekRightOccupied
    apply runs_while_step (by simp [htape])
    have hm : Runs (FreeM.lift (.move .Right)) s
        ⟨none, StackTape.cons none left,
          StackTape.blanks gap (StackTape.cons (some symbol) right)⟩
        (s.headPos + 1) 1 := by
      simpa [htape, BiTape.moveRight] using move_correct s .Right
    have hr := hm.seq (q := seekRightOccupied tm) (by
      intro middle hmiddle hpos
      simpa [hpos, add_assoc, add_comm, add_left_comm] using
        ih (StackTape.cons none left) middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
    convert hr using 1 <;> simp [seekRightOccupied, add_comm, add_left_comm]

/-- The rightward scan also handles a gap of length zero, when the head is already on a symbol. -/
theorem seekRightOccupied_stack (gap : Nat) (symbol : Symbol) (left right : StackTape Symbol)
    (s : TMState tm)
    (htape : s.config.BiTape =
      let stack := StackTape.blanks gap (StackTape.cons (some symbol) right)
      ⟨stack.head, left, stack.tail⟩) :
    Runs (seekRightOccupied tm) s
      ⟨some symbol, StackTape.blanks gap left, right⟩
      (s.headPos + gap) gap := by
  cases gap with
  | zero => simp [seekRightOccupied, htape]
  | succ gap =>
    exact seekRightOccupied_correct gap symbol left right s (by simpa using htape)

end Algolean.Algorithms.SingleTapeTuringMachines
