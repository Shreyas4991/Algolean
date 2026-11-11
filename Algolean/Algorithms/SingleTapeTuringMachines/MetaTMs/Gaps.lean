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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

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
    have hc : Completes (seekLeftOccupied tm) (s.move .Left) 0 (s.move .Left) :=
      completes_while_false _ _ _ (by simp [TMState.move, htape, BiTape.moveLeft])
    unfold seekLeftOccupied
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekLeftOccupied tm) (hloop := rfl), Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveLeft, sub_eq_add_neg]
  | succ gap ih =>
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih (StackTape.cons none right) (s.move .Left)
      (by simp [TMState.move, htape, BiTape.moveLeft])
    unfold seekLeftOccupied
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekLeftOccupied tm) (hloop := rfl), Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, sub_eq_add_neg,
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
    have hc : Completes (seekRightOccupied tm) (s.move .Right) 0 (s.move .Right) :=
      completes_while_false _ _ _ (by simp [TMState.move, htape, BiTape.moveRight])
    unfold seekRightOccupied
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekRightOccupied tm) (hloop := rfl), Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveRight]
  | succ gap ih =>
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih (StackTape.cons none left) (s.move .Right)
      (by simp [TMState.move, htape, BiTape.moveRight])
    unfold seekRightOccupied
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekRightOccupied tm) (hloop := rfl), Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, add_comm, add_left_comm]

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
