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

/-- A scan for an occupied cell stops immediately when the current cell is occupied. -/
private theorem occupied_spec (direction : Dir) (loop : Prog (TMQuery tm) Unit)
    (hloop : loop = whileLoop (.tapeIs none) (do [TMQuery tm] moveₜ direction))
    (symbol : Symbol) (left right : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, ⟨some symbol, left, right⟩⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      loop
    ⦃ fun _ cost final => final.config = ⟨label, ⟨some symbol, left, right⟩⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  subst loop
  vcgen [Spec.while_false_spec]
  simp_all

/-- Moving left across the displayed blanks preserves the tape and counts every move. -/
@[spec] theorem seekLeftOccupied_spec (gap : Nat) (symbol : Symbol)
    (left right : StackTape Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ⟨none, StackTape.blanks gap (StackTape.cons (some symbol) left), right⟩⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekLeftOccupied tm
    ⦃ fun _ cost final => final.config =
        ⟨label, ⟨some symbol, left, StackTape.blanks (gap + 1) right⟩⟩ ∧
        final.headPos = origin - (gap + 1 : Nat) ∧ cost.steps = elapsed + gap + 1 ⦄ := by
  induction gap generalizing right origin elapsed with
  | zero =>
    unfold seekLeftOccupied
    vcgen [Spec.while_step_spec (loop := seekLeftOccupied tm) (hloop := rfl),
      occupied_spec .Left (seekLeftOccupied tm) rfl symbol left (StackTape.cons none right)
        label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveLeft, sub_eq_add_neg]
  | succ gap ih =>
    unfold seekLeftOccupied
    vcgen [Spec.while_step_spec (loop := seekLeftOccupied tm) (hloop := rfl),
      ih (StackTape.cons none right) (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveLeft,
      sub_eq_add_neg, add_assoc]
    all_goals lia

/-- Crossing `gap + 1` blank cells to the left preserves the tape and stops on the next symbol. -/
theorem seekLeftOccupied_correct (gap : Nat) (symbol : Symbol) (left right : StackTape Symbol)
    (s : TMState tm)
    (htape : s.config.BiTape =
      ⟨none, StackTape.blanks gap (StackTape.cons (some symbol) left), right⟩) :
    Runs (seekLeftOccupied tm) s
      ⟨some symbol, left, StackTape.blanks (gap + 1) right⟩
      (s.headPos - (gap + 1 : Nat)) (gap + 1) := by
  apply Spec.runs
  vcgen [seekLeftOccupied_spec gap symbol left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/-- Moving right across the displayed blanks preserves the tape and counts every move. -/
@[spec] theorem seekRightOccupied_spec (gap : Nat) (symbol : Symbol)
    (left right : StackTape Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ⟨none, left, StackTape.blanks gap (StackTape.cons (some symbol) right)⟩⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekRightOccupied tm
    ⦃ fun _ cost final => final.config =
        ⟨label, ⟨some symbol, StackTape.blanks (gap + 1) left, right⟩⟩ ∧
        final.headPos = origin + (gap + 1 : Nat) ∧ cost.steps = elapsed + gap + 1 ⦄ := by
  induction gap generalizing left origin elapsed with
  | zero =>
    unfold seekRightOccupied
    vcgen [Spec.while_step_spec (loop := seekRightOccupied tm) (hloop := rfl),
      occupied_spec .Right (seekRightOccupied tm) rfl symbol (StackTape.cons none left) right
        label (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveRight]
  | succ gap ih =>
    unfold seekRightOccupied
    vcgen [Spec.while_step_spec (loop := seekRightOccupied tm) (hloop := rfl),
      ih (StackTape.cons none left) (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, BiTape.moveRight, add_assoc]
    all_goals lia

/-- Crossing `gap + 1` blank cells to the right preserves the tape and stops on the next symbol. -/
theorem seekRightOccupied_correct (gap : Nat) (symbol : Symbol) (left right : StackTape Symbol)
    (s : TMState tm)
    (htape : s.config.BiTape =
      ⟨none, left, StackTape.blanks gap (StackTape.cons (some symbol) right)⟩) :
    Runs (seekRightOccupied tm) s
      ⟨some symbol, StackTape.blanks (gap + 1) left, right⟩
      (s.headPos + (gap + 1 : Nat)) (gap + 1) := by
  apply Spec.runs
  vcgen [seekRightOccupied_spec gap symbol left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

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
