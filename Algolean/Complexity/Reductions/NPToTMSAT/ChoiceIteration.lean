/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FollowingSelections
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Visiting all five choices on the reduction's tape

* `forFiveChoices` visits every time, first position, first state, second position, and second
  state in that order. All five indices are read from unary words on the tape.
* `afterFirstTime` runs these loops just after a temporarily erased first time cell. It returns
  to that erased cell after the loops finish.
* `LeafSpec` describes the fixed action at a selected combination. The functions describing
  the output occur only in this specification, and do not select different programs.
* The program restores all five source words and the head. Its time is polynomial when
  one polynomial bounds the fixed action for every selected combination.

These are machine templates. The containing machine fixes the alphabet symbols and action
once, independently of the unary bounds and all selected indices.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToTMSAT.ChoiceIteration

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- These are the five unary bounds, the preserved input, and output on the tape. -/
@[expose] def layout (tick : Γ) (times positions states : Nat) (input output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (List.replicate times tick)
    (StackTape.separateWords [List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input] (StackTape.mapSome output))

/-- This template visits the four following choices while preserving the selected time. -/
def forRemainingChoices (tm : SingleTapeTM Γ) (tick : Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  forFollowingSelections tm tick action 4

/-- This fixed template visits the five unary choices in their displayed order. -/
def forFiveChoices (tm : SingleTapeTM Γ) (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  forBlocks tm tick [] (forFollowingSelections tm tick action 4)

/-- This gives the ordered output of the fixed action over all five choices. -/
@[expose] def word (piece : Nat → Nat → Nat → Nat → Nat → List Γ)
    (times positions states : Nat) : List Γ :=
  (List.range times).flatMap fun time =>
    (List.range positions).flatMap fun position =>
      (List.range states).flatMap fun control =>
        (List.range positions).flatMap fun otherPosition =>
          (List.range states).flatMap fun otherControl =>
            piece time position control otherPosition otherControl

/--
The action appends one specified word at each selected combination, preserves the selected
cells and all other data, and returns to the selected cell of the fifth unary word.
-/
@[expose] def LeafSpec (tick : Γ) (times positions states : Nat) (input : List Γ)
    (piece : Nat → Nat → Nat → Nat → Nat → List Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (size bound : Nat) : Prop :=
  ∀ time timeRest position positionRest control controlRest otherPosition otherPositionRest
    otherControl otherControlRest,
    time + timeRest + 1 = times → position + positionRest + 1 = positions →
    control + controlRest + 1 = states → otherPosition + otherPositionRest + 1 = positions →
    otherControl + otherControlRest + 1 = states → ∀ output,
    times + 2 * positions + 2 * states + input.length +
      (output ++ piece time position control otherPosition otherControl).length + 32 ≤ size →
    ∀ (origin : ℤ) (elapsed : Nat),
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape [List.replicate otherPositionRest tick,
          List.replicate otherPosition tick, List.replicate controlRest tick,
            List.replicate control tick, List.replicate positionRest tick,
              List.replicate position tick, List.replicate timeRest tick,
                List.replicate time tick] (List.replicate otherControl tick) [List.replicate
                  otherControlRest tick, input] (output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      action
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape [List.replicate otherPositionRest tick,
          List.replicate otherPosition tick, List.replicate controlRest tick,
            List.replicate control tick, List.replicate positionRest tick,
              List.replicate position tick, List.replicate timeRest tick,
                List.replicate time tick] (List.replicate otherControl tick) [List.replicate
                  otherControlRest tick,
                    input] (output ++ piece time position control otherPosition otherControl)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄

/-- This bounds one nested loop by its number of choices and its action's bound. -/
@[expose] def nestedMoves (size bound depth : Nat) : Nat :=
  selectionMoves size bound depth

/-- This bounds all five loops, including the return to the first time cell. -/
@[expose] def iterationMoves (size bound : Nat) : Nat :=
  size * (nestedMoves size bound 4 + 2) + 2

/-- This applies the same loop overhead to a polynomial bound for its fixed action. -/
@[expose] noncomputable def nestedPolynomial (bound : Polynomial Nat) : Nat → Polynomial Nat
  | 0 => bound
  | depth + 1 => Polynomial.X * (nestedPolynomial bound depth + 2) + 2 * Polynomial.X + 8

/-- Evaluating the polynomial gives the numeric bound for the corresponding nested loops. -/
@[simp] theorem eval_nestedPolynomial (bound : Polynomial Nat) (depth size : Nat) :
    (nestedPolynomial bound depth).eval size = nestedMoves size (bound.eval size) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp [nestedPolynomial, nestedMoves, selectionMoves, ih]

/-- This polynomial includes all five loops and the return to the first time cell. -/
@[expose] noncomputable def iterationPolynomial (bound : Polynomial Nat) : Polynomial Nat :=
  Polynomial.X * (nestedPolynomial bound 4 + 2) + 2

/-- Evaluating this polynomial gives the complete five-loop move bound. -/
@[simp] theorem eval_iterationPolynomial (bound : Polynomial Nat) (size : Nat) :
    (iterationPolynomial bound).eval size = iterationMoves size (bound.eval size) := by
  simp [iterationPolynomial, iterationMoves]

/-- This is the ordered output over the four head choices at one selected time. -/
@[expose] def rowWord (piece : Nat → Nat → Nat → Nat → Nat → List Γ)
    (time positions states : Nat) : List Γ :=
  (List.range positions).flatMap fun position =>
    (List.range states).flatMap fun control =>
      (List.range positions).flatMap fun otherPosition =>
        (List.range states).flatMap fun otherControl =>
          piece time position control otherPosition otherControl

private theorem descend1_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (times positions states : Nat) (input output : List Γ)
    (piece : Nat → Nat → Nat → Nat → Nat → List Γ) (label : Option tm.State) (size bound : Nat)
    (hleaf : LeafSpec tick times positions states input piece label action size bound)
    (time timeRest : Nat)
    (hTime : time + timeRest + 1 = times)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ rowWord piece time positions states).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick) [List.replicate timeRest tick,
          List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input] (output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forFollowingSelections tm tick action 4
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick) [List.replicate timeRest tick,
          List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick,
              input] (output ++ rowWord piece time positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + nestedMoves size bound 4 ⦄ := by
  let next : List Nat → List Γ
    | [position, control, otherPosition, otherControl] =>
      piece time position control otherPosition otherControl
    | _ => []
  have hs := forFollowingSelections_spec (tm := tm) tick action [] (time, timeRest)
    [positions, states, positions, states] input output next label
    (times + 2 * positions + 2 * states + input.length + 32) size bound
    (by lia) (by
      intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> lia) (by
      intro selected hselected written hbound positionHead steps
      obtain ⟨position, tail, hp, h₁, rfl⟩ := List.forall₂_cons_right_iff.mp hselected
      obtain ⟨control, tail, hc, h₂, rfl⟩ := List.forall₂_cons_right_iff.mp h₁
      obtain ⟨otherPosition, tail, hop, h₃, rfl⟩ := List.forall₂_cons_right_iff.mp h₂
      obtain ⟨otherControl, tail, hoc, h₄, rfl⟩ := List.forall₂_cons_right_iff.mp h₃
      obtain rfl := List.forall₂_nil_right_iff.mp h₄
      simpa [selectedTape, selectionTape, next, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hleaf time timeRest position.1 position.2 control.1 control.2
          otherPosition.1 otherPosition.2 otherControl.1 otherControl.2 hTime hp hc hop hoc
          written (by simpa [next, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound)
          positionHead steps)
    (by simpa [selectionWord, next, rowWord, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hsize) origin elapsed
  simpa [selectionTape, selectionWord, next, rowWord, nestedMoves, selectionMoves]
    using hs

/--
The four following choices are visited in order. The selected time and every source word are
preserved, and the head returns to the selected time cell.
-/
@[spec] theorem forRemainingChoices_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (times positions states : Nat) (input output : List Γ)
    (piece : Nat → Nat → Nat → Nat → Nat → List Γ) (label : Option tm.State) (size bound : Nat)
    (hleaf : LeafSpec tick times positions states input piece label action size bound)
    (time timeRest : Nat) (htime : time + timeRest + 1 = times)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ rowWord piece time positions states).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick)
          [List.replicate timeRest tick, List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input] output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forRemainingChoices tm tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick)
          [List.replicate timeRest tick, List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input]
          (output ++ rowWord piece time positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + nestedMoves size bound 4 ⦄ := by
  vcgen [forRemainingChoices, descend1_spec tick action times positions states input output
    piece label size bound hleaf time timeRest htime hsize origin elapsed]

/--
Every source word and the starting head position are restored. The output is the concatenation
of the fixed action's words in increasing order of all five indices.
-/
@[spec] theorem forFiveChoices_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (times positions states : Nat) (input output : List Γ)
    (piece : Nat → Nat → Nat → Nat → Nat → List Γ) (label : Option tm.State) (size bound : Nat)
    (hleaf : LeafSpec tick times positions states input piece label action size bound)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ word piece times positions states).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        layout tick times positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forFiveChoices tm tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        layout tick times positions states input (output ++ word piece times positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + iterationMoves size bound ⦄ := by
  let next := fun time => rowWord piece time positions states
  let following := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  have ha (index rest : Nat) (hcount : index + rest + 1 = times)
      (positionHead : ℤ) (steps : Nat) := descend1_spec tick action times positions states input
    (output ++ (List.range index).flatMap next) piece label size bound hleaf index rest hcount (by
      have hp := ((List.range_sublist.mpr (show index + 1 ≤ times by lia)).flatMap next).length_le
      have hout : ((output ++ (List.range index).flatMap next) ++ next index).length ≤
          (output ++ word piece times positions states).length := by
        simpa [word, rowWord, next, List.range_succ,
          List.length_append, Nat.add_assoc] using Nat.add_le_add_left hp output.length
      simpa only [next, List.append_assoc] using
        (show times + 2 * positions + 2 * states + input.length +
          ((output ++ (List.range index).flatMap next) ++ next index).length + 32 ≤ size by lia))
    positionHead steps
  have hr := forBlocks_append_spec tick (forFollowingSelections tm tick action 4) times [] following
    output next label (nestedMoves size bound 4) (by
      intro index rest hcount positionHead steps
      simpa [following, List.range_succ, List.append_assoc] using
        ha index rest hcount positionHead steps) origin elapsed
  have htime : times * (nestedMoves size bound 4 + 2) + 2 ≤ iterationMoves size bound := by
    dsimp [iterationMoves]
    gcongr
    lia
  vcgen [forFiveChoices, hr]
  all_goals
    simp_all [layout, counterLeft, following, next, word, rowWord]
    all_goals lia

/-- The five loops multiply their action's bound by a polynomial of degree five. -/
theorem iterationMoves_le (size bound : Nat) :
    iterationMoves size bound ≤ 16 * (size + 1) ^ 5 * (bound + 1) := by
  simp only [iterationMoves, nestedMoves, selectionMoves]
  ring_nf
  lia

/-- This runs the five choice loops immediately after a temporarily erased first time cell. -/
def afterFirstTime (tm : SingleTapeTM Γ) (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  forFiveChoices tm tick action
  moveₜ .Left

/-- The two extra moves preserve the erased first cell and add two to the loop bound. -/
@[spec] theorem afterFirstTime_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (times positions states : Nat) (input output written : List Γ)
    (label : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config =
          ⟨label, layout tick times positions states input output⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        forFiveChoices tm tick action
      ⦃ fun _ cost final => final.config =
          ⟨label, layout tick times positions states input written⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    let parts := [List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input]
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil []
        (StackTape.prepend (List.replicate times tick)
          (StackTape.cons none (StackTape.separateWords parts (StackTape.mapSome output))))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      afterFirstTime tm tick action
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil []
        (StackTape.prepend (List.replicate times tick)
          (StackTape.cons none (StackTape.separateWords parts (StackTape.mapSome written))))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 ⦄ := by
  dsimp only
  vcgen [afterFirstTime, haction (origin + 1) (elapsed + 1)]
  all_goals cases times
  all_goals simp_all [layout, TMState.move, TMState.moveCost,
    List.replicate_succ, BiTape.segment, BiTape.moveLeft, BiTape.moveRight]
  all_goals lia


end Algolean.Algorithms.NPToTMSAT.ChoiceIteration
