/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.ChoiceLayout
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FollowingSelections
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CellMarking

/-!
# Visiting positions at one selected time

* `forSelectedTimePositions` visits every simulated tape position while keeping the same
  simulated time. It sets the other position and both state selections to zero for each visit.
* `PositionSpec` states what the fixed action writes at each visited position.
* `forSelectedTimePositions_spec` proves that the tape words and selected time are restored.
  A quadratic move bound for each action gives a cubic bound for the whole loop.

The bounds are represented by runs of identical symbols; temporarily blanking one cell selects
its position in a run. These templates read the selections and lengths from the tape.
The containing machine fixes the symbols and action independently of its input.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.PositionIteration

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines NPToSAT.Computation.HeadChoices
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def onFollowingFirst (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onFollowingWord tm (markFirst tick action)

private theorem onFollowingFirst_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (left : StackTape Γ) (remaining rest : List Γ) (tail resultTail : StackTape Γ)
    (label : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      let nextLeft := StackTape.cons none
        (StackTape.prepend remaining.reverse (StackTape.cons none left))
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment nextLeft []
          (StackTape.prepend rest (StackTape.cons none tail))⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment nextLeft []
          (StackTape.prepend rest (StackTape.cons none resultTail))⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left []
        (StackTape.prepend remaining (StackTape.cons none
          (StackTape.prepend (tick :: rest) (StackTape.cons none tail))))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onFollowingFirst tick action
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment left []
        (StackTape.prepend remaining (StackTape.cons none
          (StackTape.prepend (tick :: rest) (StackTape.cons none resultTail))))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 * remaining.length + 6 ⦄ := by
  let nextLeft := StackTape.cons none
    (StackTape.prepend remaining.reverse (StackTape.cons none left))
  have hm := markFirst_spec (tm := tm) tick action nextLeft rest tail resultTail label bound
    haction
  have hv := onFollowingWord_spec (tm := tm) (markFirst tick action) left remaining
    (tick :: rest) tail resultTail label label bound (by simpa [nextLeft] using hm) origin elapsed
  vcgen [onFollowingFirst, hv]
  all_goals simp_all

private def atOtherFirstChoices (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onFollowingFirst tick (onFollowingFirst tick (onFollowingFirst tick action))

private theorem atOtherFirstChoices_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (time timeRest position positionRest positions states : Nat)
    (hpositions : 0 < positions) (hstates : 0 < states)
    (input output written : List Γ) (label : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
        (0, states - 1), (0, positions - 1), (0, states - 1)⟩
      ⦃ fun cost current => AtPair tick choice input output label origin current ∧
          cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => AtPair tick choice input written label origin final ∧
          cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        selectionTape tick [(time, timeRest)] (position, positionRest)
          [states, positions, states] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      atOtherFirstChoices tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick [(time, timeRest)] (position, positionRest)
          [states, positions, states] input written⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 * positionRest +
          2 * (states - 1) + 2 * (positions - 1) + 18 ⦄ := by
  obtain ⟨positions, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : positions ≠ 0)
  obtain ⟨states, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : states ≠ 0)
  let left := StackTape.prepend (List.replicate position tick).reverse
    (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])
  let firstLeft := StackTape.cons none
    (StackTape.prepend (List.replicate positionRest tick).reverse (StackTape.cons none left))
  let secondLeft := StackTape.cons none
    (StackTape.prepend (List.replicate states tick).reverse (StackTape.cons none firstLeft))
  let thirdLeft := StackTape.cons none
    (StackTape.prepend (List.replicate positions tick).reverse (StackTape.cons none secondLeft))
  let tail := StackTape.separateWords [input] (StackTape.mapSome output)
  let resultTail := StackTape.separateWords [input] (StackTape.mapSome written)
  let later := StackTape.prepend (tick :: List.replicate states tick) (StackTape.cons none tail)
  let resultLater := StackTape.prepend (tick :: List.replicate states tick)
    (StackTape.cons none resultTail)
  let last := StackTape.prepend (tick :: List.replicate positions tick)
    (StackTape.cons none later)
  let resultLast := StackTape.prepend (tick :: List.replicate positions tick)
    (StackTape.cons none resultLater)
  have hthird (place : ℤ) (steps : Nat) := onFollowingFirst_spec (tm := tm) tick action
    secondLeft (List.replicate positions tick) (List.replicate states tick) tail resultTail
    label bound (by
      simpa [AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
        ActiveChoices.rightWords, thirdLeft, secondLeft, firstLeft, left, tail, resultTail,
        counterLeft, StackTape.separateWords, and_assoc] using haction) place steps
  have hsecond (place : ℤ) (steps : Nat) := onFollowingFirst_spec (tm := tm) tick
    (onFollowingFirst tick action) firstLeft (List.replicate states tick)
    (List.replicate positions tick) later resultLater label (bound + 2 * positions + 6)
    (by simpa [secondLeft, later, resultLater, Nat.add_assoc] using hthird) place steps
  have hfirst := onFollowingFirst_spec (tm := tm) tick
    (onFollowingFirst tick (onFollowingFirst tick action)) left
    (List.replicate positionRest tick) (List.replicate states tick) last resultLast label
    (bound + 2 * positions + 6 + 2 * states + 6)
    (by simpa [firstLeft, last, resultLast, Nat.add_assoc] using hsecond) origin elapsed
  vcgen [atOtherFirstChoices, hfirst]
  all_goals
    simp_all [selectionTape, markedUnaryTape, left, last, resultLast, later, resultLater,
      tail, resultTail, List.replicate_succ, StackTape.separateWords]
    all_goals lia

/--
This states what the fixed action writes at one simulated tape position. The other position
and both state selections are zero. The action preserves the selected time and every tape word.
-/
@[expose] def PositionSpec (tick : Γ) (time timeRest positions states : Nat) (input : List Γ)
    (piece : Nat → List Γ) (label : Option tm.State) (action : Prog (TMQuery tm) Unit)
    (size bound : Nat) : Prop :=
  ∀ position positionRest, position + positionRest + 1 = positions → ∀ output,
    time + timeRest + 2 * positions + 2 * states + input.length +
      (output ++ piece position).length + 32 ≤ size → ∀ (origin : ℤ) (elapsed : Nat),
    let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
      (0, states - 1), (0, positions - 1), (0, states - 1)⟩
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      action
    ⦃ fun _ cost final => AtPair tick choice input (output ++ piece position) label origin final ∧
        cost.steps ≤ elapsed + bound ⦄

/--
This template visits every position while keeping the time and setting the other selections to zero.
-/
def forSelectedTimePositions (tm : SingleTapeTM Γ) (tick : Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  onFollowingWord tm (forBlocks tm tick [] (atOtherFirstChoices tick action))

/-- This bounds the position loop, including the moves that select zero in the other three words. -/
@[expose] def positionIterationMoves (size bound : Nat) : Nat :=
  size * (bound + 6 * size + 20) + 2 * size + 8

/-- Visiting all positions restores the selected time cell and every tape word. -/
@[spec] theorem forSelectedTimePositions_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (time timeRest positions states : Nat) (hpositions : 0 < positions) (hstates : 0 < states)
    (input output : List Γ) (piece : Nat → List Γ) (label : Option tm.State) (size bound : Nat)
    (hleaf : PositionSpec tick time timeRest positions states input piece label action size bound)
    (hsize : time + timeRest + 2 * positions + 2 * states + input.length +
      (output ++ (List.range positions).flatMap piece).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        selectionTape tick [] (time, timeRest)
          [positions, states, positions, states] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forSelectedTimePositions tm tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick [] (time, timeRest) [positions, states, positions, states] input
          (output ++ (List.range positions).flatMap piece)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + positionIterationMoves size bound ⦄ := by
  have ha (position rest : Nat) (hcount : position + rest + 1 = positions)
      (place : ℤ) (steps : Nat) := atOtherFirstChoices_spec tick action time timeRest position
    rest positions states hpositions hstates input
    (output ++ (List.range position).flatMap piece)
    ((output ++ (List.range position).flatMap piece) ++ piece position) label bound
    (hleaf position rest hcount _ (by
      have hp := ((List.range_sublist.mpr (show position + 1 ≤ positions by lia)).flatMap
        piece).length_le
      have hout : ((output ++ (List.range position).flatMap piece) ++ piece position).length ≤
          (output ++ (List.range positions).flatMap piece).length := by
        simpa [List.range_succ, List.length_append, Nat.add_assoc] using
          Nat.add_le_add_left hp output.length
      lia)) place steps
  have hr := onFollowingBlocks_append_spec tick (atOtherFirstChoices tick action) []
    (List.replicate time tick) timeRest positions
    [List.replicate states tick, List.replicate positions tick, List.replicate states tick, input]
    output piece label (bound + 6 * size + 18) (by
      intro position rest hcount place steps
      have hrun := ha position rest hcount place steps
      have hrest : rest ≤ size := by lia
      have hp : positions - 1 ≤ size := by lia
      have hs : states - 1 ≤ size := by lia
      vcgen [hrun]
      all_goals simp_all [selectionTape, List.range_succ, List.append_assoc]
      all_goals lia) origin elapsed
  have hwork : positions * (bound + 6 * size + 18 + 2) + 2 * timeRest + 8 ≤
      positionIterationMoves size bound := by
    dsimp [positionIterationMoves]
    gcongr <;> lia
  vcgen [forSelectedTimePositions, hr]
  all_goals simp_all [selectionTape]
  all_goals lia

end Algolean.Algorithms.NPToSAT.PositionIteration
