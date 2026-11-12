/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.HeadChoices

/-!
# Finding cells inside the initial input and certificate

* `compare` tests whether a selected tape position lies beyond the left or right blank interval
  in the verifier's initial tape. Each interval has length equal to the transition bound.
* `compare_spec` proves that the answer is stored in the chosen control state while the tape
  and head position are restored.

The containing machine fixes which side to test and which states represent the answers.
The selected position and transition bound are read from the tape.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.InitialComparison

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open NPToSAT.Computation.HeadChoices
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This tests whether the transition bound is at most the number of cells before or after the
selected position, according to the chosen side.
-/
noncomputable def compare (tm : SingleTapeTM Γ) [DecidableEq tm.State] (zero one tick : Γ)
    (greater atMost : tm.State) (rest : Bool) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (onCounter tm
    (compareBlocksLeOffset tm zero one tick greater atMost 0 1 (if rest then 1 else 0))
      (if rest then 4 else 5))

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem comparisonMoves_le (first second current before between size : Nat)
    (crossed : List (List Γ))
    (hsize : first + second + current + before + between + regionSpan crossed + 16 ≤ size) :
    2 * current + 2 + (compareBlocksOffsetMoves first second before between 0 +
      2 * second + 2 * (crossed.map List.length).sum + 4 * crossed.length + 4) ≤
        comparisonTime size := by
  have hm : compareBlocksOffsetMoves first second before between 0 ≤
      512 * (size + 16) ^ 2 := by
    dsimp [compareBlocksOffsetMoves]
    gcongr
    all_goals lia
  dsimp only [regionSpan] at hsize
  dsimp only [comparisonTime]
  ring_nf at hm ⊢
  lia

/-- The comparison records its answer and restores the complete tape and original head position. -/
@[spec] theorem compare_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (greater atMost : tm.State) (hstates : greater ≠ atMost) (rest : Bool)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + output.length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      compare tm zero one tick greater atMost rest
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if choice.time.2 ≤ (if rest then choice.firstPosition.2
          else choice.firstPosition.1) then atMost else greater)) origin final ∧
        cost.steps ≤ elapsed + comparisonTime size ⦄ := by
  let word := fun count => List.replicate count tick
  let before := [word choice.time.1]
  let between := if rest then [word choice.firstPosition.1] else []
  let atPosition := between ++ word choice.time.2 :: before
  let crossed := if rest then [word choice.secondPosition.2, word choice.secondPosition.1,
      word choice.firstState.2, word choice.firstState.1]
    else [word choice.secondPosition.2, word choice.secondPosition.1,
      word choice.firstState.2, word choice.firstState.1, word choice.firstPosition.2]
  let selected := if rest then choice.firstPosition.2 else choice.firstPosition.1
  let current := word choice.secondState.1
  let near := ActiveChoices.leftWords tick choice
  let parts := ActiveChoices.rightWords tick choice input
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let moves := compareBlocksOffsetMoves choice.time.2 selected
    (regionSpan before) (regionSpan between) 0
  let visitMoves := moves + 2 * selected + 2 * (crossed.map List.length).sum +
    4 * crossed.length + 4
  have hframe : earlierLeft (counterLeft [] atPosition).tail
      (word selected) crossed = counterLeft [] near := by
    cases rest <;> simp [earlierLeft_counterLeft, atPosition, before, between, crossed, selected,
      near, ActiveChoices.leftWords, word]
  have ha (position : ℤ) (steps : Nat) := onEarlierWord_spec (tm := tm)
    (compareBlocksLeOffset tm zero one tick greater atMost 0 1 (if rest then 1 else 0))
    (counterLeft [] atPosition).tail (counterLeft [] atPosition).tail (word selected) crossed
    current tail tail label (some (if choice.time.2 ≤ selected then atMost else greater)) moves
    (by
      intro position steps
      cases rest
      all_goals
        simpa [comparisonLeft, before, between, atPosition, counterRight, word, selected, moves]
          using compareBlocksLeOffset_spec (tm := tm) zero one hne tick greater atMost hstates
            0 choice.time.2 selected before between (counterRight crossed current tail)
            label position steps) position steps
  simp only [hframe] at ha
  have hcap : choice.time.2 + selected + choice.secondState.1 + regionSpan before +
      regionSpan between + regionSpan crossed + 16 ≤ size := by
    cases rest
    all_goals
      simp only [before, between, crossed, selected, word, regionSpan_cons, regionSpan_nil,
        List.length_replicate, Bool.false_eq_true, ite_false, ite_true]
      dsimp only [ActiveChoices.size] at hsize
      lia
  have hbound : 2 * current.length + 2 + visitMoves ≤ comparisonTime size := by
    simpa only [current, word, List.length_replicate, visitMoves, moves] using
      comparisonMoves_le choice.time.2 selected choice.secondState.1 (regionSpan before)
        (regionSpan between) size crossed hcap
  have hr := onPrefixAtMark_output_spec (tm := tm)
    (onCounter tm (compareBlocksLeOffset tm zero one tick greater atMost 0 1
      (if rest then 1 else 0)) (if rest then 4 else 5)) near current parts output output label
    (some (if choice.time.2 ≤ selected then atMost else greater)) visitMoves (by
      intro position steps
      cases rest
      all_goals
        simpa [tail, visitMoves, crossed, word, selected, Nat.add_assoc] using
          (ha position steps)) origin elapsed
  vcgen [compare, hr]
  all_goals
    simp_all [AtPair, pairTape, near, parts, current, word, selected]
    all_goals lia

end Algolean.Algorithms.NPToSAT.InitialComparison
