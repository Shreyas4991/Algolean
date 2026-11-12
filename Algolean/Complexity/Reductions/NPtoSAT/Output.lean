/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.ChoiceIteration
public import Algolean.Problems.Encodings.SAT
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.RegionWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Leaving the completed SAT word on the tape

The program adds the symbol ending the formula and erases the five unary bounds and preserved
input. It then removes the temporary symbol before the output. The final tape contains exactly the
SAT word, with the head at its first symbol, as required by CSLib's computation convention.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.Output

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Problems.SAT
open NPToTMSAT.ChoiceIteration
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def eraseFollowing (tm : SingleTapeTM Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    moveₜ .Right
    eraseRight tm
    eraseFollowing tm count

private theorem eraseFollowing_spec (words : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil []
          (StackTape.separateWords words (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseFollowing tm words.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil [] (StackTape.mapSome output)⟩ ∧
        final.headPos = origin + regionSpan words ∧
        cost.steps = elapsed + regionSpan words ⦄ := by
  induction words generalizing origin elapsed with
  | nil =>
    simp only [List.length_nil, eraseFollowing]
    vcgen
    simp_all [StackTape.separateWords]
  | cons word words ih =>
    have he := eraseRight_segment_spec (tm := tm) StackTape.nil
      (StackTape.separateWords words (StackTape.mapSome output)) word label (origin + 1)
      (elapsed + 1)
    have hi := ih (origin + 1 + word.length) (elapsed + 1 + word.length)
    simp only [List.length_cons, eraseFollowing]
    vcgen [he, hi]
    all_goals
      simp_all [TMState.move, TMState.moveCost, StackTape.separateWords,
        regionSpan]
      all_goals lia

private def clearSource (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  eraseFollowing tm 6
  moveₜ .Right
  eraseAndMove tm

private theorem clearSource_spec (tick : Γ) (times positions states : Nat)
    (input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let size := times + 2 * positions + 2 * states + input.length + 7
    ⦃ fun cost current => current.config =
        ⟨label, NPToTMSAT.ChoiceIteration.layout tick times positions states
          (tick :: input) (tick :: output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      clearSource tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.mk₁ output⟩ ∧
        final.headPos = origin + size + 1 ∧ cost.steps ≤ elapsed + size + 3 ⦄ := by
  dsimp only
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  have he := eraseFollowing_spec (tm := tm)
    [List.replicate times tick, List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, tick :: input]
    (tick :: output) label (origin - 1) (initial.steps + 1)
  simp only [List.length_cons, List.length_nil] at he
  have hm :
      (NPToTMSAT.ChoiceIteration.layout tick times positions states (tick :: input)
        (tick :: output)).moveLeft =
      BiTape.segment StackTape.nil [] (StackTape.separateWords
        [List.replicate times tick, List.replicate positions tick, List.replicate states tick,
          List.replicate positions tick, List.replicate states tick, tick :: input]
        (StackTape.mapSome (tick :: output))) := by
    simpa [NPToTMSAT.ChoiceIteration.layout] using
      BiTape.segment_moveLeft_gap StackTape.nil (List.replicate times tick)
        (StackTape.separateWords
          [List.replicate positions tick, List.replicate states tick, List.replicate positions tick,
            List.replicate states tick, tick :: input] (StackTape.mapSome (tick :: output)))
  vcgen [clearSource, he, eraseAndMove_spec]
  all_goals
    cases output
    all_goals
      simp_all [regionSpan, TMState.move, TMState.moveCost, TMState.write,
        BiTape.segment, BiTape.moveRight, BiTape.write, BiTape.mk₁, BiTape.nil]
    all_goals lia

/--
This fixed program finishes a formula, erases the source words and input, and removes the
temporary symbol before the output. It leaves only the formula, with the head at its first symbol.
-/
def finish (tm : SingleTapeTM Γ) (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  appendFromRegion tm (code (.inr 5)) 5
  clearSource tm

/-- Finishing produces a clean output tape and uses a linear number of moves in the tape size. -/
@[spec] theorem finish_spec (tick : Γ) (code : CodeSymbol → List Γ)
    (times positions states : Nat) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let size := times + 2 * positions + 2 * states + input.length + 7
    ⦃ fun cost current => current.config =
        ⟨label, NPToTMSAT.ChoiceIteration.layout tick times positions states
          (tick :: input) (tick :: output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finish tm code
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.mk₁ (output ++ code (.inr 5))⟩ ∧
        final.headPos = origin + size + 1 ∧ cost.steps ≤
          elapsed + 3 * size + 2 * output.length + 2 * (code (.inr 5)).length + 17 ⦄ := by
  dsimp only
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  have ha := appendFromRegion_spec (tm := tm) (code (.inr 5)) (List.replicate times tick)
    [List.replicate positions tick, List.replicate states tick, List.replicate positions tick,
      List.replicate states tick, tick :: input] (tick :: output) StackTape.nil label origin
    initial.steps
  simp only [List.length_cons, List.length_nil] at ha
  have hc := clearSource_spec (tm := tm) tick times positions states input
    (output ++ code (.inr 5)) label origin
    (initial.steps + 2 * (times + regionSpan
      [List.replicate positions tick, List.replicate states tick, List.replicate positions tick,
        List.replicate states tick, tick :: input] + (tick :: output).length +
          (code (.inr 5)).length) + 12)
  vcgen [finish, ha, hc]
  all_goals simp_all [NPToTMSAT.ChoiceIteration.layout, regionSpan]
  all_goals lia

end Algolean.Algorithms.NPToSAT.Output
