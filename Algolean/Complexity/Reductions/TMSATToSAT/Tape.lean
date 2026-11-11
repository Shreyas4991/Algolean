/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Writing
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Tape regions for writing the TMSAT-to-SAT reduction

The machine uses one tape. From left to right, it stores temporary data, the original input,
and the output in separate regions. A blank separates consecutive regions. Each region begins
with one fixed symbol `marker : Γ`, so even an empty region has an occupied first cell.
The original input follows its marker without any changes to its symbols.

`prepare` creates empty working regions and an empty output region, preserving every input
symbol. It finishes on the first region's marker. With `k` working regions and an input of
length `n`, it uses exactly `2 * n + 2 * k + 7` head moves.

The representation uses `BiTape.segment` and `StackTape.separateWords`. The programs
`nextRegion` and `previousRegion` move between neighboring regions. The output is last so
that the existing `appendWord` program can extend it without overwriting another region.

`finish` erases the temporary regions and original input, removes the output's marker, and
leaves the head at the first output cell. The final tape follows CSLib's output convention.

The marker and the number of working regions are fixed when constructing the containing
Query machine, independently of the input and its length. The words themselves are tape data.
Every occupied cell contains a symbol of `Γ`; region boundaries use physical blank cells.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Tape

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type}

/--
This describes the head at the first region's marker, with one blank between successive regions.
The lists contain the region contents without their markers. An empty list of regions is blank.
-/
@[expose] def layout (marker : Γ) : List (List Γ) → BiTape Γ
  | [] => BiTape.nil
  | current :: rest => BiTape.segment StackTape.nil (marker :: current)
      (StackTape.separateWords (rest.map (marker :: ·)) StackTape.nil)

variable [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This writes the input's marker and the empty output region and returns to the input marker. -/
private def frameInput (marker : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  tape ←ₜ some marker
  moveₜ .Right
  seekRightBlank tm
  moveₜ .Right
  tape ←ₜ some marker
  moveₜ .Left
  seekLeftEnd tm

private theorem frameInput_spec (marker : Γ) (input : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      frameInput (tm := tm) marker
    ⦃ fun _ cost final => final.config = ⟨label, layout marker [input, []]⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps = elapsed + 2 * input.length + 7 ⦄ := by
  have hmarker : StackTape.cons (some marker) StackTape.nil = StackTape.mapSome [marker] := rfl
  vcgen [frameInput,
    seekRightBlank_segment_spec (StackTape.cons (some marker) StackTape.nil) StackTape.nil input
      label origin (elapsed + 2),
    seekLeftEnd_segment_spec StackTape.nil (StackTape.mapSome [marker])
      (input.reverse ++ [marker]) [] label (origin + input.length) (elapsed + input.length + 4)]
  all_goals cases input
  all_goals simp_all [TMState.move, TMState.moveCost, TMState.write, layout,
    BiTape.mk₁, BiTape.nil, BiTape.segment, BiTape.moveLeft, BiTape.moveRight, BiTape.write,
    List.reverse_append, sub_eq_add_neg]
  all_goals lia

/-- This places a fixed number of empty regions before the current first region. -/
private def prependEmpty (marker : Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    moveₜ .Left
    tape ←ₜ none
    moveₜ .Left
    tape ←ₜ some marker
    prependEmpty marker count

private theorem prependEmpty_spec (marker : Γ) (count : Nat) (current : List Γ)
    (rest : List (List Γ)) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label, layout marker (current :: rest)⟩ ∧
        initial.headPos = origin ∧ cost.steps = elapsed ⦄
      prependEmpty (tm := tm) marker count
    ⦃ fun _ cost final => final.config =
        ⟨label, layout marker (List.replicate count [] ++ current :: rest)⟩ ∧
        final.headPos = origin - 2 * count ∧ cost.steps = elapsed + 2 * count ⦄ := by
  induction count generalizing current rest origin elapsed with
  | zero =>
    vcgen [prependEmpty]
    simp_all
  | succ count ih =>
    vcgen [prependEmpty, ih [] (current :: rest) (origin - 2) (elapsed + 2)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost, layout,
      BiTape.segment, BiTape.moveLeft, BiTape.write, List.replicate_succ', sub_eq_add_neg]
    all_goals lia

/--
This machine template preserves the input, places empty working regions before it, and places
an empty output region after it. It finishes at the first region's marker. The containing
machine fixes `marker` and `workCount` once, independently of the input and its length.
-/
def prepare (tm : SingleTapeTM Γ) (marker : Γ) (workCount : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  frameInput marker
  prependEmpty marker workCount

/-- Preparing the regions preserves the input and records the exact head position and move count. -/
@[spec] theorem prepare_spec (marker : Γ) (workCount : Nat) (input : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      prepare tm marker workCount
    ⦃ fun _ cost final => final.config =
        ⟨label, layout marker (List.replicate workCount [] ++ [input, []])⟩ ∧
        final.headPos = origin - (2 * workCount + 1 : Nat) ∧
        cost.steps = elapsed + 2 * input.length + 2 * workCount + 7 ⦄ := by
  vcgen [prepare, frameInput_spec marker input label origin elapsed,
    prependEmpty_spec marker workCount input [[]] label (origin - 1)
      (elapsed + 2 * input.length + 7)]
  all_goals simp_all
  all_goals lia

/--
Initialization preserves the input and control state and creates exactly the requested empty
working regions and one empty output region. The theorem gives the exact head position and
number of moves and applies after any earlier computation with the displayed input tape.
-/
theorem prepare_correct (marker : Γ) (workCount : Nat) (input : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.mk₁ input) :
    Runs (prepare tm marker workCount) s
      (layout marker (List.replicate workCount [] ++ [input, []]))
      (s.headPos - (2 * workCount + 1 : Nat)) (2 * input.length + 2 * workCount + 7) := by
  apply Spec.runs
  vcgen [prepare_spec marker workCount input s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

private def eraseRegions (tm : SingleTapeTM Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    eraseRight tm
    moveₜ .Right
    eraseRegions tm count

private theorem eraseRegions_spec (marker : Γ) (regions : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let moves : Nat := (regions.map fun region => region.length + 2).sum
    ⦃ fun cost current => current.config = ⟨label, layout marker (regions ++ [output])⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseRegions tm regions.length
    ⦃ fun _ cost final => final.config = ⟨label, layout marker [output]⟩ ∧
        final.headPos = origin + moves ∧ cost.steps = elapsed + moves ⦄ := by
  dsimp only
  induction regions generalizing origin elapsed with
  | nil =>
    simp only [List.length_nil, eraseRegions]
    vcgen
    simp_all
  | cons region regions ih =>
    simp only [List.length_cons, eraseRegions]
    vcgen [eraseRight_segment_spec (tm := tm) StackTape.nil
        (StackTape.separateWords ((regions ++ [output]).map (marker :: ·)) StackTape.nil)
        (marker :: region) label origin elapsed,
      ih (origin + (region.length + 2 : Nat)) (elapsed + region.length + 2)]
    all_goals
      cases regions
      all_goals
        simp_all [layout, TMState.move, TMState.moveCost, BiTape.segment, BiTape.moveRight,
          List.map_append, StackTape.separateWords]
        all_goals lia

/--
This machine template erases `count` regions preceding the output, then removes the output's
marker. It leaves only the output word on the tape, with the head at its first cell. The
containing machine fixes the number of regions independently of the input and their lengths.
-/
def finish (tm : SingleTapeTM Γ) (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseRegions tm count
  eraseAndMove tm

/--
Finishing preserves the output and control state and erases every other occupied cell.
The exact move count includes each erased symbol and each separating blank crossed.
-/
@[spec] theorem finish_spec (marker : Γ) (regions : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let moves : Nat := (regions.map fun region => region.length + 2).sum + 1
    ⦃ fun cost current => current.config = ⟨label, layout marker (regions ++ [output])⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      finish tm regions.length
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.mk₁ output⟩ ∧
        final.headPos = origin + moves ∧ cost.steps = elapsed + moves ⦄ := by
  dsimp only
  vcgen [finish, eraseRegions_spec marker regions output label origin elapsed, eraseAndMove_spec]
  all_goals
    cases output
    all_goals
      simp_all [layout, TMState.move, TMState.moveCost, TMState.write,
        BiTape.mk₁, BiTape.nil, BiTape.segment, BiTape.write, BiTape.moveRight]
      all_goals lia

/-- The cleanup program produces precisely the clean output tape with the stated move count. -/
theorem finish_correct (marker : Γ) (regions : List (List Γ)) (output : List Γ)
    (s : TMState tm) (htape : s.config.BiTape = layout marker (regions ++ [output])) :
    let moves : Nat := (regions.map fun region => region.length + 2).sum + 1
    Runs (finish tm regions.length) s (BiTape.mk₁ output) (s.headPos + moves) moves := by
  apply Spec.runs
  vcgen [finish_spec marker regions output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.TMSATToSAT.Tape
