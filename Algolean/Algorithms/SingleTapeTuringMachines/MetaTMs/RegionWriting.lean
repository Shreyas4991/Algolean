/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Writing

/-!
# Appending beyond several words on one tape

* `appendAcross` starts on a blank, crosses a fixed number of words, appends a fixed word
  to the final region, and returns to the starting blank.
* `appendFromRegion` performs the same operation from the beginning of a source word.
* `appendFromCell` temporarily marks an occupied source cell, appends beyond its region, and
  restores that cell and the head.

These are machine templates. The containing machine fixes the number of intervening regions
and the appended word once. The words already on the tape may have arbitrary lengths, including
zero. Every intervening word and all cells farther left are preserved.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/-- This counts the cells occupied by the words and their following blank separators. -/
@[expose] def regionSpan (parts : List (List Symbol)) : Nat :=
  (parts.map List.length).sum + parts.length

/--
This machine template appends `word` beyond `count` intervening regions and returns to the
starting blank. All cells beyond the final output region must initially be blank.
The number of regions is fixed with the program; their lengths are read from the tape.
-/
def appendAcross (tm : SingleTapeTM Symbol) (word : List Symbol) : Nat → Prog (TMQuery tm) Unit
  | 0 => do [TMQuery tm]
    moveₜ .Right
    appendWord tm none word
    moveₜ .Left
  | n + 1 => do [TMQuery tm]
    moveₜ .Right
    seekRightBlank tm
    appendAcross tm word n
    seekLeftGap tm

/-- Appending across the listed words preserves them and counts every head move. -/
@[spec] theorem appendAcross_spec (word : List Symbol) (parts : List (List Symbol))
    (output : List Symbol) (left : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        segment left [] (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendAcross tm word parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        segment left [] (StackTape.separateWords parts (StackTape.mapSome (output ++ word)))⟩ ∧
        final.headPos = origin ∧
        cost.steps = elapsed + 2 * (regionSpan parts + output.length + word.length) + 8 ⦄ := by
  induction parts generalizing left origin elapsed with
  | nil =>
    simp only [List.length_nil, appendAcross]
    vcgen [appendWord_spec none left output word label (origin + 1) (elapsed + 1)]
    all_goals
      simp_all [regionSpan, TMState.move, TMState.moveCost] <;>
      lia
  | cons part parts ih =>
    simp only [List.length_cons, appendAcross]
    vcgen [seekRightBlank_segment_spec (StackTape.cons none left)
        (StackTape.separateWords parts (StackTape.mapSome output)) part
        label (origin + 1) (elapsed + 1),
      ih (stackAppend part.reverse (StackTape.cons none left))
        (origin + 1 + part.length) (elapsed + 1 + part.length),
      seekLeftGap_segment_spec left part.reverse []
        (StackTape.separateWords parts (StackTape.mapSome (output ++ word)))
        label (origin + 1 + part.length)
        (elapsed + 1 + part.length +
          2 * (regionSpan parts + output.length + word.length) + 8)]
    all_goals
      simp_all [regionSpan, TMState.move, TMState.moveCost] <;>
      lia
/--
This machine template appends a fixed word to the output beyond the source and `count` more
regions. It preserves the source and returns to its first cell. That cell is the following
blank when the source is empty. A blank must precede the source.
-/
def appendFromRegion (tm : SingleTapeTM Symbol) (word : List Symbol) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  appendAcross tm word (count + 1)
  moveₜ .Right

/-- Appending from a source word preserves all earlier regions and restores the head. -/
@[spec] theorem appendFromRegion_spec (word input : List Symbol) (parts : List (List Symbol))
    (output : List Symbol) (left : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        segment (StackTape.cons none left) input
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendFromRegion tm word parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        segment (StackTape.cons none left) input
          (StackTape.separateWords parts (StackTape.mapSome (output ++ word)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          2 * (input.length + regionSpan parts + output.length + word.length) + 12 ⦄ := by
  have ha := appendAcross_spec (tm := tm) word (input :: parts) output left
    label (origin - 1) (elapsed + 1)
  simp only [List.length_cons] at ha
  vcgen [appendFromRegion, ha]
  all_goals
    cases input <;>
    simp_all [regionSpan, TMState.move, TMState.moveCost, BiTape.segment,
      BiTape.moveLeft, BiTape.moveRight] <;>
    lia

/--
This machine template appends a fixed word beyond the current source region and `count` more
regions. It temporarily erases the scanned symbol to find its way back, then restores it.
The containing machine fixes the restored symbol, appended word, and number of regions.
-/
def appendFromCell (tm : SingleTapeTM Symbol) (restore : Symbol) (word : List Symbol)
    (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  appendAcross tm word (count + 1)
  tape ←ₜ some restore

/-- Appending from an occupied cell preserves the source and restores the head and control state. -/
@[spec] theorem appendFromCell_spec (restore : Symbol) (word rest output : List Symbol)
    (parts : List (List Symbol)) (left : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, segment left (restore :: rest)
        (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendFromCell tm restore word parts.length
    ⦃ fun _ cost final => final.config = ⟨label, segment left (restore :: rest)
        (StackTape.separateWords parts (StackTape.mapSome (output ++ word)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          2 * (rest.length + regionSpan parts + output.length + word.length) + 10 ⦄ := by
  have ha := appendAcross_spec (tm := tm) word (rest :: parts) output left label origin elapsed
  simp only [List.length_cons] at ha
  vcgen [appendFromCell, ha]
  all_goals
    simp_all [regionSpan, TMState.write, BiTape.segment, BiTape.write] <;>
    lia

end Algolean.Algorithms.SingleTapeTuringMachines
