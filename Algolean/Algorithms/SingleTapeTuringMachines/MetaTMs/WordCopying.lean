/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.RegionWriting

/-!
# Copying binary words across intervening tape regions

* `copyBitsAcross` reads a binary word, appends the chosen representation of each bit to
  a later output region, and returns to the source's first cell.
* `appendLengthHeader` writes one true bit per source bit, followed by a false bit.
  It preserves the source and returns to its first cell.
* `copyBitsMoves` gives its exact number of head moves when both bit representations have
  the same length. Empty source words and empty intervening regions are allowed.

This is a machine template. The containing machine fixes the digit symbols, the two output
representations, and the number of intervening regions. It reads every source bit from the
tape. The source, intervening regions, earlier output, and cells farther left are preserved.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def copyCurrent (restore : Γ) (word : List Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendFromCell tm restore word count
  moveₜ .Right

private theorem copyCurrent_spec (restore : Γ) (word rest output : List Γ)
    (parts : List (List Γ)) (left : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left (restore :: rest)
        (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyCurrent (tm := tm) restore word parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons (some restore) left) rest
          (StackTape.separateWords parts (StackTape.mapSome (output ++ word)))⟩ ∧
        final.headPos = origin + 1 ∧ cost.steps = elapsed +
          2 * (rest.length + regionSpan parts + output.length + word.length) + 11 ⦄ := by
  vcgen [copyCurrent,
    appendFromCell_spec restore word rest output parts left label origin elapsed]
  all_goals
    cases rest <;>
    simp_all [TMState.move, TMState.moveCost, BiTape.segment, BiTape.moveRight]

private def copyBitsLoop (zero one : Γ) (code : Bool → List Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some one then
      copyCurrent one (code true) count
    else
      copyCurrent zero (code false) count

private theorem copyBitsLoop_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (bits : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left
        (bits.map (fun bit => if bit then one else zero))
        (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyBitsLoop (tm := tm) zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (bits.map (fun bit => if bit then one else zero)).reverse left) []
          (StackTape.separateWords parts (StackTape.mapSome (output ++ bits.flatMap code)))⟩ ∧
        final.headPos = origin + bits.length ∧ cost.steps = elapsed +
          (width + 1) * bits.length ^ 2 +
            2 * bits.length * (regionSpan parts + output.length) +
              (width + 10) * bits.length ⦄ := by
  induction bits generalizing output left origin elapsed with
  | nil =>
    unfold copyBitsLoop
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit bits ih =>
    unfold copyBitsLoop
    vcgen [Spec.while_step_spec (loop := copyBitsLoop (tm := tm) zero one code parts.length)
        (hloop := rfl),
      copyCurrent_spec one (code true) (bits.map (fun bit => if bit then one else zero))
        output parts left label origin elapsed,
      copyCurrent_spec zero (code false) (bits.map (fun bit => if bit then one else zero))
        output parts left label origin elapsed,
      ih (output ++ code bit) (StackTape.cons (some (if bit then one else zero)) left)
        (origin + 1) (elapsed + 2 * (bits.length + regionSpan parts + output.length + width) + 11)]
    all_goals
      cases bit
      all_goals
        simp_all [List.reverse_cons, StackTape.prepend_append, List.append_assoc]
        all_goals ring_nf at *
        all_goals simp_all

/--
This machine template copies a binary word to the output beyond `count` intervening regions.
It replaces each copied bit by its fixed `code` word and returns to the source's first cell.
A blank must precede the source, and all cells beyond the output must initially be blank.
-/
def copyBitsAcross (tm : SingleTapeTM Γ) (zero one : Γ) (code : Bool → List Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  copyBitsLoop zero one code count
  seekLeftEnd tm

/-- This counts the copy and return moves from the representation width and tape word lengths. -/
@[expose] def copyBitsMoves (width size distance output : Nat) : Nat :=
  (width + 1) * size ^ 2 + 2 * size * (distance + output) + (width + 11) * size + 2

/-- Copying preserves the source and intervening words and restores the head with the exact cost. -/
@[spec] theorem copyBitsAcross_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (bits : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyBitsAcross tm zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome (output ++ bits.flatMap code)))⟩ ∧
        final.headPos = origin ∧
        cost.steps = elapsed +
          copyBitsMoves width bits.length (regionSpan parts) output.length ⦄ := by
  vcgen [copyBitsAcross,
    copyBitsLoop_spec zero one hne code width hwidth bits parts output (StackTape.cons none left)
      label origin elapsed,
    seekLeftEnd_segment_spec left
      (StackTape.separateWords parts (StackTape.mapSome (output ++ bits.flatMap code)))
      (bits.map (fun bit => if bit then one else zero)).reverse [] label (origin + bits.length)
      (elapsed + (width + 1) * bits.length ^ 2 +
        2 * bits.length * (regionSpan parts + output.length) + (width + 10) * bits.length)]
  all_goals
    simp_all [copyBitsMoves]
    all_goals lia

/-- This counts the moves used to copy the source length and write its ending bit. -/
@[expose] def lengthHeaderMoves (width size distance output : Nat) : Nat :=
  copyBitsMoves width size distance output +
    (2 * (size + distance + output + width * size + width) + 12)

/--
This machine template appends one represented true bit per source bit and a represented false
bit after them. It preserves the source and the intervening regions and restores the head.
The digit symbols, output representations, and number of regions are fixed with the program.
-/
def appendLengthHeader (tm : SingleTapeTM Γ) (zero one : Γ) (code : Bool → List Γ)
    (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  copyBitsAcross tm zero one (fun _ => code true) count
  appendFromRegion tm (code false) count

/-- Writing the length header preserves its source and records the exact move count. -/
@[spec] theorem appendLengthHeader_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (bits : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendLengthHeader tm zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome
            (output ++ (List.replicate bits.length true ++ [false]).flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          lengthHeaderMoves width bits.length (regionSpan parts) output.length ⦄ := by
  have hlength : (bits.flatMap fun _ => code true).length = width * bits.length := by
    simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  have hconstant := congrArg (List.flatMap code) (List.map_const' (l := bits) (b := true))
  simp only [List.flatMap_map] at hconstant
  vcgen [appendLengthHeader,
    copyBitsAcross_spec zero one hne (fun _ => code true) width (fun _ => hwidth true)
      bits parts output left label origin elapsed,
    appendFromRegion_spec (code false) (bits.map (fun bit => if bit then one else zero))
      parts (output ++ bits.flatMap (fun _ => code true)) left label origin
      (elapsed + copyBitsMoves width bits.length (regionSpan parts) output.length)]
  all_goals
    simp_all [lengthHeaderMoves, List.append_assoc]
    all_goals ring_nf at *

end Algolean.Algorithms.SingleTapeTuringMachines
