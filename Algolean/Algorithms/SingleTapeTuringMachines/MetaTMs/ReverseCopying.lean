/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.WordCopying

/-!
# Copying binary digits in reverse order

* `copyBitsReverseAcross` reads a binary word from right to left and appends its reversed
  digits to a later output region. Each digit is written with its chosen representation.
* The source word, intervening words, earlier output, and cells farther left are preserved.
  The head returns to the source's first cell, including when the word is empty.
* The exact move count is the existing `copyBitsMoves`, which also counts forward copying.

This is a machine template. The containing machine fixes the digit symbols, output words,
and number of intervening regions. The digits and their number are read from the tape.
This allows a counter to be read in the digit order used for binary variable names.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def reverseLoop (zero one : Γ) (code : Bool → List Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some one then
      appendFromCell tm one (code true) count
    else
      appendFromCell tm zero (code false) count
    moveₜ .Left

private theorem reverseLoop_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (bits done : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        (BiTape.segment (StackTape.prepend (done.map (fun bit => if bit then one else zero))
          (StackTape.cons none (StackTape.separateWords parts (StackTape.mapSome output))))
          (bits.map (fun bit => if bit then one else zero)) left).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      reverseLoop (tm := tm) zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        (BiTape.segment (StackTape.prepend
          ((bits.reverse ++ done).map (fun bit => if bit then one else zero))
          (StackTape.cons none
            (StackTape.separateWords parts (StackTape.mapSome (output ++ bits.flatMap code)))))
          [] left).mirror⟩ ∧
        final.headPos = origin - bits.length ∧ cost.steps = elapsed +
          (width + 1) * bits.length ^ 2 +
            2 * bits.length * (done.length + regionSpan parts + output.length) +
              (width + 10) * bits.length ⦄ := by
  induction bits generalizing done output origin elapsed with
  | nil =>
    unfold reverseLoop
    vcgen [Spec.while_false_spec]
    simp_all [BiTape.segment, BiTape.mirror]
  | cons bit bits ih =>
    let digit : Bool → Γ := fun bit => if bit then one else zero
    unfold reverseLoop
    vcgen [Spec.while_step_spec (loop := reverseLoop (tm := tm) zero one code parts.length)
        (hloop := rfl),
      appendFromCell_spec one (code true) (done.map digit) output parts
        (StackTape.prepend (bits.map digit) (StackTape.cons none left)) label origin elapsed,
      appendFromCell_spec zero (code false) (done.map digit) output parts
        (StackTape.prepend (bits.map digit) (StackTape.cons none left)) label origin elapsed,
      ih (bit :: done) (output ++ code bit) (origin - 1)
        (elapsed + 2 * (done.length + regionSpan parts + output.length + width) + 11)]
    all_goals
      cases bit <;>
      cases bits
      all_goals
        simp_all [digit, BiTape.segment, BiTape.mirror, BiTape.moveLeft,
          TMState.move, TMState.moveCost, List.reverse_cons, StackTape.prepend_append,
          List.append_assoc]
        all_goals ring_nf at *
        all_goals simp_all

/--
This machine template appends a reversed copy beyond `count` intervening regions. It starts
and finishes at the source's first cell. A blank must precede the source, and all cells after
the existing output must be blank. The source and every intervening region remain unchanged.
-/
def copyBitsReverseAcross (tm : SingleTapeTM Γ) (zero one : Γ) (code : Bool → List Γ)
    (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Left
  reverseLoop zero one code count
  moveₜ .Right

/-- Reversed copying preserves the source and restores the head with the exact quadratic cost. -/
@[spec] theorem copyBitsReverseAcross_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (bits : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyBitsReverseAcross tm zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ bits.reverse.flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          copyBitsMoves width bits.length (regionSpan parts) output.length ⦄ := by
  vcgen [copyBitsReverseAcross,
    seekRightBlank_segment_spec (StackTape.cons none left)
      (StackTape.separateWords parts (StackTape.mapSome output))
      (bits.map (fun bit => if bit then one else zero)) label origin elapsed,
    reverseLoop_spec zero one hne code width hwidth bits.reverse [] parts output left
      label (origin + bits.length - 1) (elapsed + bits.length + 1)]
  case vc1 =>
    cases hbits : bits.reverse
    all_goals
      simp_all [TMState.move, TMState.moveCost, BiTape.segment, BiTape.mirror,
        BiTape.moveLeft, List.map_reverse]
      all_goals lia
  case vc2 =>
    cases bits
    all_goals
      simp_all [TMState.move, TMState.moveCost, BiTape.segment, BiTape.mirror,
        BiTape.moveRight, copyBitsMoves]
      all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
