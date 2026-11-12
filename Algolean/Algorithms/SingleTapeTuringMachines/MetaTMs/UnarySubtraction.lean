/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockCounting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement

/-!
# Subtracting a unary word from a binary counter

* `subtractBlocks` subtracts the number of repetitions of a fixed word from an earlier binary
  counter. Each repetition subtracts one, regardless of its length. The result stays zero if
  the subtraction reaches zero before the source word ends.
* The source word, intervening words, and head position are preserved. Leading zeros may
  remain in the counter, so its length does not change.

This is a machine template. The containing machine fixes the digit symbols, repeated word,
control states, and number of intervening words once for every input length.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- These are the counter digits after subtraction, with the most significant digit first. -/
@[expose] def subtractDigits (bits : List Bool) (count : Nat) : List Bool :=
  match count with
  | 0 => bits
  | n + 1 =>
    let previous := subtractDigits bits n
    if binaryValue previous.reverse = 0 then previous
    else (decrementBits previous.reverse).reverse

/-- Subtracting zero leaves the counter digits unchanged. -/
@[simp] theorem subtractDigits_zero (bits : List Bool) : subtractDigits bits 0 = bits := rfl

/-- Subtraction preserves the number of counter digits, including leading zeros. -/
@[simp] theorem subtractDigits_length (bits : List Bool) (count : Nat) :
    (subtractDigits bits count).length = bits.length := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [subtractDigits]
    split_ifs <;> simpa only [List.length_reverse, length_decrementBits] using ih

/-- Reading the resulting digits gives subtraction of natural numbers, which stops at zero. -/
theorem subtractDigits_value (bits : List Bool) (count : Nat) :
    binaryValue (subtractDigits bits count).reverse = binaryValue bits.reverse - count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [subtractDigits]
    split_ifs with hzero
    · rw [hzero]
      rw [ih] at hzero
      lia
    · have hp : 0 < binaryValue (subtractDigits bits count).reverse := by lia
      have hs := binaryValue_decrementBits (subtractDigits bits count).reverse hp
      simp only [List.reverse_reverse]
      lia

/-- These are binary digits on the tape, with the most significant digit first. -/
@[expose] def counterDigits (zero one : Γ) (bits : List Bool) : List Γ :=
  bits.map (fun bit => if bit then one else zero)

private noncomputable def subtractOne (zero one : Γ) (zeroFlag positiveFlag ready : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  testZero tm one zeroFlag positiveFlag
  ifₜ state =ₜ some positiveFlag then
    decrementLeft tm zero one
  else
    pure ()
  state ←ₜ ready

private theorem subtractOne_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroFlag positiveFlag ready : tm.State) (hflags : zeroFlag ≠ positiveFlag)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      subtractOne zero one zeroFlag positiveFlag ready
    ⦃ fun _ cost final => final.config = ⟨some ready,
        BiTape.segment StackTape.nil (counterDigits zero one (subtractDigits bits 1)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 6 * bits.length + 6 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  by_cases hzero : binaryValue bits.reverse = 0
  · vcgen [subtractOne, testZero_spec (tm := tm) zero one hne zeroFlag positiveFlag hflags
      bits tail label origin initial.steps, Spec.branch_false_spec]
    case vc1 => simp_all [counterDigits]
    case vc2 =>
      refine ⟨by simp_all, ?_⟩
      dsimp only [binderNameHint]
      vcgen
      simp_all [counterDigits, subtractDigits]
      lia
  · have hcount := carryCount_le_length (bits.reverse.map Bool.not)
    vcgen [subtractOne, testZero_spec (tm := tm) zero one hne zeroFlag positiveFlag hflags
        bits tail label origin initial.steps,
      decrementLeft_spec (tm := tm) zero one hne bits (by lia) tail
        (some positiveFlag) origin (initial.steps + 2 * bits.length + 2)]
    all_goals
      simp_all [counterDigits, subtractDigits]
      all_goals lia

private noncomputable def visitSubtract (zero one : Γ) (zeroFlag positiveFlag ready : tm.State)
    (near : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  onCounter tm (subtractOne zero one zeroFlag positiveFlag ready) near
  seekRightBlank tm

private theorem visitSubtract_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroFlag positiveFlag ready : tm.State) (hflags : zeroFlag ≠ positiveFlag)
    (bits : List Bool) (near : List (List Γ)) (before after : List Γ) (tail : StackTape Γ)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some ready,
        BiTape.segment
          (StackTape.prepend before.reverse (counterLeft (counterDigits zero one bits) near))
          [] (StackTape.prepend after (StackTape.cons none tail))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitSubtract zero one zeroFlag positiveFlag ready near.length
    ⦃ fun _ cost final => final.config = ⟨some ready,
        BiTape.segment (StackTape.prepend before.reverse
          (counterLeft (counterDigits zero one (subtractDigits bits 1)) near))
          [] (StackTape.prepend after (StackTape.cons none tail))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          2 * before.length + 8 * bits.length +
            2 * (near.map List.length).sum + 4 * near.length + 12 ⦄ := by
  let later := StackTape.prepend after (StackTape.cons none tail)
  have ha (position : ℤ) (steps : Nat) := subtractOne_spec (tm := tm) zero one hne
    zeroFlag positiveFlag ready hflags bits (counterRight near before later)
    (some ready) position steps
  have hv := onCounter_spec (tm := tm) (subtractOne zero one zeroFlag positiveFlag ready)
    (counterDigits zero one bits) (counterDigits zero one (subtractDigits bits 1))
    near before later later
    (some ready) (some ready) (6 * bits.length + 6)
    (by simpa [counterDigits, Nat.add_assoc] using ha)
    (origin - before.length) (elapsed + before.length + 2)
  vcgen [visitSubtract,
    seekLeftEnd_le_spec (tm := tm) ((counterLeft (counterDigits zero one bits) near).tail)
      later before.reverse [] (some ready) origin elapsed,
    hv,
    seekRightBlank_le_spec (tm := tm)
      (counterLeft (counterDigits zero one (subtractDigits bits 1)) near)
      later before (some ready) (origin - before.length)
      (elapsed + before.length + 2 + (6 * bits.length + 6) + bits.length + bits.length +
        2 * (near.map List.length).sum + 4 * near.length + 4)]
  all_goals
    simp_all [later, counterDigits]
    all_goals lia

/--
This machine template subtracts one for each source repetition and stops decreasing at zero.
It preserves the unary source and restores its first cell under the head. Its finite control
states and tape symbols are fixed once when the containing machine is constructed.
-/
noncomputable def subtractBlocks (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (unitTail : List Γ) (zeroFlag positiveFlag ready : tm.State)
    (near : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  forBlocks tm tick unitTail (visitSubtract zero one zeroFlag positiveFlag ready near)

/-- This bounds subtraction in terms of counter length, source length, and intervening words. -/
@[expose] def subtractBlocksMoves (unit digits count distance : Nat) : Nat :=
  32 * (unit + 1) * (digits + count + distance + 2) * (count + 1)

/--
The counter loses exactly the unary count, with subtraction stopping at zero. All other tape
cells and the head position are preserved, and the number of counter digits is unchanged.
-/
@[spec] theorem subtractBlocks_spec (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (unitTail : List Γ) (zeroFlag positiveFlag ready : tm.State)
    (hflags : zeroFlag ≠ positiveFlag) (bits : List Bool) (count : Nat)
    (near : List (List Γ)) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some ready,
        BiTape.segment (counterLeft (counterDigits zero one bits) near)
          (unaryWord (tick :: unitTail) count) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      subtractBlocks tm zero one tick unitTail zeroFlag positiveFlag ready near.length
    ⦃ fun _ cost final => final.config = ⟨some ready,
        BiTape.segment (counterLeft (counterDigits zero one (subtractDigits bits count)) near)
          (unaryWord (tick :: unitTail) count) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          subtractBlocksMoves (unitTail.length + 1) bits.length count (regionSpan near) ⦄ := by
  let lefts (index : Nat) :=
    (counterLeft (counterDigits zero one (subtractDigits bits index)) near).tail
  let bound := 16 * (unitTail.length + 2) * (bits.length + count + regionSpan near + 2)
  have ha : BlockAction tick unitTail count lefts (fun _ => tail) (some ready)
      (visitSubtract (tm := tm) zero one zeroFlag positiveFlag ready near.length) bound := by
    intro index rest hcount position steps
    have hv := visitSubtract_spec (tm := tm) zero one hne zeroFlag positiveFlag ready hflags
      (subtractDigits bits index) near (unaryWord (tick :: unitTail) index)
      (unitTail ++ unaryWord (tick :: unitTail) rest) tail position steps
    have hprefix : index * (unitTail.length + 1) ≤ count * (unitTail.length + 1) :=
      Nat.mul_le_mul_right _ (by lia)
    have hwork : 2 * (unaryWord (tick :: unitTail) index).length + 8 * bits.length +
        2 * (near.map List.length).sum + 4 * near.length + 12 ≤ bound := by
      have hlength : (unaryWord (tick :: unitTail) index).length ≤
          count * (unitTail.length + 1) := by
        simpa [unaryWord, List.length_flatten] using hprefix
      calc
        _ ≤ 2 * (count * (unitTail.length + 1)) + 8 * bits.length +
            2 * (near.map List.length).sum + 4 * near.length + 12 := by gcongr
        _ ≤ bound := by dsimp [bound, regionSpan]; ring_nf; lia
    have hnext : subtractDigits (subtractDigits bits index) 1 =
        subtractDigits bits (index + 1) := rfl
    vcgen [hv]
    all_goals
      simp_all [lefts, bound, regionSpan]
      all_goals ring_nf at *
      all_goals lia
  vcgen [subtractBlocks, forBlocks_spec tick unitTail count lefts (fun _ => tail) (some ready)
    (visitSubtract (tm := tm) zero one zeroFlag positiveFlag ready near.length)
    bound ha origin elapsed]
  all_goals
    simp_all [lefts, subtractBlocksMoves, bound, regionSpan]
    all_goals ring_nf at *
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
