/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnarySubtraction

/-!
# Removing leading zeros from a binary counter

* `trimCounterBits` relates removal of leading zero digits to the existing natural-number code.
* `normalizeCounter` erases the leading zero cells and stops at the first remaining digit.
  The counter's value and the blank immediately after its digits stay unchanged.

This is a machine template. The containing machine fixes the digit symbols once. The digits
and the counter's length are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

private def Canonical : List Bool → Prop
  | [] => True
  | true :: rest => Canonical rest
  | false :: rest => rest ≠ [] ∧ Canonical rest

private theorem canonical_increment (bits : List Bool) (h : Canonical bits) :
    Canonical (incrementBits bits) := by
  induction bits with
  | nil => trivial
  | cons bit rest ih =>
    have ht : Canonical rest := by cases bit <;> simp_all [Canonical]
    cases bit
    · simpa [Canonical] using ht
    · have hn : incrementBits rest ≠ [] := by
        cases rest with
        | nil => simp
        | cons bit rest => cases bit <;> simp
      exact ⟨hn, ih ht⟩

private theorem canonical_encode (n : Nat) : Canonical (encodingNatBool.encode n) := by
  induction n with
  | zero => trivial
  | succ n ih => rw [← incrementBits_encodingNatBool]; exact canonical_increment _ ih

private theorem canonical_zero_iff (bits : List Bool) (h : Canonical bits) :
    binaryValue bits = 0 ↔ bits = [] := by
  induction bits with
  | nil => simp
  | cons bit rest ih =>
    cases bit
    · obtain ⟨hn, ht⟩ := h
      simp only [binaryValue, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or, List.cons_ne_nil, iff_false]
      exact fun hz => hn ((ih ht).mp hz)
    · simp [binaryValue]

private theorem canonical_injective (first second : List Bool)
    (hfirst : Canonical first) (hsecond : Canonical second)
    (hvalue : binaryValue first = binaryValue second) : first = second := by
  induction first generalizing second with
  | nil =>
    have hz : binaryValue second = 0 := by simpa using hvalue.symm
    exact ((canonical_zero_iff second hsecond).mp hz).symm
  | cons bit rest ih =>
    cases second with
    | nil =>
      have hz : binaryValue (bit :: rest) = 0 := by simpa using hvalue
      exact (canonical_zero_iff _ hfirst).mp hz
    | cons otherBit otherRest =>
      have ht : Canonical rest := by cases bit <;> simp_all [Canonical]
      have hu : Canonical otherRest := by cases otherBit <;> simp_all [Canonical]
      cases bit <;> cases otherBit
      all_goals simp only [binaryValue, Bool.false_eq_true, ite_false, ite_true] at hvalue
      all_goals try lia
      all_goals congr 1; apply ih _ ht hu; lia

private theorem canonical_append_true (bits : List Bool) : Canonical (bits ++ [true]) := by
  induction bits with
  | nil => trivial
  | cons bit rest ih => cases bit <;> simp_all [Canonical]

private theorem canonical_trim (bits : List Bool) :
    Canonical (bits.dropWhile (fun bit => !bit)).reverse := by
  induction bits with
  | nil => trivial
  | cons bit rest ih =>
    cases bit
    · simpa using ih
    · simpa using canonical_append_true rest.reverse

private theorem binaryValue_append_false (bits : List Bool) :
    binaryValue (bits ++ [false]) = binaryValue bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [List.cons_append, binaryValue, ih]

private theorem binaryValue_trim (bits : List Bool) :
    binaryValue (bits.dropWhile (fun bit => !bit)).reverse = binaryValue bits.reverse := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    cases bit
    · simpa only [List.dropWhile_cons, Bool.not_false, ite_true, List.reverse_cons,
        binaryValue_append_false] using ih
    · rfl

/-- Removing leading zeros gives the existing binary code for the counter's numeric value. -/
theorem trimCounterBits (bits : List Bool) :
    (bits.dropWhile (fun bit => !bit)).reverse =
      encodingNatBool.encode (binaryValue bits.reverse) :=
  canonical_injective _ _ (canonical_trim bits) (canonical_encode _) (by simp [binaryValue_trim])

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This template erases leading zero digits and stops at the counter's first remaining digit. -/
def normalizeCounter (tm : SingleTapeTM Γ) (zero : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (tape =ₜ some zero) do
    tape ←ₜ none
    moveₜ .Right

private theorem normalizeCounter_digits_spec (zero one : Γ) (hne : zero ≠ one)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let rest := bits.dropWhile (fun bit => !bit)
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      normalizeCounter tm zero
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (counterDigits zero one rest) tail⟩ ∧
        final.headPos = origin + bits.length - rest.length ∧
        cost.steps ≤ elapsed + bits.length - rest.length ⦄ := by
  dsimp only
  induction bits generalizing origin elapsed with
  | nil =>
    unfold normalizeCounter
    vcgen [Spec.while_false_spec]
    simp_all [counterDigits]
  | cons bit bits ih =>
    cases bit
    · have hlength := (List.dropWhile_sublist (l := bits) (fun bit : Bool => !bit)).length_le
      unfold normalizeCounter
      vcgen [Spec.while_step_spec (loop := normalizeCounter tm zero) (hloop := rfl),
        ih (origin + 1) (elapsed + 1)]
      all_goals
        cases bits
        all_goals simp_all [counterDigits, TMState.write, TMState.move, TMState.moveCost,
          BiTape.segment, BiTape.moveRight, BiTape.write]
        all_goals lia
    · unfold normalizeCounter
      vcgen [Spec.while_false_spec]
      all_goals simp_all [counterDigits, Ne.symm hne]

/--
Removing leading zeros leaves the existing binary encoding of the same number. It preserves
the following words and control state, and makes at most one head move per original digit.
-/
@[spec] theorem normalizeCounter_spec (zero one : Γ) (hne : zero ≠ one)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let value := binaryValue bits.reverse
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      normalizeCounter tm zero
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (counterWord zero one value) tail⟩ ∧
        final.headPos = origin + bits.length - value.size ∧
        cost.steps ≤ elapsed + bits.length ⦄ := by
  dsimp only
  have heq : counterDigits zero one (bits.dropWhile (fun bit => !bit)) =
      counterWord zero one (binaryValue bits.reverse) := by
    have h := congrArg List.reverse (trimCounterBits bits)
    simpa [counterDigits, counterWord] using congrArg
      (List.map (fun bit => if bit then one else zero)) h
  have hlength := congrArg List.length (trimCounterBits bits)
  vcgen [normalizeCounter_digits_spec (tm := tm) zero one hne bits tail label origin elapsed]
  all_goals simp_all
  all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
