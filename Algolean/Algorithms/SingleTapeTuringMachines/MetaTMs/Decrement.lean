/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Increment
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FiniteState

/-!
# Testing and decrementing binary counters

The counter uses two fixed symbols of the tape alphabet as zero and one. Its most significant
digit comes first, and blank cells separate it from neighboring words.

* `testZero` tests whether the counter represents zero and records the answer in one of two
  chosen control states. It preserves the tape, returns to the first counter cell, and uses
  exactly `2 * n + 2` head moves for a counter of length `n`, including an empty counter.
* `decrementLeft` subtracts one from a positive counter and returns to its first cell. It
  preserves the counter's length, its neighboring word, and the control state. Leading zeros
  may remain. It uses at most `4 * n + 4` head moves for a counter of length `n`.

The pure function `decrementBits` describes subtraction with the least significant digit first.
The machine proofs reverse the lists when relating this function to the tape.

These are machine templates. The containing machine fixes the alphabet, digit symbols, and
result states once, independently of the input and its length. Every input length uses the
same finite program.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/--
This pure function subtracts one from a positive number whose least significant digit comes
first. The length stays unchanged. Its value on a word representing zero is not subtraction.
-/
def decrementBits : List Bool → List Bool
  | [] => []
  | false :: bits => true :: decrementBits bits
  | true :: bits => false :: bits

/-- Subtracting one leaves the number of digits unchanged. -/
@[simp] theorem length_decrementBits (bits : List Bool) :
    (decrementBits bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [decrementBits, ih]

/-- On a positive input, the resulting digits represent exactly one less. -/
theorem binaryValue_decrementBits (bits : List Bool) (hpositive : 0 < binaryValue bits) :
    binaryValue (decrementBits bits) + 1 = binaryValue bits := by
  induction bits with
  | nil => simp at hpositive
  | cons bit bits ih =>
    cases bit with
    | false =>
      have hrest : 0 < binaryValue bits := by simpa using hpositive
      have := ih hrest
      simp [decrementBits]
      lia
    | true => simp [decrementBits, Nat.add_comm]

private theorem decrementBits_eq (bits : List Bool) (hpositive : 0 < binaryValue bits) :
    List.replicate (carryCount (bits.map Bool.not)) true ++
      false :: (carryTail (bits.map Bool.not)).tail.map Bool.not = decrementBits bits := by
  induction bits with
  | nil => simp at hpositive
  | cons bit bits ih =>
    cases bit with
    | false =>
      simpa [decrementBits, List.replicate_succ] using
        congrArg (List.cons true) (ih (by simpa using hpositive))
    | true => simp [decrementBits, Function.comp_def]

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private noncomputable def zeroTable (one : Γ) (zeroState positiveState : tm.State) :
    ScanTable tm where
  states := Fintype.elems.toList
  symbols := Fintype.elems.toList
  next label symbol := if label = positiveState ∨ symbol = one then positiveState else zeroState
  mem_states label := Finset.mem_toList.mpr (Fintype.complete label)
  mem_symbols symbol := Finset.mem_toList.mpr (Fintype.complete symbol)

private theorem zeroTable_absorbs (one : Γ) (zeroState positiveState : tm.State)
    (word : List Γ) : word.foldl (zeroTable one zeroState positiveState).next positiveState =
      positiveState := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => simpa [zeroTable] using ih

private theorem zeroTable_result (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (bits : List Bool) :
    (bits.map (fun bit => if bit then one else zero)).foldl
      (zeroTable one zeroState positiveState).next zeroState =
        if binaryValue bits = 0 then zeroState else positiveState := by
  induction bits with
  | nil => simp
  | cons bit bits ih =>
    cases bit with
    | false => simpa [zeroTable, hstates, hne] using ih
    | true =>
      simpa [zeroTable] using zeroTable_absorbs one zeroState positiveState
        (bits.map (fun bit => if bit then one else zero))

/--
This machine template tests whether a binary counter represents zero and restores the head.
It records the answer in one of two fixed control states and leaves every tape cell unchanged.
The containing machine fixes the digit meaning one and both result states once.
-/
noncomputable def testZero (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (one : Γ) (zeroState positiveState : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ zeroState
  scan (zeroTable one zeroState positiveState)
  seekLeftEnd tm

/-- Testing for zero preserves the tape, records the answer, and restores the head. -/
@[spec] theorem testZero_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      testZero tm one zeroState positiveState
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroState else positiveState),
          BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * bits.length + 2 ⦄ := by
  vcgen [testZero,
    scan_spec (zeroTable one zeroState positiveState) StackTape.nil tail
      (bits.map (fun bit => if bit then one else zero)) zeroState origin elapsed,
    seekLeftEnd_segment_spec StackTape.nil tail
      (bits.map (fun bit => if bit then one else zero)).reverse []
      (some ((bits.map (fun bit => if bit then one else zero)).foldl
        (zeroTable one zeroState positiveState).next zeroState))
      (origin + bits.length) (elapsed + bits.length)]
  all_goals simp_all [zeroTable_result zero one hne zeroState positiveState hstates,
    binaryValue_eq_zero_iff]
  all_goals lia

/--
Testing a counter preserves its digits and the neighboring word. It records whether the number
is zero, restores the first counter cell, and uses exactly twice its length plus two head moves.
This includes empty counters and counters with leading zeros.
-/
theorem testZero_correct (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (bits : List Bool) (tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment StackTape.nil
      (bits.map (fun bit => if bit then one else zero)) tail) :
    ∃ cost final, Completes (testZero tm one zeroState positiveState) s cost final ∧
      final.config = ⟨some (if binaryValue bits.reverse = 0 then zeroState else positiveState),
        s.config.BiTape⟩ ∧ final.headPos = s.headPos ∧ cost.steps = 2 * bits.length + 2 := by
  apply Spec.completes
  vcgen [testZero_spec zero one hne zeroState positiveState hstates bits tail
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template subtracts one from a positive binary counter and restores the head.
The containing machine fixes the two distinct digit symbols once for every input length.
The counter occupies a region with blank cells on both sides, and its right neighbor is preserved.
-/
def decrementLeft (tm : SingleTapeTM Γ) (zero one : Γ) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Left
  carryLeft tm one zero
  tape ←ₜ some zero
  seekRightBlank tm
  seekLeftEnd tm

/--
Subtraction uses the increment program with the two digit meanings exchanged.
For a positive counter, the digit count stays unchanged and the head returns to its start.
-/
@[spec] theorem decrementLeft_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (hpositive : 0 < binaryValue bits.reverse) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      decrementLeft tm zero one
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil
        ((decrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps =
          elapsed + 2 * bits.length + 2 * carryCount (bits.reverse.map Bool.not) + 4 ⦄ := by
  let digit := fun bit : Bool => if bit then one else zero
  let swapped := fun bit : Bool => if bit then zero else one
  have hdigit : (fun bit : Bool => if bit then zero else one) ∘ Bool.not =
      (fun bit => if bit then one else zero) := by
    funext bit
    cases bit <;> rfl
  have hconvert : (incrementBits (bits.reverse.map Bool.not)).map Bool.not =
      decrementBits bits.reverse := by
    rw [← incrementBits_eq, ← decrementBits_eq bits.reverse hpositive]
    simp
  have hlength : (incrementBits (bits.reverse.map Bool.not)).length = bits.length := by
    have h := congrArg List.length hconvert
    simpa using h
  have houtput : (incrementBits (bits.reverse.map Bool.not)).reverse.map swapped =
      (decrementBits bits.reverse).reverse.map digit := by
    have hfun : digit ∘ Bool.not = swapped := by
      funext bit
      cases bit <;> rfl
    rw [← hconvert]
    simp only [List.map_reverse, List.map_map, hfun]
  change ⦃ _ ⦄ incrementLeft tm one zero ⦃ _ ⦄
  vcgen [incrementLeft_spec one zero (Ne.symm hne) (bits.map Bool.not) tail label origin elapsed]
  all_goals simp_all [digit, swapped, List.map_reverse, List.map_map]
  all_goals lia

/--
On a positive input, subtraction preserves the counter's length, its neighboring word, and
the control state. It restores the first counter cell and uses at most four times the number
of digits plus four head moves.
-/
theorem decrementLeft_correct (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (hpositive : 0 < binaryValue bits.reverse) (tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment StackTape.nil
      (bits.map (fun bit => if bit then one else zero)) tail) :
    let output := (decrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)
    ∃ moves, Runs (decrementLeft tm zero one) s
      (BiTape.segment StackTape.nil output tail) s.headPos moves ∧
      moves ≤ 4 * bits.length + 4 := by
  have hcount := carryCount_le_length (bits.reverse.map Bool.not)
  apply Spec.runs_le
  vcgen [decrementLeft_spec zero one hne bits hpositive tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all
  all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
