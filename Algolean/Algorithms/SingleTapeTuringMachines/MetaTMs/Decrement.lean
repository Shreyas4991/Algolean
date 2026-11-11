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
open scoped TMQuery

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

private theorem carryTail_not_ne_nil (bits : List Bool) (hpositive : 0 < binaryValue bits) :
    carryTail (bits.map Bool.not) ≠ [] := by
  induction bits with
  | nil => simp at hpositive
  | cons bit bits ih =>
    cases bit with
    | false => exact ih (by simpa using hpositive)
    | true => simp

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
  let initial : TMState tm := {s with config.state := some zeroState}
  obtain ⟨cost, middle, hc, hm, hp, hb⟩ := scan_segment_correct
    (zeroTable one zeroState positiveState) StackTape.nil tail
      (bits.map (fun bit => if bit then one else zero)) zeroState initial
        (by simpa [initial] using htape) rfl
  obtain ⟨more, final, hr, hf, hh, ht⟩ := seekLeftEnd_segment StackTape.nil
    (bits.map (fun bit => if bit then one else zero)).reverse [] tail middle
      (by simp [hm])
  refine ⟨0 + (cost + more), final, (completes_update s zeroState).seq (hc.seq hr),
    ?_, ?_, ?_⟩
  · simp [hf, hm, htape, zeroTable_result zero one hne zeroState positiveState hstates]
  · simpa [hp, initial] using hh
  · simp only [TMCost.add_steps, TMCost.zero_steps, hb, ht, List.length_reverse,
      List.length_map, Nat.zero_add]
    lia

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
  let digit := fun bit : Bool => if bit then one else zero
  let swapped := fun bit : Bool => if bit then zero else one
  let count := carryCount (bits.reverse.map Bool.not)
  let higher := (carryTail (bits.reverse.map Bool.not)).tail.map swapped
  let output := (decrementBits bits.reverse).reverse.map digit
  have hswap (word : List Bool) : (word.map Bool.not).map swapped = word.map digit := by
    simp only [List.map_map]
    congr 1
    funext bit
    cases bit <;> rfl
  have houtput : output.reverse = List.replicate count one ++ zero :: higher := by
    simp only [output, List.map_reverse, List.reverse_reverse]
    have hfun : digit ∘ Bool.not = swapped := by
      funext bit
      cases bit <;> rfl
    have h := congrArg (List.map digit) (decrementBits_eq bits.reverse hpositive)
    simp only [List.map_append, List.map_replicate, List.map_cons, List.map_map, hfun] at h
    simpa [digit, count, higher] using h.symm
  obtain ⟨rest, hrest⟩ : ∃ rest,
      carryTail (bits.reverse.map Bool.not) = false :: rest := by
    rcases carryTail_shape (bits.reverse.map Bool.not) with he | ⟨rest, he⟩
    · exact False.elim (carryTail_not_ne_nil bits.reverse hpositive he)
    · exact ⟨rest, he⟩
  have hstart := (seekRightBlank_segment StackTape.nil (bits.map digit) tail s htape).append_move
    .Left
  have hc := hstart.seq (q := do
      carryLeft tm one zero
      FreeM.lift (.write (some zero)))
    (second := BiTape.segment (StackTape.mapSome higher) (zero :: List.replicate count one) tail)
    (pos₂ := s.headPos + bits.length - 1 - count) (time₂ := count) (by
      intro middle hmiddle hpos
      have hmirror : middle.config.BiTape =
          (BiTape.segment (StackTape.cons none tail)
            ((bits.reverse.map Bool.not).map swapped) StackTape.nil).mirror := by
        have ht := congrArg SingleTapeTM.Cfg.BiTape hmiddle
        cases hx : (bits.map digit).reverse <;>
          simpa [hswap, List.map_reverse, hx, BiTape.segment, BiTape.mirror,
            BiTape.moveLeft] using ht
      have hw := (carryLeft_correct one zero hne.symm (StackTape.cons none tail) StackTape.nil
        (bits.reverse.map Bool.not) middle hmirror).append_write (some zero)
      rw [hrest] at hw
      have hhigher : higher = rest.map swapped := by
        dsimp only [higher]
        rw [hrest]
        rfl
      rw [hhigher]
      simpa [digit, count, swapped, hpos, BiTape.segment, BiTape.mirror,
        BiTape.write, sub_eq_add_neg, add_assoc] using hw)
  have he := hc.seq (q := seekRightBlank tm)
    (second := BiTape.segment (StackTape.mapSome output.reverse) [] tail)
    (pos₂ := s.headPos + bits.length) (time₂ := count + 1) (by
      intro middle hmiddle hpos
      simpa [houtput, hpos, sub_eq_add_neg, add_assoc] using
        seekRightBlank_segment (StackTape.mapSome higher) (zero :: List.replicate count one)
          tail middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  have hr := he.seq (q := seekLeftEnd tm)
    (second := BiTape.segment StackTape.nil output tail)
    (pos₂ := s.headPos) (time₂ := output.length + 2) (by
      intro middle hmiddle hpos
      simpa [output, hpos] using seekLeftEnd_segment StackTape.nil output.reverse [] tail
        middle (by simpa using congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  refine ⟨(bits.map digit).length + 1 + count + (count + 1) + (output.length + 2), ?_, ?_⟩
  · simpa [decrementLeft, bind_assoc, output, digit] using hr
  · have := carryCount_le_length (bits.reverse.map Bool.not)
    simp only [List.length_map, List.length_reverse] at *
    dsimp only [count, output] at *
    simp only [List.length_map, List.length_reverse, length_decrementBits] at *
    lia

end Algolean.Algorithms.SingleTapeTuringMachines
