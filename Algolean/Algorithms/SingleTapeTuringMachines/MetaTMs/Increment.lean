/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Copying
public import Mathlib.Data.Nat.Digits.Defs
public import Algolean.Models.SingleTapeTM.Alphabet.Encoding

/-!
# Adding one to a binary word

The Turing machine program `increment` adds one to a Boolean word whose least significant bit is
stored first. Here `false` represents zero, `true` represents one, and the empty word represents
zero. For example, `[true, true, false]` represents three and becomes `[false, false, true]`, which
represents four. Overflow adds a new most significant bit to the right of the existing word.

The machine changes each initial one bit to zero while moving right. It then writes one at the first
zero or blank and returns to the first cell. It preserves the control state and uses exactly twice
the number of initial one bits plus two head moves. The pure Lean functions in this file describe
the expected output, the carry length, and the numeric value used in the correctness proof.

`incrementLeft` stores the most significant bit first and adds a cell on the left on overflow.
It works over two chosen symbols of any fixed alphabet and preserves the region beyond the
blank on the right. This lets a counter grow away from an input stored to its right.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/--
`incrementBits bits` is a pure Lean function that describes the word obtained by adding one to a
binary number stored with its least significant bit first. It changes initial ones to zeros and the
next zero to one. If the carry reaches the end, it adds a final one; in particular, empty input
becomes `[true]`.
-/
@[simp] def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementBits bits

/--
`carryCount bits` is a pure Lean function that counts the consecutive `true` bits at the beginning
of `bits`. This is the number of cells the increment program crosses before reaching a zero or
blank.
-/
@[simp] def carryCount : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: bits => carryCount bits + 1

/--
`carryTail bits` is a pure Lean function that removes the consecutive `true` bits at the beginning
of `bits`. The returned suffix begins with `false`, or is empty if every input bit was `true`.
-/
@[simp] def carryTail : List Bool → List Bool
  | [] => []
  | false :: bits => false :: bits
  | true :: bits => carryTail bits

/--
`binaryValue bits` is a pure Lean function that reads a Boolean word as a natural number with the
least significant bit first, interpreting `false` as zero and `true` as one. The empty word has
value zero.
-/
@[simp] def binaryValue : List Bool → ℕ
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + 2 * binaryValue bits

/-- A binary word represents zero exactly when it has no one bits. -/
@[simp] theorem binaryValue_eq_zero_iff (bits : List Bool) :
    binaryValue bits = 0 ↔ true ∉ bits := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp [ih]

/-- Reading the binary digits agrees with Mathlib's positional number notation. -/
theorem binaryValue_eq_ofDigits (bits : List Bool) :
    binaryValue bits = Nat.ofDigits 2 (bits.map Bool.toNat) := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp [ih, Nat.ofDigits]

/--
The output specified by `incrementBits` represents exactly one more than the input. This also holds
for empty input and for an input whose carry extends the word.
-/
theorem binaryValue_incrementBits (bits : List Bool) :
    binaryValue (incrementBits bits) = binaryValue bits + 1 := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all <;> lia

private theorem incrementBits_encodePosNum (p : PosNum) :
    incrementBits (Computability.encodePosNum p) = Computability.encodePosNum p.succ := by
  induction p <;> simp_all [Computability.encodePosNum, PosNum.succ, incrementBits]

/-- Incrementing the chosen binary encoding gives the chosen encoding of the next number. -/
@[simp] theorem incrementBits_encodingNatBool (n : Nat) :
    incrementBits (Computability.encodingNatBool.encode n) =
      Computability.encodingNatBool.encode (n + 1) := by
  have h : (n + 1 : Num) = (n : Num).succ := by
    apply Num.toNat_injective
    simp [Num.succ_to_nat]
  change incrementBits (Computability.encodeNum (n : Num)) =
    Computability.encodeNum ((n + 1 : Nat) : Num)
  rw [Nat.cast_add, Nat.cast_one, h]
  cases (n : Num) <;> simp [Computability.encodeNum, Num.succ, Num.succ',
    incrementBits_encodePosNum, Computability.encodePosNum]

/--
Adding one preserves the input length or increases it by one. The incremented word therefore has at
most `bits.length + 1` symbols.
-/
theorem length_incrementBits_le (bits : List Bool) :
    (incrementBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all

/--
The initial run of one bits cannot be longer than the input word. Consequently, the rightward carry
phase crosses at most `bits.length` cells.
-/
theorem carryCount_le_length (bits : List Bool) : carryCount bits ≤ bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all

/--
The incremented word consists of zeros replacing the initial one bits, followed by a single one and
the untouched suffix after the first zero. When no zero occurs, that single one is the new most
significant bit.
-/
theorem incrementBits_eq (bits : List Bool) :
    List.replicate (carryCount bits) false ++ true :: (carryTail bits).tail =
      incrementBits bits := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all [List.replicate_succ]

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
`carryRight tm` is a Turing machine program that changes each consecutive `true` under the head to
`false` and moves right after each change. It stops on the first `false` or blank without changing
that stopping cell. The following write in `increment` resolves the carry at that cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def carryRight (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (tape =ₜ some true) do
    tape ←ₜ some false
    moveₜ .Right

/-- Carrying right changes the initial one bits to zero and counts exactly those moves. -/
@[spec] theorem carryRight_spec (left bits : List Bool) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left bits⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      carryRight tm
    ⦃ fun _ cost final => final.config =
        ⟨label, cursor (List.replicate (carryCount bits) false ++ left) (carryTail bits)⟩ ∧
        final.headPos = origin + carryCount bits ∧ cost.steps = elapsed + carryCount bits ⦄ := by
  induction bits generalizing left origin elapsed with
  | nil =>
    unfold carryRight
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit bits ih =>
    cases bit with
    | false =>
      unfold carryRight
      vcgen [Spec.while_false_spec]
      simp_all
    | true =>
      unfold carryRight
      vcgen [Spec.while_step_spec (loop := carryRight tm) (hloop := rfl),
        ih (false :: left) (origin + 1) (elapsed + 1)]
      all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
        List.replicate_succ', List.append_assoc, add_assoc]
      all_goals lia

/--
The carry phase changes exactly the initial `carryCount bits` one bits to zeros and leaves
`carryTail bits` under and to the right of the head. It preserves the existing prefix and control
state and uses exactly `carryCount bits` head moves.
-/
theorem carryRight_correct (left bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left bits) :
    Runs (carryRight tm) s
      (cursor (List.replicate (carryCount bits) false ++ left) (carryTail bits))
      (s.headPos + carryCount bits) (carryCount bits) := by
  apply Spec.runs
  vcgen [carryRight_spec left bits s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`increment tm` is a Turing machine program that adds one to the binary word beginning under the
head, with the least significant bit first. It clears the initial ones, writes one at the first zero
or blank, and returns to the starting cell. Empty input becomes `[true]`, and an input of all ones
gains a new bit at its right end.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def increment (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  carryRight tm
  tape ←ₜ some true
  seekLeftEnd tm

/-- Adding one restores the head and counts both the carry and the return trip. -/
@[spec] theorem increment_spec (bits : List Bool) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] bits⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      increment tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor [] (incrementBits bits)⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * carryCount bits + 2 ⦄ := by
  have houtput := incrementBits_eq bits
  vcgen [increment, carryRight_spec [] bits label origin elapsed,
    seekLeftEnd_spec (List.replicate (carryCount bits) false) (true :: (carryTail bits).tail)
      label (origin + carryCount bits) (elapsed + carryCount bits)]
  all_goals cases htail : carryTail bits
  all_goals simp_all [TMState.write]
  all_goals lia

/--
The increment program replaces the input with `incrementBits bits`, preserves the control state, and
restores the starting head coordinate. Its exact cost is `2 * carryCount bits + 2` head moves,
accounting for carry propagation and the return trip.
-/
theorem increment_correct (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (increment tm) s (cursor [] (incrementBits bits))
      s.headPos (2 * carryCount bits + 2) := by
  apply Spec.runs
  vcgen [increment_spec bits s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
Incrementing a word uses at most `2 * bits.length + 2` head moves and allocates at most that many
additional cells. The final allocation count includes the cells already recorded in the initial
state, even when the carry overflows the word.
-/
theorem increment_complexity (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    ∃ cost final, Completes (increment tm) s cost final ∧ cost.steps ≤ 2 * bits.length + 2 ∧
      cost.cellsAllocated ≤ 2 * bits.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * bits.length + 2) := by
  obtain ⟨cost, final, hc, ht, hspace, htotal⟩ := (increment_correct bits s hs).space
  have := carryCount_le_length bits
  exact ⟨cost, final, hc, by lia, by lia, by lia⟩

/-- The carry stops at a zero bit or reaches the end of the word. -/
theorem carryTail_shape (bits : List Bool) :
    carryTail bits = [] ∨ ∃ rest, carryTail bits = false :: rest := by
  induction bits with
  | nil => exact Or.inl rfl
  | cons bit bits ih => cases bit <;> simp_all

section LeftCounter

open Copying

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {counter : SingleTapeTM Γ} [DecidableEq counter.State]

/--
This machine template changes consecutive one bits to zero while moving left. It stops on
the first zero or blank. The containing machine fixes both digit symbols once for all inputs.
-/
def carryLeft (counter : SingleTapeTM Γ) (zero one : Γ) :
    Prog (TMQuery counter) Unit := do [TMQuery counter]
  whileₜ (tape =ₜ some one) do
    tape ←ₜ some zero
    moveₜ .Left

/-- Carrying left preserves the neighboring regions and uses one move per changed bit. -/
@[spec] theorem carryLeft_spec (zero one : Γ) (hne : zero ≠ one)
    (left tail : StackTape Γ) (bits : List Bool) (label : Option counter.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        (BiTape.segment left (bits.map (fun bit => if bit then one else zero)) tail).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      carryLeft counter zero one
    ⦃ fun _ cost final => final.config = ⟨label,
        (BiTape.segment (StackTape.prepend (List.replicate (carryCount bits) zero) left)
          ((carryTail bits).map (fun bit => if bit then one else zero)) tail).mirror⟩ ∧
        final.headPos = origin - carryCount bits ∧ cost.steps = elapsed + carryCount bits ⦄ := by
  induction bits generalizing left origin elapsed with
  | nil =>
    unfold carryLeft
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit bits ih =>
    cases bit with
    | false =>
      unfold carryLeft
      vcgen [Spec.while_false_spec]
      simp_all
    | true =>
      unfold carryLeft
      vcgen [Spec.while_step_spec (loop := carryLeft counter zero one) (hloop := rfl),
        ih (StackTape.cons (some zero) left) (origin - 1) (elapsed + 1)]
      all_goals cases bits
      all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
        BiTape.segment, BiTape.mirror, BiTape.write, BiTape.moveLeft,
        List.replicate_succ', StackTape.prepend_append, sub_eq_add_neg, add_assoc]
      all_goals lia

/-- Propagating the carry preserves both neighboring regions and uses one move per changed bit. -/
theorem carryLeft_correct (zero one : Γ) (hne : zero ≠ one)
    (left tail : StackTape Γ) (bits : List Bool) (s : TMState counter)
    (htape : s.config.BiTape =
      (BiTape.segment left (bits.map (fun bit => if bit then one else zero)) tail).mirror) :
    Runs (carryLeft counter zero one) s
      (BiTape.segment (StackTape.prepend (List.replicate (carryCount bits) zero) left)
        ((carryTail bits).map (fun bit => if bit then one else zero)) tail).mirror
      (s.headPos - carryCount bits) (carryCount bits) := by
  apply Spec.runs
  vcgen [carryLeft_spec zero one hne left tail bits s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template adds one to a binary word whose most significant bit comes first.
The containing machine fixes the two distinct digit symbols once for every input length.
It starts and finishes at the word's first cell. Overflow adds a cell on the left, where the
tape must be blank; the region beyond the blank on the right remains unchanged.
-/
def incrementLeft (counter : SingleTapeTM Γ) (zero one : Γ) :
    Prog (TMQuery counter) Unit := do [TMQuery counter]
  seekRightBlank counter
  moveₜ .Left
  carryLeft counter zero one
  tape ←ₜ some one
  seekRightBlank counter
  seekLeftEnd counter

/--
Incrementing a counter preserves its right neighbor and finishes on the first output digit.
The exact move count includes the scan, the carry, and both return scans.
-/
@[spec] theorem incrementLeft_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (tail : StackTape Γ) (label : Option counter.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      incrementLeft counter zero one
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil
        ((incrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)) tail⟩ ∧
        final.headPos = origin + bits.length - (incrementBits bits.reverse).length ∧
        cost.steps = elapsed + bits.length + 2 * carryCount bits.reverse +
          (incrementBits bits.reverse).length + 4 ⦄ := by
  let digit := fun bit : Bool => if bit then one else zero
  let count := carryCount bits.reverse
  let higher := (carryTail bits.reverse).tail.map digit
  let output := (incrementBits bits.reverse).reverse.map digit
  have houtput : output.reverse = List.replicate count zero ++ one :: higher := by
    simp only [output, List.map_reverse, List.reverse_reverse]
    rw [← incrementBits_eq]
    simp [digit, count, higher]
  have hlength : (incrementBits bits.reverse).length = count + higher.length + 1 := by
    have h := congrArg List.length houtput
    simpa [output, add_assoc] using h
  unfold incrementLeft
  iterate 3 rw [← bind_assoc]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨label, BiTape.segment (StackTape.mapSome higher) (one :: List.replicate count zero) tail⟩ ∧
    current.headPos = origin + bits.length - 1 - count ∧
    cost.steps = elapsed + bits.length + 1 + count)
  · vcgen [seekRightBlank_segment_spec StackTape.nil tail (bits.map digit)
        label origin elapsed,
      carryLeft_spec zero one hne (StackTape.cons none tail) StackTape.nil bits.reverse
        label (origin + bits.length - 1) (elapsed + bits.length + 1)]
    case vc1 => simp_all [digit]
    case vc2 =>
      cases hx : (bits.map digit).reverse
      all_goals simp_all [digit, List.map_reverse, TMState.move, TMState.moveCost,
        BiTape.segment, BiTape.mirror, BiTape.moveLeft]
      all_goals lia
    case vc3 =>
      rcases carryTail_shape bits.reverse with htail | ⟨rest, htail⟩
      all_goals simp_all [digit, count, higher, TMState.write,
        BiTape.segment, BiTape.mirror, BiTape.write]
  · intro _
    vcgen [seekRightBlank_segment_spec (StackTape.mapSome higher) tail
        (one :: List.replicate count zero) label
        (origin + bits.length - 1 - count) (elapsed + bits.length + 1 + count),
      seekLeftEnd_segment_spec StackTape.nil tail output.reverse []
        label (origin + bits.length) (elapsed + bits.length + 2 * count + 2)]
    all_goals simp_all [digit, count, output]
    all_goals lia

/--
Incrementing preserves the neighboring region and control state. The head finishes at the
first output bit, and the number of moves is at most four times the input length plus five.
-/
theorem incrementLeft_correct (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (tail : StackTape Γ) (s : TMState counter)
    (htape : s.config.BiTape = BiTape.segment StackTape.nil
      (bits.map (fun bit => if bit then one else zero)) tail) :
    let output := (incrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)
    ∃ moves, Runs (incrementLeft counter zero one) s
      (BiTape.segment StackTape.nil output tail)
      (s.headPos + bits.length - output.length) moves ∧ moves ≤ 4 * bits.length + 5 := by
  have hcount := carryCount_le_length bits.reverse
  have hlength := length_incrementBits_le bits.reverse
  apply Spec.runs_le
  vcgen [incrementLeft_spec zero one hne bits tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all
  all_goals lia

end LeftCounter

end Algolean.Algorithms.SingleTapeTuringMachines
