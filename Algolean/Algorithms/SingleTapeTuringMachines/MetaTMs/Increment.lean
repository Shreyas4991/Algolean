/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Copying
public import Mathlib.Data.Nat.Digits.Defs

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

open scoped TMQuery

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
  induction bits generalizing left s with
  | nil =>
    simp [carryRight, hs]
  | cons bit bits ih =>
    cases bit with
    | false =>
      simp [carryRight, hs]
    | true =>
      unfold carryRight
      apply runs_while_step (by simp [hs])
      have hw : Runs (FreeM.lift (.write (some false))) s (cursor left (false :: bits))
          s.headPos 0 := by simpa [hs] using write_correct s (some false)
      have hb : Runs (do FreeM.lift (.write (some false)); FreeM.lift (.move .Right)) s
          (cursor (false :: left) bits) (s.headPos + 1) 1 := by
        simpa using hw.seq (q := FreeM.lift (.move .Right))
          (second := cursor (false :: left) bits) (pos₂ := s.headPos + 1) (time₂ := 1) (by
            intro t ht hp
            simpa [TMState.move, ht, hp] using move_correct t .Right)
      have hr := hb.seq (q := carryRight tm) (time₂ := carryCount bits)
        (second := cursor (List.replicate (carryCount (true :: bits)) false ++ left)
          (carryTail (true :: bits))) (pos₂ := s.headPos + carryCount (true :: bits)) (by
          intro t ht hp
          have htape : t.config.BiTape = cursor (false :: left) bits := by simp [ht]
          convert ih (false :: left) t htape using 1 <;>
            simp [List.replicate_succ', List.append_assoc, hp, add_assoc]
          lia)
      simpa [carryRight, Nat.add_comm] using hr

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

/--
The increment program replaces the input with `incrementBits bits`, preserves the control state, and
restores the starting head coordinate. Its exact cost is `2 * carryCount bits + 2` head moves,
accounting for carry propagation and the return trip.
-/
theorem increment_correct (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (increment tm) s (cursor [] (incrementBits bits))
      s.headPos (2 * carryCount bits + 2) := by
  have hc : Runs (carryRight tm) s
      (cursor (List.replicate (carryCount bits) false) (carryTail bits))
      (s.headPos + carryCount bits) (carryCount bits) := by
    simpa using carryRight_correct [] bits s hs
  have h := hc.seq (q := do FreeM.lift (.write (some true)); seekLeftEnd tm)
    (second := cursor [] (incrementBits bits)) (pos₂ := s.headPos)
    (time₂ := carryCount bits + 2) (by
      intro t ht hp
      have hw : Runs (FreeM.lift (.write (some true))) t
          (cursor (List.replicate (carryCount bits) false) (true :: (carryTail bits).tail))
          (s.headPos + carryCount bits) 0 := by
        cases htail : carryTail bits <;>
          simpa [ht, hp, htail] using write_correct t (some true)
      simpa using hw.seq (q := seekLeftEnd tm) (second := cursor [] (incrementBits bits))
        (pos₂ := s.headPos) (time₂ := carryCount bits + 2) (by
          intro u hu hup
          have huTape : u.config.BiTape = cursor (List.replicate (carryCount bits) false)
              (true :: (carryTail bits).tail) := by simp [hu]
          simpa [hup, incrementBits_eq] using
            seekLeftEnd_correct (List.replicate (carryCount bits) false)
              (true :: (carryTail bits).tail) u huTape))
  simpa [increment, two_mul, Nat.add_assoc] using h

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

/-- Propagating the carry preserves both neighboring regions and uses one move per changed bit. -/
theorem carryLeft_correct (zero one : Γ) (hne : zero ≠ one)
    (left tail : StackTape Γ) (bits : List Bool) (s : TMState counter)
    (htape : s.config.BiTape =
      (BiTape.segment left (bits.map (fun bit => if bit then one else zero)) tail).mirror) :
    Runs (carryLeft counter zero one) s
      (BiTape.segment (StackTape.prepend (List.replicate (carryCount bits) zero) left)
        ((carryTail bits).map (fun bit => if bit then one else zero)) tail).mirror
      (s.headPos - carryCount bits) (carryCount bits) := by
  induction bits generalizing left s with
  | nil => simp [carryLeft, htape]
  | cons bit bits ih =>
    cases bit with
    | false => simp [carryLeft, htape, hne]
    | true =>
      unfold carryLeft
      apply runs_while_step (by simp [htape])
      have hb : Runs (do
          FreeM.lift (.write (some zero))
          FreeM.lift (.move .Left)) s
          (BiTape.segment (StackTape.cons (some zero) left)
            (bits.map (fun bit => if bit then one else zero)) tail).mirror
          (s.headPos - 1) 1 := by
        cases bits <;>
          simpa [htape, BiTape.segment, BiTape.mirror, BiTape.write, BiTape.moveLeft,
            sub_eq_add_neg] using (write_correct s (some zero)).append_move .Left
      have hr := hb.seq (q := carryLeft counter zero one)
        (second := (BiTape.segment
          (StackTape.prepend (List.replicate (carryCount (true :: bits)) zero) left)
          ((carryTail (true :: bits)).map (fun bit => if bit then one else zero)) tail).mirror)
        (pos₂ := s.headPos - carryCount (true :: bits)) (time₂ := carryCount bits) (by
          intro middle hmiddle hpos
          simpa [hpos, List.replicate_succ', StackTape.prepend_append, sub_eq_add_neg,
            Int.add_assoc, Int.add_comm, Int.add_left_comm] using
            ih (StackTape.cons (some zero) left) middle
              (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
      simpa [carryLeft, Nat.add_comm] using hr

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
  let digit := fun bit : Bool => if bit then one else zero
  let count := carryCount bits.reverse
  let higher := (carryTail bits.reverse).tail.map digit
  let output := (incrementBits bits.reverse).reverse.map digit
  have houtput : output.reverse = List.replicate count zero ++ one :: higher := by
    simp only [output, List.map_reverse, List.reverse_reverse]
    rw [← incrementBits_eq]
    simp [digit, count, higher]
  have hstart := (seekRightBlank_segment StackTape.nil (bits.map digit) tail s htape).append_move
    .Left
  have hc := hstart.seq (q := do
      carryLeft counter zero one
      FreeM.lift (.write (some one)))
    (second := BiTape.segment (StackTape.mapSome higher) (one :: List.replicate count zero) tail)
    (pos₂ := s.headPos + bits.length - 1 - count) (time₂ := count) (by
      intro middle hmiddle hpos
      have hmirror : middle.config.BiTape =
          (BiTape.segment (StackTape.cons none tail)
            (bits.reverse.map digit) StackTape.nil).mirror := by
        have ht := congrArg SingleTapeTM.Cfg.BiTape hmiddle
        cases hx : (bits.map digit).reverse <;>
          simpa [List.map_reverse, hx, BiTape.segment, BiTape.mirror, BiTape.moveLeft] using ht
      have hw := (carryLeft_correct zero one hne (StackTape.cons none tail) StackTape.nil
        bits.reverse middle hmirror).append_write (some one)
      rcases carryTail_shape bits.reverse with htail | ⟨rest, htail⟩ <;>
        simpa [digit, count, higher, htail, hpos, BiTape.segment, BiTape.mirror, BiTape.write,
          sub_eq_add_neg, add_assoc] using hw)
  have he := hc.seq (q := seekRightBlank counter)
    (second := BiTape.segment (StackTape.mapSome output.reverse) [] tail)
    (pos₂ := s.headPos + bits.length) (time₂ := count + 1) (by
      intro middle hmiddle hpos
      simpa [houtput, hpos, sub_eq_add_neg, add_assoc] using
        seekRightBlank_segment (StackTape.mapSome higher) (one :: List.replicate count zero) tail
          middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  have hr := he.seq (q := seekLeftEnd counter)
    (second := BiTape.segment StackTape.nil output tail)
    (pos₂ := s.headPos + bits.length - output.length) (time₂ := output.length + 2) (by
      intro middle hmiddle hpos
      simpa [hpos] using seekLeftEnd_segment StackTape.nil output.reverse [] tail middle
        (by simpa using congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  refine ⟨(bits.map digit).length + 1 + count + (count + 1) + (output.length + 2), ?_, ?_⟩
  · simpa [incrementLeft, bind_assoc, digit, output] using hr
  · have hc := carryCount_le_length bits.reverse
    have hl := length_incrementBits_le bits.reverse
    simp only [List.length_map, List.length_reverse] at *
    dsimp only [count, output] at *
    simp only [List.length_map, List.length_reverse] at *
    lia

end LeftCounter

end Algolean.Algorithms.SingleTapeTuringMachines
