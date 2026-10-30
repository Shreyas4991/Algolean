/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BitOperations
public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning

/-!
# Binary increment on a Boolean tape

Bits are least-significant first. The empty word represents zero. Overflow appends a new
most-significant bit. The procedure returns to the first bit and preserves the control state.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

/-- Pure specification of increment in least-significant-first representation. -/
@[simp] def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementBits bits

/-- Number of initially consecutive one bits crossed by the carry. -/
@[simp] def carryCount : List Bool → ℕ
  | [] => 0
  | false :: _ => 0
  | true :: bits => carryCount bits + 1

/-- Suffix remaining after all initially consecutive one bits. -/
@[simp] def carryTail : List Bool → List Bool
  | [] => []
  | false :: bits => false :: bits
  | true :: bits => carryTail bits

/-- Numeric interpretation of a least-significant-first Boolean word. -/
@[simp] def binaryValue : List Bool → ℕ
  | [] => 0
  | bit :: bits => (if bit then 1 else 0) + 2 * binaryValue bits

/-- The pure specification increments the represented natural number, including overflow. -/
theorem binaryValue_incrementBits (bits : List Bool) :
    binaryValue (incrementBits bits) = binaryValue bits + 1 := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all <;> lia

/-- Increment extends the word by at most one bit. -/
theorem length_incrementBits_le (bits : List Bool) :
    (incrementBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all

/-- A carry crosses no more than the number of input bits. -/
theorem carryCount_le_length (bits : List Bool) : carryCount bits ≤ bits.length := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all

/-- The zeroed carry prefix followed by the final one is exactly the incremented word. -/
theorem incrementBits_eq (bits : List Bool) :
    List.replicate (carryCount bits) false ++ true :: (carryTail bits).tail =
      incrementBits bits := by
  induction bits with
  | nil => simp
  | cons bit bits ih => cases bit <;> simp_all [List.replicate_succ]

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Propagate a carry across one bits, zeroing each bit crossed. -/
def carryRight (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (tape =ₜ some true) do
    tape ←ₜ some false
    moveₜ .Right

/-- The carry loop's exact state and cost, valid with any prefix and visited-cell history. -/
theorem carryRight_correct (left bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left bits) :
    Runs (carryRight tm) s
      (cursor (List.replicate (carryCount bits) false ++ left) (carryTail bits))
      (s.headPos + carryCount bits) (carryCount bits) := by
  induction bits generalizing left s with
  | nil =>
    simpa [carryRight, hs] using runs_while_false (tm := tm) (.tapeIs (some true))
      (do FreeM.lift (.write (some false)); FreeM.lift (.move .Right)) s (by simp [hs])
  | cons bit bits ih =>
    cases bit with
    | false =>
      simpa [carryRight, hs] using runs_while_false (tm := tm) (.tapeIs (some true))
        (do FreeM.lift (.write (some false)); FreeM.lift (.move .Right)) s (by simp [hs])
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

/-- Increment the input word and return to its first bit. -/
def increment (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  carryRight tm
  tape ←ₜ some true
  seekLeftEnd tm

/-- Increment has the specified tape output and an exact carry-dependent head-move count. -/
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
        simpa [ht, hp, cursor_write_any] using write_correct t (some true)
      simpa using hw.seq (q := seekLeftEnd tm) (second := cursor [] (incrementBits bits))
        (pos₂ := s.headPos) (time₂ := carryCount bits + 2) (by
          intro u hu hup
          have huTape : u.config.BiTape = cursor (List.replicate (carryCount bits) false)
              (true :: (carryTail bits).tail) := by simp [hu]
          simpa [hup, incrementBits_eq] using
            seekLeftEnd_correct (List.replicate (carryCount bits) false)
              (true :: (carryTail bits).tail) u huTape))
  simpa [increment, two_mul, Nat.add_assoc] using h

/-- Increment uses linear time and additional space, even on an all-ones input. -/
theorem increment_complexity (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    ∃ cost final, Completes (increment tm) s cost final ∧ cost.steps ≤ 2 * bits.length + 2 ∧
      cost.cellsVisited ≤ 2 * bits.length + 2 ∧
      final.cellsVisited.card ≤ s.cellsVisited.card + (2 * bits.length + 2) := by
  obtain ⟨cost, final, hc, ht, hspace, htotal⟩ := (increment_correct bits s hs).space
  have := carryCount_le_length bits
  exact ⟨cost, final, hc, by lia, by lia, by lia⟩

end Algolean.Algorithms.SingleTapeTuringMachines
