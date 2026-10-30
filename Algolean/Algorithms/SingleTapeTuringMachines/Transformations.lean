/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BitOperations
public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning

/-! # Appending and complementing Boolean blocks -/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Append a fixed bit and return to the first bit of the resulting block. -/
def appendBit (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  tape ←ₜ some bit
  seekLeftEnd tm

/-- Appending preserves the original block, adds one bit, and returns the head to its origin. -/
theorem appendBit_correct (bits : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (appendBit tm bit) s (cursor [] (bits ++ [bit])) s.headPos (2 * bits.length + 2) := by
  have hr : Runs (seekRightBlank tm) s (cursor bits.reverse [])
      (s.headPos + bits.length) bits.length := by
    simpa using seekRightBlank_correct [] bits s hs
  have h := hr.seq (q := do FreeM.lift (.write (some bit)); seekLeftEnd tm)
    (second := cursor [] (bits ++ [bit])) (pos₂ := s.headPos) (time₂ := bits.length + 2) (by
      intro t ht hp
      have hw : Runs (FreeM.lift (.write (some bit))) t (cursor bits.reverse [bit])
          (s.headPos + bits.length) 0 := by simpa [ht, hp] using write_correct t (some bit)
      simpa using hw.seq (q := seekLeftEnd tm) (second := cursor [] (bits ++ [bit]))
        (pos₂ := s.headPos) (time₂ := bits.length + 2) (by
          intro u hu hup
          have huTape : u.config.BiTape = cursor bits.reverse [bit] := by simp [hu]
          simpa [hup] using seekLeftEnd_correct bits.reverse [bit] u huTape))
  simpa [appendBit, two_mul, Nat.add_assoc] using h

/-- Flip all bits from the head through the right end, stopping on the first blank. -/
def complementRight (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    flipBit tm
    moveₜ .Right

/-- The complementing scan changes only the suffix and moves once for each bit. -/
theorem complementRight_correct (left right : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (complementRight tm) s (cursor ((right.map Bool.not).reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil =>
    simpa [complementRight, hs] using runs_while_false (tm := tm) (.not (.tapeIs none))
      (do flipBit tm; FreeM.lift (.move .Right)) s (by simp [hs])
  | cons bit right ih =>
    unfold complementRight
    apply runs_while_step (by simp [hs])
    have hf : Runs (flipBit tm) s (cursor left (bit.not :: right)) s.headPos 0 := by
      simpa [hs] using flipBit_correct s
    have hb : Runs (do flipBit tm; FreeM.lift (.move .Right)) s
        (cursor (bit.not :: left) right) (s.headPos + 1) 1 := by
      simpa using hf.seq (q := FreeM.lift (.move .Right))
        (second := cursor (bit.not :: left) right) (pos₂ := s.headPos + 1) (time₂ := 1) (by
          intro t ht hp
          simpa [TMState.move, ht, hp] using move_correct t .Right)
    have hr := hb.seq (q := complementRight tm) (time₂ := right.length)
      (second := cursor (((bit :: right).map Bool.not).reverse ++ left) [])
      (pos₂ := s.headPos + (bit :: right).length) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor (bit.not :: left) right := by simp [ht]
        simpa [List.reverse_cons, List.append_assoc, hp, add_assoc, add_comm, add_left_comm] using
          ih (bit.not :: left) t htape)
    simpa [complementRight, Nat.add_comm] using hr

/-- Complement the entire block and return to its first bit. -/
def complementBlock (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  complementRight tm
  seekLeftEnd tm

/-- Block complementation has exact linear time and preserves the head origin and control state. -/
theorem complementBlock_correct (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (complementBlock tm) s (cursor [] (bits.map Bool.not))
      s.headPos (2 * bits.length + 2) := by
  have hr : Runs (complementRight tm) s (cursor (bits.map Bool.not).reverse [])
      (s.headPos + bits.length) bits.length := by
    simpa using complementRight_correct [] bits s hs
  have h := hr.seq (q := seekLeftEnd tm) (second := cursor [] (bits.map Bool.not))
    (pos₂ := s.headPos) (time₂ := bits.length + 2) (by
      intro t ht hp
      have htape : t.config.BiTape = cursor (bits.map Bool.not).reverse [] := by simp [ht]
      simpa [hp] using seekLeftEnd_correct (bits.map Bool.not).reverse [] t htape)
  simpa [complementBlock, two_mul, Nat.add_assoc] using h

end Algolean.Algorithms.SingleTapeTuringMachines
