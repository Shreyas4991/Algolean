/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BitOperations
public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning

/-!
# Appending a bit and complementing a block

These Turing machine programs transform a contiguous Boolean word on an otherwise blank tape.
`appendBit` scans to its right boundary, writes a chosen bit, and returns to the first cell.
`complementRight` flips each bit from the current cell to the right boundary and stops on the
following blank. `complementBlock` also returns the head to the beginning after flipping.

The full-block programs expect the head at the beginning of the input and restore that coordinate
when they finish. Both work on empty input and use exactly `2 * bits.length + 2` head moves. Their
correctness theorems also prove that they preserve the control state.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
`appendBit tm bit` is a Turing machine program that starts at the beginning of a Boolean block,
scans right to the first blank, and writes `bit` there. It then returns to the first cell of the
extended block. On empty input it writes a one-bit word at the starting cell and returns to that
cell.
-/
def appendBit (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  tape ←ₜ some bit
  seekLeftEnd tm

/--
Appending `bit` transforms `bits` into `bits ++ [bit]` and returns the head to its original
coordinate. The program preserves the control state and uses exactly `2 * bits.length + 2` head
moves, including when `bits` is empty.
-/
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

/--
`complementRight tm` is a Turing machine program that flips each occupied Boolean cell from the
current position to the right, moving right after every flip. It stops on the first blank, leaves
that blank unchanged, and does not return to its starting position.
-/
def complementRight (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    flipBit tm
    moveₜ .Right

/--
The rightward complementing scan negates every bit of `right` and preserves `left`. It stops on the
blank immediately after the suffix, at `s.headPos + right.length`, and uses exactly `right.length`
head moves.
-/
theorem complementRight_correct (left right : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (complementRight tm) s (cursor ((right.map Bool.not).reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil =>
    simp [complementRight, hs]
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

/--
`complementBlock tm` is a Turing machine program that starts at the first cell of a Boolean block,
negates every bit, and then returns the head to the beginning. An empty block remains empty, with
the head returning to its original blank cell.
-/
def complementBlock (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  complementRight tm
  seekLeftEnd tm

/--
Complementing the block replaces `bits` with `bits.map Bool.not` and restores the original head
coordinate. It preserves the control state and uses exactly `2 * bits.length + 2` head moves.
-/
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
