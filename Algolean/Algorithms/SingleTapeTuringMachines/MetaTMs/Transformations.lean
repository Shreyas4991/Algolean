/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BitOperations
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning

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

open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
`appendBit tm bit` is a Turing machine program that starts at the beginning of a Boolean block,
scans right to the first blank, and writes `bit` there. It then returns to the first cell of the
extended block. On empty input it writes a one-bit word at the starting cell and returns to that
cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
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
  obtain ⟨cost, middle, hc, ht, hp, hm⟩ := seekRightBlank_correct [] bits s hs
  obtain ⟨more, final, hr, hf, hpos, htime⟩ := seekLeftEnd_correct bits.reverse [bit]
    (middle.write (some bit)) (by simp [TMState.write, ht])
  apply Spec.runs
  vcgen [appendBit, Spec.steps hc 0, Spec.steps hr bits.length]
  all_goals simp_all [TMState.write, add_assoc, add_comm, add_left_comm, two_mul]

/--
`complementRight tm` is a Turing machine program that flips each occupied Boolean cell from the
current position to the right, moving right after every flip. It stops on the first blank, leaves
that blank unchanged, and does not return to its starting position.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
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
    unfold complementRight
    apply Spec.runs
    vcgen [Spec.while_false_spec]
    cases hcfg : s.config
    simp_all
  | cons bit right ih =>
    obtain ⟨first, flipped, hflip, hcfg, hhead, hfirst⟩ := flipBit_correct s
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih (bit.not :: left) (flipped.move .Right)
      (by simp [TMState.move, hcfg, hs])
    unfold complementRight
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := complementRight tm) (hloop := rfl),
      Spec.steps hflip 0, Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost,
      List.reverse_cons, List.append_assoc, add_comm, add_left_comm]

/--
`complementBlock tm` is a Turing machine program that starts at the first cell of a Boolean block,
negates every bit, and then returns the head to the beginning. An empty block remains empty, with
the head returning to its original blank cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
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
  obtain ⟨cost, middle, hc, ht, hp, hm⟩ := complementRight_correct [] bits s hs
  obtain ⟨more, final, hr, hf, hpos, htime⟩ := seekLeftEnd_correct
    (bits.map Bool.not).reverse [] middle
    (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht)
  apply Spec.runs
  vcgen [complementBlock, Spec.steps hc 0, Spec.steps hr bits.length]
  all_goals simp_all [add_assoc, add_comm, add_left_comm, two_mul]

end Algolean.Algorithms.SingleTapeTuringMachines
