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

/-- Appending a bit preserves the control label and returns to the first input cell. -/
@[spec] theorem appendBit_spec (bits : List Bool) (bit : Bool) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] bits⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendBit tm bit
    ⦃ fun _ cost final => final.config = ⟨label, cursor [] (bits ++ [bit])⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * bits.length + 2 ⦄ := by
  vcgen [appendBit, seekRightBlank_spec [] bits label origin elapsed,
    seekLeftEnd_spec bits.reverse [bit] label (origin + bits.length) (elapsed + bits.length)]
  all_goals simp_all [TMState.write]
  all_goals lia

/--
Appending `bit` transforms `bits` into `bits ++ [bit]` and returns the head to its original
coordinate. The program preserves the control state and uses exactly `2 * bits.length + 2` head
moves, including when `bits` is empty.
-/
theorem appendBit_correct (bits : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (appendBit tm bit) s (cursor [] (bits ++ [bit])) s.headPos (2 * bits.length + 2) := by
  apply Spec.runs
  vcgen [appendBit_spec bits bit s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

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

/-- Flipping the remaining bits preserves the preceding word and counts every move. -/
@[spec] theorem complementRight_spec (left right : List Bool) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      complementRight tm
    ⦃ fun _ cost final =>
        final.config = ⟨label, cursor ((right.map Bool.not).reverse ++ left) []⟩ ∧
        final.headPos = origin + right.length ∧ cost.steps = elapsed + right.length ⦄ := by
  induction right generalizing left origin elapsed with
  | nil =>
    unfold complementRight
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit right ih =>
    unfold complementRight
    vcgen [Spec.while_step_spec (loop := complementRight tm) (hloop := rfl), flipBit_spec,
      ih (bit.not :: left) (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
      List.reverse_cons, List.append_assoc, add_assoc]
    all_goals lia

/--
The rightward complementing scan negates every bit of `right` and preserves `left`. It stops on the
blank immediately after the suffix, at `s.headPos + right.length`, and uses exactly `right.length`
head moves.
-/
theorem complementRight_correct (left right : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (complementRight tm) s (cursor ((right.map Bool.not).reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  apply Spec.runs
  vcgen [complementRight_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

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

/-- Complementing the whole word restores the head and counts the return trip. -/
@[spec] theorem complementBlock_spec (bits : List Bool) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] bits⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      complementBlock tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor [] (bits.map Bool.not)⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * bits.length + 2 ⦄ := by
  vcgen [complementBlock, complementRight_spec [] bits label origin elapsed,
    seekLeftEnd_spec (bits.map Bool.not).reverse [] label
      (origin + bits.length) (elapsed + bits.length)]
  all_goals simp_all
  all_goals lia

/--
Complementing the block replaces `bits` with `bits.map Bool.not` and restores the original head
coordinate. It preserves the control state and uses exactly `2 * bits.length + 2` head moves.
-/
theorem complementBlock_correct (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (complementBlock tm) s (cursor [] (bits.map Bool.not))
      s.headPos (2 * bits.length + 2) := by
  apply Spec.runs
  vcgen [complementBlock_spec bits s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.SingleTapeTuringMachines
