/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting

/-!
# Counting an earlier unary word from a marked position

* `countEarlierAtMark` adds an earlier unary word's length to the binary counter at the far
  left. It preserves every source word, the output, and the marked head position.
* `countEarlierAtMark_spec` proves the resulting counter value and a quadratic move bound.

This is a machine template. The containing machine fixes its symbols and numbers of
intervening words. The count is read from the tape on each run.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This adds the earlier word's unary count to the binary counter and restores the head. -/
def countEarlierAtMark (tm : SingleTapeTM Γ) (zero one tick : Γ) (before between : Nat) :
    Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (onCounter tm (countBlocks tm zero one tick [] before) between)

/-- This counts the source scan, counter visits, and both crossings of the intervening words. -/
@[expose] def earlierCountMoves (start count : Nat) (before between : List (List Γ))
    (current : List Γ) : Nat :=
  countBlocksMoves 1 start count (regionSpan before) + 2 * count +
    2 * (between.map List.length).sum + 4 * between.length + 2 * current.length + 6

/-- Counting preserves the marked position and all words except the binary counter. -/
@[spec] theorem countEarlierAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (start count : Nat) (before between : List (List Γ)) (current : List Γ)
    (parts : List (List Γ)) (output : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let near := between ++ List.replicate count tick :: before
    ⦃ fun cost machineState => machineState.config = ⟨label,
          markedUnaryTape near current parts output (counterWord zero one start)⟩ ∧
        machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      countEarlierAtMark tm zero one tick before.length between.length
    ⦃ fun _ cost final => final.config = ⟨label,
          markedUnaryTape near current parts output (counterWord zero one (start + count))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          earlierCountMoves start count before between current ⦄ := by
  dsimp only
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let source := List.replicate count tick
  let left := counterLeft (counterWord zero one start) before
  let resultLeft := counterLeft (counterWord zero one (start + count)) before
  let countBound := countBlocksMoves 1 start count (regionSpan before)
  have ha (position : ℤ) (steps : Nat) := countBlocks_spec (tm := tm) zero one hne tick []
    start count before (counterRight between current tail) label position steps
  have hv := onEarlierWord_spec (tm := tm) (countBlocks tm zero one tick [] before.length)
    left.tail resultLeft.tail source between current tail tail label label countBound
    (by intro position steps; simpa [left, resultLeft, source, countBound] using ha position steps)
  have hp := onPrefixAtMark_spec (tm := tm)
    (onCounter tm (countBlocks tm zero one tick [] before.length) between.length)
    (counterLeft (counterWord zero one start) (between ++ source :: before))
    (counterLeft (counterWord zero one (start + count)) (between ++ source :: before))
    (by simp) current tail tail label label
    (countBound + 2 * source.length + 2 * (between.map List.length).sum +
      4 * between.length + 4)
    (by intro position steps; simpa [left, resultLeft, Nat.add_assoc] using hv position steps)
    origin elapsed
  have hcost : elapsed + 2 * current.length + 2 + (countBound + 2 * count +
      2 * (between.map List.length).sum + 4 * between.length + 4) =
        elapsed + earlierCountMoves start count before between current := by
    simp only [earlierCountMoves, countBound]
    ring
  simpa only [countEarlierAtMark, markedUnaryTape, tail, source, List.length_replicate,
    hcost] using hp

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- The counter visits and scans are bounded quadratically by the total displayed data length. -/
theorem earlierCountMoves_le (start count : Nat) (before between : List (List Γ))
    (current : List Γ) :
    earlierCountMoves start count before between current ≤
      128 * (start + count + regionSpan before + regionSpan between + current.length + 4) ^ 2 := by
  let size := start + count + regionSpan before + regionSpan between + current.length + 4
  have hp : countBlocksMoves 1 start count (regionSpan before) ≤ 64 * size ^ 2 := by
    dsimp [countBlocksMoves]
    calc
      _ ≤ 64 * size * size := by gcongr <;> dsimp [size] <;> lia
      _ = _ := by ring
  have hl : 2 * count + 2 * (between.map List.length).sum + 4 * between.length +
      2 * current.length + 6 ≤ 4 * size := by
    dsimp [size, regionSpan]
    lia
  have hs : size ≤ size ^ 2 := by simpa only [pow_two] using Nat.le_mul_self size
  dsimp [earlierCountMoves]
  dsimp only [size] at hp hl hs
  lia

end Algolean.Algorithms.SingleTapeTuringMachines
