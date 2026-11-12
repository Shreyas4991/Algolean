/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockIteration
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CounterVisits
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.RegionWriting
import Mathlib.Tactic.GCongr

/-!
# Counting a unary word into a binary counter

* `countBlocks` adds the number of repetitions of a fixed word to a binary counter farther left.
  Each repetition contributes one, even when the repeated word has several symbols.
* The source word and intervening words are preserved. The head returns to the source's first
  cell. The counter may grow left into blank cells.
* The source may itself be the part of a word before a temporarily erased cell. This allows
  a containing machine to recover a loop's current position without keeping another counter.

This is a machine template. The digit symbols, repeated word, and number of intervening words
are fixed independently of the numbers stored on the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def bumpCounter (zero one : Γ) (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  onCounter tm (incrementLeft tm zero one) count
  seekRightBlank tm

/--
This template adds the number of repetitions of `tick :: unitTail` to the binary counter.
It visits the counter once per repetition, preserves every other cell, and restores the head.
-/
def countBlocks (tm : SingleTapeTM Γ) (zero one tick : Γ) (unitTail : List Γ) (near : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  forBlocks tm tick unitTail (bumpCounter zero one near)

private theorem bumpCounter_spec (zero one : Γ) (hne : zero ≠ one)
    (value : Nat) (near : List (List Γ)) (before after : List Γ) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment
          (StackTape.prepend before.reverse (counterLeft (counterWord zero one value) near))
          [] (StackTape.prepend after (StackTape.cons none tail))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      bumpCounter (tm := tm) zero one near.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment
          (StackTape.prepend before.reverse (counterLeft (counterWord zero one (value + 1)) near))
          [] (StackTape.prepend after (StackTape.cons none tail))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * before.length +
          6 * value.size + (value + 1).size + 2 * (near.map List.length).sum +
            4 * near.length + 11 ⦄ := by
  let later := StackTape.prepend after (StackTape.cons none tail)
  have ha (position : ℤ) (steps : Nat) := incrementCounterWord_spec (tm := tm) zero one hne
    value (counterRight near before later) label position steps
  have hv := onCounter_spec (tm := tm) (incrementLeft tm zero one)
    (counterWord zero one value) (counterWord zero one (value + 1)) near before later later
    label label (4 * value.size + 5) (by simpa [counterWord, Nat.add_assoc] using ha)
    (origin - before.length) (elapsed + before.length + 2)
  vcgen [bumpCounter,
    seekLeftEnd_le_spec (tm := tm) ((counterLeft (counterWord zero one value) near).tail)
      later before.reverse [] label origin elapsed,
    hv,
    seekRightBlank_le_spec (tm := tm)
      (counterLeft (counterWord zero one (value + 1)) near) later before label
      (origin - before.length)
      (elapsed + before.length + 2 + (4 * value.size + 5) + value.size + (value + 1).size +
        2 * (near.map List.length).sum + 4 * near.length + 4)]
  all_goals
    simp_all [later, counterWord]
    all_goals lia

/-- This polynomial expression bounds all counter visits, increments, and source scans. -/
@[expose] def countBlocksMoves (unit start count distance : Nat) : Nat :=
  32 * (unit + 1) * (start + count + distance + 2) * (count + 1)

/--
Counting adds exactly `count` to the counter's initial value and preserves the rest of the
tape. The bound is quadratic in the source count, counter value, and intervening tape length.
-/
@[spec] theorem countBlocks_spec (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (unitTail : List Γ) (start count : Nat) (near : List (List Γ))
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft (counterWord zero one start) near)
          (unaryWord (tick :: unitTail) count) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      countBlocks tm zero one tick unitTail near.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (counterLeft (counterWord zero one (start + count)) near)
          (unaryWord (tick :: unitTail) count) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          countBlocksMoves (unitTail.length + 1) start count (regionSpan near) ⦄ := by
  let lefts (index : Nat) := (counterLeft (counterWord zero one (start + index)) near).tail
  let bound := 16 * (unitTail.length + 2) * (start + count + regionSpan near + 2)
  have ha : BlockAction tick unitTail count lefts (fun _ => tail) label
      (bumpCounter (tm := tm) zero one near.length) bound := by
    intro index rest hcount position steps
    have hv := bumpCounter_spec (tm := tm) zero one hne (start + index) near
      (unaryWord (tick :: unitTail) index)
      (unitTail ++ unaryWord (tick :: unitTail) rest) tail label position steps
    have hsize : (start + index).size ≤ start + count :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by lia)
    have hnext : (start + index + 1).size ≤ start + count + 1 :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by lia)
    have hprefix : index * (unitTail.length + 1) ≤ count * (unitTail.length + 1) :=
      Nat.mul_le_mul_right _ (by lia)
    have hwork : 2 * (unaryWord (tick :: unitTail) index).length +
        6 * (start + index).size + (start + index + 1).size +
        2 * (near.map List.length).sum + 4 * near.length + 11 ≤ bound := by
      have hlength : (unaryWord (tick :: unitTail) index).length ≤
          count * (unitTail.length + 1) := by
        simpa [unaryWord, List.length_flatten] using hprefix
      calc
        _ ≤ 2 * (count * (unitTail.length + 1)) + 6 * (start + count) +
            (start + count + 1) + 2 * (near.map List.length).sum + 4 * near.length + 11 := by
          gcongr
        _ ≤ bound := by
          dsimp [bound, regionSpan]
          ring_nf
          lia
    vcgen [hv]
    all_goals
      simp_all [lefts, bound, regionSpan]
      all_goals ring_nf at *
      all_goals lia
  vcgen [countBlocks, forBlocks_spec tick unitTail count lefts (fun _ => tail) label
    (bumpCounter (tm := tm) zero one near.length) bound ha origin elapsed]
  all_goals
    simp_all [lefts, countBlocksMoves, bound, regionSpan]
    all_goals ring_nf at *
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
