/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnarySubtraction
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CounterOne
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Testing and clearing a binary counter

* `testOneAndClear` records whether a binary counter equals one, then erases the counter.
  It leaves the following tape unchanged and stops at the blank after the erased digits.
* `compareCounterWithBlocks` subtracts a unary count before testing. It records whether the
  original counter is larger than that count by one and then clears the counter.
* `testZeroAndClear` tests for zero and clears the counter.
* `compareCounterLeBlocks` records whether the counter is at most the unary count.
* Leading zeros are allowed, so these tests also work after subtraction.

These are machine templates. The containing machine fixes the digit symbols and result states
once. The counter's digits and length are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This tests whether the counter is one, erases its digits, and stops on the blank after them. -/
noncomputable def testOneAndClear (one : Γ)
    (different equal extra : tm.State) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  testOne tm one different equal extra
  ifₜ state =ₜ some equal then
    pure ()
  else
    state ←ₜ different
  eraseRight tm

/-- Testing and erasing a counter preserves the cells to its right and records the exact answer. -/
@[spec] theorem testOneAndClear_spec (zero one : Γ) (hne : zero ≠ one)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      testOneAndClear one different equal extra
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 1 then equal else different),
          BiTape.segment StackTape.nil [] tail⟩ ∧
        final.headPos = origin + bits.length ∧
        cost.steps ≤ elapsed + 3 * bits.length + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  by_cases hone : binaryValue bits.reverse = 1
  · vcgen [testOneAndClear, testOne_spec (tm := tm) zero one hne different equal extra hfirst
      hlast bits tail label origin initial.steps, Spec.branch_true_spec]
    case vc1 => simp_all [counterDigits]
    case vc2 =>
      refine ⟨by simp_all, ?_⟩
      dsimp only [binderNameHint]
      vcgen [eraseRight_segment_spec (tm := tm) StackTape.nil tail
        (counterDigits zero one bits) (some equal) origin (initial.steps + 2 * bits.length + 2)]
      all_goals
        simp_all [counterDigits]
        all_goals lia
  · vcgen [testOneAndClear, testOne_spec (tm := tm) zero one hne different equal extra hfirst
      hlast bits tail label origin initial.steps, Spec.branch_false_spec]
    case vc1 => simp_all [counterDigits]
    case vc2 =>
      refine ⟨by simp_all; split_ifs <;> simp_all [Ne.symm hother], ?_⟩
      dsimp only [binderNameHint]
      vcgen [eraseRight_segment_spec (tm := tm) StackTape.nil tail
        (counterDigits zero one bits) (some different) origin (initial.steps + 2 * bits.length + 2)]
      all_goals
        simp_all [counterDigits]
        all_goals lia


/--
This compares a binary counter with a unary word, records whether the counter is larger by
one, and clears the counter. The source word and head position are preserved. The containing
machine fixes the symbols, control states, and number of intervening words.
-/
noncomputable def compareCounterWithBlocks (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (different equal extra : tm.State) (near : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ different
  subtractBlocks tm zero one tick [] different equal different near
  onCounter tm (testOneAndClear one different equal extra) near

/-- This counts the subtraction and the final visit that tests and clears the counter. -/
@[expose] def counterComparisonMoves (digits count distance : Nat) : Nat :=
  subtractBlocksMoves 1 digits count distance + 4 * digits + 4 * distance + 6

/-- The result records whether the counter exceeds the unary count by exactly one. -/
@[spec] theorem compareCounterWithBlocks_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra) (bits : List Bool) (count : Nat)
    (near : List (List Γ)) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft (counterDigits zero one bits) near)
          (List.replicate count tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareCounterWithBlocks tm zero one tick different equal extra near.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = count + 1 then equal else different),
          BiTape.segment (counterLeft [] near) (List.replicate count tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          counterComparisonMoves bits.length count (regionSpan near) ⦄ := by
  let source := List.replicate count tick
  let subtracted := subtractDigits bits count
  let subtracting := subtractBlocksMoves 1 bits.length count (regionSpan near)
  have hs := subtractBlocks_spec (tm := tm) zero one hne tick [] different equal different
    hfirst bits count near tail origin elapsed
  have hf := onCounter_spec (tm := tm) (testOneAndClear one different equal extra)
    (counterDigits zero one subtracted) [] near source tail tail (some different)
    (some (if binaryValue bits.reverse = count + 1 then equal else different))
    (3 * bits.length + 2) (by
      intro position steps
      have heq : binaryValue subtracted.reverse = 1 ↔ binaryValue bits.reverse = count + 1 := by
        simp only [subtracted, subtractDigits_value]
        lia
      simpa [counterDigits, subtracted, heq, Nat.add_assoc] using
        testOneAndClear_spec (tm := tm) zero one hne different equal extra hfirst hlast hother
          subtracted (counterRight near source tail) (some different) position steps)
    origin (elapsed + subtracting)
  vcgen [compareCounterWithBlocks, hs, hf]
  all_goals
    clear hs hf
    simp_all [source, subtracted, subtracting, counterDigits, counterComparisonMoves, regionSpan]
    all_goals lia

/-- The comparison bound is quadratic in the counter length, unary count, and crossed tape. -/
theorem counterComparisonMoves_le (digits count distance : Nat) :
    counterComparisonMoves digits count distance ≤ 128 * (digits + count + distance + 4) ^ 2 := by
  dsimp [counterComparisonMoves, subtractBlocksMoves]
  ring_nf
  lia

/-- This tests whether a binary counter is zero and erases its digits afterward. -/
noncomputable def testZeroAndClear (one : Γ) (nonzero zero : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  testOne tm one zero nonzero nonzero
  eraseRight tm

/-- Testing for zero preserves the following tape and finishes just after the erased counter. -/
@[spec] theorem testZeroAndClear_spec (zero one : Γ) (hne : zero ≠ one)
    (nonzero zeroState : tm.State) (hstates : nonzero ≠ zeroState)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      testZeroAndClear one nonzero zeroState
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroState else nonzero),
          BiTape.segment StackTape.nil [] tail⟩ ∧
        final.headPos = origin + bits.length ∧
        cost.steps ≤ elapsed + 3 * bits.length + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  have ht := testOne_spec (tm := tm) zero one hne zeroState nonzero nonzero
    (Ne.symm hstates) (Ne.symm hstates) bits tail label origin initial.steps
  simp only [ite_self] at ht
  vcgen [testZeroAndClear, ht,
    eraseRight_segment_spec (tm := tm) StackTape.nil tail (counterDigits zero one bits)
      (some (if binaryValue bits.reverse = 0 then zeroState else nonzero)) origin
      (initial.steps + 2 * bits.length + 2)]
  all_goals
    by_cases hz : true ∈ bits
    all_goals simp_all [counterDigits]
    all_goals lia

/--
This tests whether a binary counter is at most a unary count and then clears the counter.
The containing machine fixes its symbols, answer states, and number of intervening words.
-/
noncomputable def compareCounterLeBlocks (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (greater atMost : tm.State) (near : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ greater
  subtractBlocks tm zero one tick [] greater atMost greater near
  onCounter tm (testZeroAndClear one greater atMost) near

/-- The comparison preserves the unary word and records whether the counter is at most it. -/
@[spec] theorem compareCounterLeBlocks_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (greater atMost : tm.State) (hstates : greater ≠ atMost) (bits : List Bool) (count : Nat)
    (near : List (List Γ)) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft (counterDigits zero one bits) near)
          (List.replicate count tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareCounterLeBlocks tm zero one tick greater atMost near.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse ≤ count then atMost else greater),
          BiTape.segment (counterLeft [] near) (List.replicate count tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          counterComparisonMoves bits.length count (regionSpan near) ⦄ := by
  let source := List.replicate count tick
  let subtracted := subtractDigits bits count
  let subtracting := subtractBlocksMoves 1 bits.length count (regionSpan near)
  have hs := subtractBlocks_spec (tm := tm) zero one hne tick [] greater atMost greater
    hstates bits count near tail origin elapsed
  have hf := onCounter_spec (tm := tm) (testZeroAndClear one greater atMost)
    (counterDigits zero one subtracted) [] near source tail tail (some greater)
    (some (if binaryValue bits.reverse ≤ count then atMost else greater))
    (3 * bits.length + 2) (by
      intro position steps
      have heq : binaryValue subtracted.reverse = 0 ↔ binaryValue bits.reverse ≤ count := by
        simp only [subtracted, subtractDigits_value, Nat.sub_eq_zero_iff_le]
      simpa [counterDigits, subtracted, heq, Nat.add_assoc] using
        testZeroAndClear_spec (tm := tm) zero one hne greater atMost hstates
          subtracted (counterRight near source tail) (some greater) position steps)
    origin (elapsed + subtracting)
  vcgen [compareCounterLeBlocks, hs, hf]
  all_goals
    clear hs hf
    simp_all [source, subtracted, subtracting, counterDigits, counterComparisonMoves, regionSpan]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
