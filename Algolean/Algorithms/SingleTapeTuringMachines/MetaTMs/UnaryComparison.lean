/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.EarlierWords
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CounterComparison
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Expanding

/-!
# Comparing two unary words

* `equalBlocks` tests whether the current unary word and a chosen earlier unary word have the
  same length. Each word repeats one fixed symbol, and the answer is stored in the control state.
* `compareBlocksOffset` also tests whether either number is larger by one, using a fixed offset.
* Both words, every intervening word, and the head position are preserved. A temporary binary
  counter grows into blank cells farther left and is erased before the program returns.

These are machine templates. The offset, symbols, three control states, and numbers of
intervening words are fixed once. The two lengths being compared are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def initializeCounter (zero one : Γ) (offset : Nat) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  writeLeft tm (counterWord zero one offset).reverse
  moveₜ .Right

private theorem initializeCounter_spec (zero one : Γ) (offset : Nat)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      initializeCounter (tm := tm) zero one offset
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (counterWord zero one offset) tail⟩ ∧
        final.headPos = origin - offset.size ∧ cost.steps ≤ elapsed + offset.size + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  have hblank : (BiTape.segment (StackTape.nil : StackTape Γ) [] tail).moveLeft =
      BiTape.segment StackTape.nil [] (StackTape.cons none tail) := rfl
  vcgen [initializeCounter, writeLeft_spec (tm := tm) (counterWord zero one offset).reverse
    StackTape.nil (StackTape.cons none tail) label (origin - 1) (initial.steps + 1)]
  all_goals
    simp_all [TMState.move, TMState.moveCost, counterWord]
    all_goals lia

private noncomputable def compareBlocksUsing (zero one tick : Γ)
    (offset before between : Nat) (finish : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onCounter tm (initializeCounter zero one offset) (between + before + 1)
  onCounter tm (countBlocks tm zero one tick [] before) between
  finish

/--
This template compares two unary words with one fixed offset. It tests whether the earlier
number plus `offset` is one more than the current number. Offsets zero, one, and two test
whether the earlier number is larger by one, equal, or smaller by one, respectively.
The containing machine fixes the offset, symbols, states, and intervening-word counts once.
-/
noncomputable def compareBlocksOffset (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (different equal extra : tm.State)
    (offset before between : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  compareBlocksUsing zero one tick offset before between
    (compareCounterWithBlocks tm zero one tick different equal extra (between + before + 1))

/-- This template tests equality of the two unary lengths, using the fixed offset one. -/
noncomputable def equalBlocks (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (different equal extra : tm.State) (before between : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  compareBlocksOffset tm zero one tick different equal extra 1 before between

/-- These are the unary words and preserved data to the left of the current unary word. -/
@[expose] def comparisonLeft (zero one tick : Γ) (value earlier : Nat)
    (before between : List (List Γ)) : StackTape Γ :=
  counterLeft (counterWord zero one value) (between ++ List.replicate earlier tick :: before)

/-- This bounds comparison by the two unary lengths and the lengths of the preserved words. -/
@[expose] def equalBlocksMoves (first second before between : Nat) : Nat :=
  512 * (first + second + before + between + 4) ^ 2

/-- This bounds comparison with a fixed offset, including the temporary counter initialization. -/
@[expose] def compareBlocksOffsetMoves (first second before between offset : Nat) : Nat :=
  512 * (first + second + before + between + offset + 3) ^ 2

private theorem compareBlocksUsing_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (offset first second : Nat) (before between : List (List Γ)) (tail : StackTape Γ)
    (label : Option tm.State) (finish : Prog (TMQuery tm) Unit) (result : tm.State)
    (hfinish : ∀ (position : ℤ) (steps : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment (comparisonLeft zero one tick (offset + first) first before between)
            (List.replicate second tick) tail⟩ ∧
          current.headPos = position ∧ cost.steps ≤ steps ⦄
        finish
      ⦃ fun _ cost final => final.config = ⟨some result,
          BiTape.segment (comparisonLeft zero one tick 0 first before between)
            (List.replicate second tick) tail⟩ ∧
          final.headPos = position ∧ cost.steps ≤ steps +
            counterComparisonMoves (offset + first).size second
              (regionSpan (between ++ List.replicate first tick :: before)) ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareBlocksUsing zero one tick offset before.length between.length finish
    ⦃ fun _ cost final => final.config = ⟨some result,
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          compareBlocksOffsetMoves first second (regionSpan before)
            (regionSpan between) offset ⦄ := by
  let source := List.replicate first tick
  let current := List.replicate second tick
  let allNear := between ++ source :: before
  let counted := counterWord zero one (offset + first)
  let initializing :=
    2 * offset.size + 2 * (allNear.map List.length).sum + 4 * allNear.length + 6
  let counting := countBlocksMoves 1 offset first (regionSpan before)
  let crossed := 2 * first + 2 * (between.map List.length).sum + 4 * between.length + 4
  let comparing := counterComparisonMoves (offset + first).size second (regionSpan allNear)
  have hleft (value : Nat) := earlierLeft_counterLeft (counterWord zero one value)
    source before between
  have hi := onCounter_spec (tm := tm) (initializeCounter zero one offset) []
    (counterWord zero one offset) allNear current tail tail label label (offset.size + 2)
    (by
      intro position steps
      simpa [counterWord, Nat.add_assoc] using initializeCounter_spec (tm := tm)
        zero one offset (counterRight allNear current tail) label position steps)
    origin elapsed
  have hc (position : ℤ) (steps : Nat) := countBlocks_spec (tm := tm) zero one hne tick []
    offset first before (counterRight between current tail) label position steps
  have hv := onEarlierWord_spec (tm := tm) (countBlocks tm zero one tick [] before.length)
    (counterLeft (counterWord zero one offset) before).tail
    (counterLeft counted before).tail source between current tail tail label label counting
    (by simpa [source, counted, counting] using hc)
    origin (elapsed + initializing)
  have ht := hfinish origin (elapsed + initializing + counting + crossed)
  have htime : initializing + counting + crossed + comparing ≤
      compareBlocksOffsetMoves first second (regionSpan before) (regionSpan between) offset := by
    have ho : offset.size ≤ offset := Nat.size_le.mpr Nat.lt_two_pow_self
    have hd : (offset + first).size ≤ offset + first := Nat.size_le.mpr Nat.lt_two_pow_self
    have hmul := Nat.mul_le_mul_right second hd
    simp only [initializing, counting, crossed, comparing, allNear, source,
      countBlocksMoves, counterComparisonMoves, subtractBlocksMoves, regionSpan,
      List.map_append, List.map_cons, List.sum_append, List.sum_cons, List.length_replicate,
      List.length_append, List.length_cons, compareBlocksOffsetMoves]
    ring_nf at hmul ⊢
    lia
  simp only [allNear, List.length_append, List.length_cons, Nat.add_assoc] at hi ht
  simp only [counted, hleft] at hv
  simp only [compareBlocksUsing, Nat.add_assoc]
  vcgen [hi, hv, ht]
  all_goals
    clear hi hv ht hc hleft
    simp_all [comparisonLeft, initializing, counting, crossed, comparing,
      allNear, source, current, counterWord, Nat.add_assoc, Nat.add_comm]
    all_goals lia

/--
The result state records the stated comparison. Every original tape cell and the starting head
position are restored, and the temporary binary counter is erased.
-/
@[spec] theorem compareBlocksOffset_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra) (offset : Nat)
    (first second : Nat) (before between : List (List Γ)) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareBlocksOffset tm zero one tick different equal extra offset
        before.length between.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if first + offset = second + 1 then equal else different),
          BiTape.segment (comparisonLeft zero one tick 0 first before between)
            (List.replicate second tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          compareBlocksOffsetMoves first second (regionSpan before)
            (regionSpan between) offset ⦄ := by
  have hs := compareBlocksUsing_spec (tm := tm) zero one hne tick offset first second before
    between tail label
    (compareCounterWithBlocks tm zero one tick different equal extra
      (between.length + before.length + 1))
    (if first + offset = second + 1 then equal else different) (by
      intro position steps
      have ht := compareCounterWithBlocks_spec (tm := tm) zero one hne tick different equal extra
        hfirst hlast hother (encodingNatBool.encode (offset + first)).reverse second
        (between ++ List.replicate first tick :: before) tail label position steps
      simpa [comparisonLeft, counterDigits, counterWord, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using ht)
    origin elapsed
  vcgen [compareBlocksOffset, hs]

/-- Equality restores all source words and satisfies the same quadratic bound. -/
@[spec] theorem equalBlocks_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (first second : Nat) (before between : List (List Γ)) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      equalBlocks tm zero one tick different equal extra before.length between.length
    ⦃ fun _ cost final => final.config = ⟨some (if first = second then equal else different),
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          equalBlocksMoves first second (regionSpan before) (regionSpan between) ⦄ := by
  simpa [equalBlocks, equalBlocksMoves, compareBlocksOffsetMoves, Nat.add_assoc] using
    compareBlocksOffset_spec (tm := tm) zero one hne tick different equal extra hfirst hlast hother
      1 first second before between tail label origin elapsed


/--
This template tests whether an earlier unary count plus a fixed offset is at most the current
count. It preserves both words, their neighbors, and the head position, and clears its counter.
-/
noncomputable def compareBlocksLeOffset (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (greater atMost : tm.State) (offset before between : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  compareBlocksUsing zero one tick offset before between
    (compareCounterLeBlocks tm zero one tick greater atMost (between + before + 1))

/-- The result records whether the earlier number plus its offset is at most the current one. -/
@[spec] theorem compareBlocksLeOffset_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (greater atMost : tm.State) (hstates : greater ≠ atMost) (offset first second : Nat)
    (before between : List (List Γ)) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (comparisonLeft zero one tick 0 first before between)
          (List.replicate second tick) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareBlocksLeOffset tm zero one tick greater atMost offset before.length between.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if first + offset ≤ second then atMost else greater),
          BiTape.segment (comparisonLeft zero one tick 0 first before between)
            (List.replicate second tick) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          compareBlocksOffsetMoves first second (regionSpan before)
            (regionSpan between) offset ⦄ := by
  have hs := compareBlocksUsing_spec (tm := tm) zero one hne tick offset first second before
    between tail label
    (compareCounterLeBlocks tm zero one tick greater atMost (between.length + before.length + 1))
    (if first + offset ≤ second then atMost else greater) (by
      intro position steps
      have ht := compareCounterLeBlocks_spec (tm := tm) zero one hne tick greater atMost hstates
        (encodingNatBool.encode (offset + first)).reverse second
        (between ++ List.replicate first tick :: before) tail label position steps
      simpa [comparisonLeft, counterDigits, counterWord, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using ht)
    origin elapsed
  vcgen [compareBlocksLeOffset, hs]

end Algolean.Algorithms.SingleTapeTuringMachines
