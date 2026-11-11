/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.While
public import Algolean.Models.SingleTapeTM.Tape

/-!
# Moving the head and recognizing fixed words

* `moveCells` repeats a chosen move instruction a fixed number of times. It preserves the tape
  and the control state.
* `checkPrefix` compares a chosen word with the cells beginning under the head and records the
  answer in the control state. It preserves the tape and restores the head position. A blank
  before the comparison ends gives a negative answer.
* `findPreviousWord` searches left in steps of the chosen word's length, testing each position.
  It stops at the start of a match, preserves the tape, and enters the chosen result state.
  A matching word must occur at one of the tested positions.

These are machine templates. Their parameters are fixed when constructing the containing
machine, independently of the input and its length. The same finite program runs on every
input length.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This machine template makes a fixed number of moves in the chosen direction. The containing
machine fixes both arguments independently of the input and its length.
-/
def moveCells (tm : SingleTapeTM Γ) (direction : Dir) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    moveₜ direction
    moveCells tm direction count

/-- Repeating the chosen direction preserves the tape symbols and records every move. -/
@[spec] theorem moveCells_spec (direction : Dir) (count : Nat) (view : BiTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      moveCells tm direction count
    ⦃ fun _ cost final => final.config = ⟨label,
        (match direction with
          | .Left => BiTape.moveLeft (Symbol := Γ)
          | .Right => BiTape.moveRight (Symbol := Γ)
          | .Stop => id)^[count] view⟩ ∧
        final.headPos = origin + count * direction.offset ∧ cost.steps = elapsed + count ⦄ := by
  induction count generalizing view origin elapsed with
  | zero =>
    vcgen [moveCells]
    simp_all
  | succ count ih =>
    vcgen [moveCells, ih ((match direction with
      | .Left => BiTape.moveLeft (Symbol := Γ)
      | .Right => BiTape.moveRight (Symbol := Γ)
      | .Stop => id) view) (origin + direction.offset) (elapsed + 1)]
    all_goals cases direction
    all_goals simp_all [TMState.move, TMState.moveCost,
      Function.iterate_succ_apply, add_assoc]
    all_goals lia

/-- The fixed moves preserve the tape symbols and control state and have exactly the stated cost. -/
theorem moveCells_correct (direction : Dir) (count : Nat) (s : TMState tm) :
    let moveTape := match direction with
      | .Left => BiTape.moveLeft (Symbol := Γ)
      | .Right => BiTape.moveRight (Symbol := Γ)
      | .Stop => id
    Runs (moveCells tm direction count) s (moveTape^[count] s.config.BiTape)
      (s.headPos + count * direction.offset) count := by
  apply Spec.runs
  vcgen [moveCells_spec direction count s.config.BiTape s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template compares a fixed word with the cells beginning under the head.
It restores the head position and enters `yes` on a match or `no` otherwise. The containing
machine fixes the comparison word and both states once for every input length.
-/
def checkPrefix (tm : SingleTapeTM Γ) (yes no : tm.State) :
    List Γ → Prog (TMQuery tm) Unit
  | [] => do [TMQuery tm]
    state ←ₜ yes
  | symbol :: rest => do [TMQuery tm]
    ifₜ tape =ₜ some symbol then
      moveₜ .Right
      checkPrefix tm yes no rest
      moveₜ .Left
    else
      state ←ₜ no

/-- The prefix test restores the head and records its answer and a bound on its moves. -/
@[spec] theorem checkPrefix_spec (yes no : tm.State) (expected word : List Γ)
    (left tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left word tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      checkPrefix tm yes no expected
    ⦃ fun _ cost final => final.config =
        ⟨some (if expected <+: word then yes else no), BiTape.segment left word tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * expected.length ⦄ := by
  induction expected generalizing word left label origin elapsed with
  | nil =>
    vcgen [checkPrefix]
    simp_all
  | cons symbol expected ih =>
    cases word with
    | nil =>
      vcgen [checkPrefix,
        ih [] (StackTape.cons (some symbol) left) label (origin + 1) (elapsed + 1)]
      all_goals simp_all
      all_goals lia
    | cons first word =>
      vcgen [checkPrefix,
        ih word (StackTape.cons (some symbol) left) label (origin + 1) (elapsed + 1)]
      all_goals simp_all [TMState.move, TMState.moveCost]
      all_goals lia

/--
The comparison reports exactly whether the chosen word is a prefix of the current region.
It preserves the whole tape, including neighboring regions, restores the head position, and
uses at most twice the comparison word's length in head moves.
-/
theorem checkPrefix_correct (yes no : tm.State) (expected word : List Γ)
    (left tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left word tail) :
    ∃ cost final, Completes (checkPrefix tm yes no expected) s cost final ∧
      final.config = ⟨some (if expected <+: word then yes else no), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 2 * expected.length := by
  apply Spec.completes
  vcgen [checkPrefix_spec yes no expected word left tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

private def previousWord (tm : SingleTapeTM Γ) (found searching : tm.State)
    (word : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveCells tm .Left word.length
  checkPrefix tm found searching word

private theorem previousWord_spec (found searching : tm.State) (expected actual : List Γ)
    (hlen : actual.length = expected.length) (left tail : StackTape Γ) (suffix : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (StackTape.prepend actual.reverse left) suffix tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      previousWord tm found searching expected
    ⦃ fun _ cost final => final.config =
        ⟨some (if expected = actual then found else searching),
          BiTape.segment left (actual ++ suffix) tail⟩ ∧
        final.headPos = origin - expected.length ∧
        cost.steps ≤ elapsed + 3 * expected.length ⦄ := by
  have hprefix : expected <+: actual ++ suffix ↔ expected = actual := by
    rw [List.prefix_iff_eq_take, ← hlen, List.take_left]
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  vcgen [previousWord,
    moveCells_spec .Left expected.length
      (BiTape.segment (StackTape.prepend actual.reverse left) suffix tail)
      label origin initial.steps,
    checkPrefix_spec found searching expected (actual ++ suffix) left tail label
      (origin - expected.length) (initial.steps + expected.length)]
  all_goals simp_all [← hlen, BiTape.segment_moveLeft_iterate, sub_eq_add_neg]
  all_goals lia

private def previousLoop (tm : SingleTapeTM Γ) (found searching : tm.State)
    (word : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ state =ₜ some found) do
    previousWord tm found searching word

private theorem previousLoop_found_spec (found searching : tm.State) (expected : List Γ)
    (view : BiTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some found, view⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      previousLoop tm found searching expected
    ⦃ fun _ cost final => final.config = ⟨some found, view⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed ⦄ := by
  unfold previousLoop
  vcgen [Spec.while_false_spec]
  simp_all

private theorem previousLoop_spec (found searching : tm.State) (hne : found ≠ searching)
    (expected : List Γ) (blocks : List (List Γ))
    (hblocks : ∀ block ∈ blocks, block.length = expected.length ∧ block ≠ expected)
    (left tail : StackTape Γ) (suffix : List Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some searching, BiTape.segment
        (StackTape.prepend (expected ++ blocks.flatten).reverse left) suffix tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      previousLoop tm found searching expected
    ⦃ fun _ cost final => final.config =
        ⟨some found, BiTape.segment left (expected ++ blocks.flatten ++ suffix) tail⟩ ∧
        final.headPos = origin - expected.length * (blocks.length + 1) ∧
        cost.steps ≤ elapsed + 3 * expected.length * (blocks.length + 1) ⦄ := by
  induction blocks using List.reverseRecOn generalizing suffix origin elapsed with
  | nil =>
    unfold previousLoop
    vcgen [Spec.while_step_spec (loop := previousLoop tm found searching expected) (hloop := rfl),
      previousWord_spec found searching expected expected rfl left tail suffix
        (some searching) origin elapsed,
      previousLoop_found_spec found searching expected
        (BiTape.segment left (expected ++ suffix) tail)
        (origin - expected.length) (elapsed + 3 * expected.length)]
    all_goals simp_all
  | append_singleton blocks block ih =>
    have hblock := hblocks block (by simp)
    have hrest : ∀ word ∈ blocks, word.length = expected.length ∧ word ≠ expected :=
      fun word hw => hblocks word (by simp [hw])
    unfold previousLoop
    vcgen [Spec.while_step_spec (loop := previousLoop tm found searching expected) (hloop := rfl),
      previousWord_spec found searching expected block hblock.1
        (StackTape.prepend (expected ++ blocks.flatten).reverse left) tail suffix
        (some searching) origin elapsed,
      ih hrest (block ++ suffix) (origin - expected.length) (elapsed + 3 * expected.length)]
    all_goals simp_all [List.flatten_append, List.reverse_append, StackTape.prepend_append,
      List.append_assoc]
    all_goals ring_nf at *
    all_goals lia

/--
This machine template searches left through words of a fixed length until it finds `expected`.
The head starts just after one of these words and finishes on the matched word's first cell.
The chosen word must occur at one of the tested positions.
It leaves every tape cell unchanged and records `found` in the control state. The containing
machine fixes the word and both control states once for all input lengths.
-/
def findPreviousWord (tm : SingleTapeTM Γ) (found searching : tm.State) (expected : List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ searching
  previousLoop tm found searching expected

/--
The search preserves the tape and stops at the first earlier match. Its move bound is three
times the word length times the number of tested words, including the match.
-/
@[spec] theorem findPreviousWord_spec (found searching : tm.State) (hne : found ≠ searching)
    (expected : List Γ) (blocks : List (List Γ))
    (hblocks : ∀ block ∈ blocks, block.length = expected.length ∧ block ≠ expected)
    (left tail : StackTape Γ) (suffix : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend (expected ++ blocks.flatten).reverse left) suffix tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      findPreviousWord tm found searching expected
    ⦃ fun _ cost final => final.config =
        ⟨some found, BiTape.segment left (expected ++ blocks.flatten ++ suffix) tail⟩ ∧
        final.headPos = origin - expected.length * (blocks.length + 1) ∧
        cost.steps ≤ elapsed + 3 * expected.length * (blocks.length + 1) ⦄ := by
  vcgen [findPreviousWord,
    previousLoop_spec found searching hne expected blocks hblocks left tail suffix origin elapsed]
  simp_all

/--
If the preceding words all have the comparison length and none matches, the search reaches the
displayed earlier occurrence and preserves the whole tape. It uses at most `3 * w * k` head
moves, where `w` is the comparison length and `k` counts the tested words, including the match.
-/
theorem findPreviousWord_correct (found searching : tm.State) (hne : found ≠ searching)
    (expected : List Γ) (blocks : List (List Γ))
    (hblocks : ∀ block ∈ blocks, block.length = expected.length ∧ block ≠ expected)
    (left tail : StackTape Γ) (suffix : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.prepend (expected ++ blocks.flatten).reverse left) suffix tail) :
    ∃ cost final, Completes (findPreviousWord tm found searching expected) s cost final ∧
      final.config = ⟨some found, BiTape.segment left (expected ++ blocks.flatten ++ suffix) tail⟩ ∧
      final.headPos = s.headPos - expected.length * (blocks.length + 1) ∧
      cost.steps ≤ 3 * expected.length * (blocks.length + 1) := by
  apply Spec.completes
  vcgen [findPreviousWord_spec found searching hne expected blocks hblocks left tail suffix
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.SingleTapeTuringMachines
