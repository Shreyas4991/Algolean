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
open scoped TMQuery

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

/-- The fixed moves preserve the tape symbols and control state and have exactly the stated cost. -/
theorem moveCells_correct (direction : Dir) (count : Nat) (s : TMState tm) :
    let moveTape := match direction with
      | .Left => BiTape.moveLeft (Symbol := Γ)
      | .Right => BiTape.moveRight (Symbol := Γ)
      | .Stop => id
    Runs (moveCells tm direction count) s (moveTape^[count] s.config.BiTape)
      (s.headPos + count * direction.offset) count := by
  induction count generalizing s with
  | zero =>
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    cases s.config
    rfl
  | succ count ih =>
    have h := (ih (s.move direction)).prepend_move
    convert h using 1 <;>
      simp [moveCells, TMState.move, Function.iterate_succ_apply, Nat.cast_add,
        Nat.cast_one, add_mul, add_assoc, add_comm]
    cases direction <;> rfl

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

/--
The comparison reports exactly whether the chosen word is a prefix of the current region.
It preserves the whole tape, including neighboring regions, restores the head position, and
uses at most twice the comparison word's length in head moves.
-/
theorem checkPrefix_correct (yes no : tm.State) (expected word : List Γ)
    (left tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left word tail) :
    ∃ cost final, Completes (checkPrefix tm yes no expected) s cost final ∧
      final.config = {s.config with «state» := some (if expected <+: word then yes else no)} ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 2 * expected.length := by
  induction expected generalizing word left s with
  | nil =>
    exact ⟨0, {s with config.state := some yes}, completes_update s yes,
      by simp, rfl, by simp⟩
  | cons symbol rest ih =>
    cases word with
    | nil =>
      refine ⟨0, {s with config.state := some no}, ?_, by simp, rfl, by simp⟩
      unfold checkPrefix
      exact Completes.branch (by simpa [htape] using completes_update s no)
    | cons first word =>
      by_cases heq : first = symbol
      · subst first
        let moved := s.move .Right
        obtain ⟨cost, final, hc, hcfg, hpos, hb⟩ :=
          ih word (StackTape.cons (some symbol) left) moved
            (by simp [moved, TMState.move, htape])
        let returned := final.move .Left
        have hr := (completes_move s .Right).seq (hc.seq (completes_move final .Left))
        refine ⟨s.moveCost .Right + (cost + final.moveCost .Left), returned, ?_, ?_, ?_, ?_⟩
        · unfold checkPrefix
          apply Completes.branch
          simpa [htape, moved, returned] using hr
        · simp [returned, TMState.move, hcfg, moved, htape]
        · simp [returned, TMState.move, hpos, moved]
        · change 1 + (cost.steps + 1) ≤ 2 * (rest.length + 1)
          lia
      · refine ⟨0, {s with config.state := some no}, ?_, ?_, rfl, by simp⟩
        · unfold checkPrefix
          exact Completes.branch (by simpa [htape, heq] using completes_update s no)
        · simp [Ne.symm heq]

private def previousWord (tm : SingleTapeTM Γ) (found searching : tm.State)
    (word : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveCells tm .Left word.length
  checkPrefix tm found searching word

private theorem previousWord_correct (found searching : tm.State) (expected actual : List Γ)
    (hlen : actual.length = expected.length) (left tail : StackTape Γ) (suffix : List Γ)
    (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.prepend actual.reverse left) suffix tail) :
    ∃ cost final, Completes (previousWord tm found searching expected) s cost final ∧
      final.config = ⟨some (if expected = actual then found else searching),
        BiTape.segment left (actual ++ suffix) tail⟩ ∧
      final.headPos = s.headPos - expected.length ∧ cost.steps ≤ 3 * expected.length := by
  obtain ⟨cost, middle, hc, hm, hp, hb⟩ := moveCells_correct (tm := tm) .Left expected.length s
  have hmiddle : middle.config.BiTape = BiTape.segment left (actual ++ suffix) tail := by
    simp [hm, htape, ← hlen, BiTape.segment_moveLeft_iterate]
  obtain ⟨more, final, hr, hf, hh, hbound⟩ :=
    checkPrefix_correct found searching expected (actual ++ suffix) left tail middle hmiddle
  have hprefix : expected <+: actual ++ suffix ↔ expected = actual := by
    rw [List.prefix_iff_eq_take, ← hlen, List.take_left]
  refine ⟨cost + more, final, hc.seq hr, ?_, ?_, ?_⟩
  · simpa [hprefix, hmiddle] using hf
  · simpa [hp, sub_eq_add_neg] using hh
  · simp only [TMCost.add_steps, hb]
    lia

private def previousLoop (tm : SingleTapeTM Γ) (found searching : tm.State)
    (word : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ state =ₜ some found) do
    previousWord tm found searching word

private theorem previousLoop_correct (found searching : tm.State) (hne : found ≠ searching)
    (expected : List Γ) (blocks : List (List Γ))
    (hblocks : ∀ block ∈ blocks, block.length = expected.length ∧ block ≠ expected)
    (left tail : StackTape Γ) (suffix : List Γ) (s : TMState tm)
    (hstate : s.config.state = some searching)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.prepend (expected ++ blocks.flatten).reverse left) suffix tail) :
    ∃ cost final, Completes (previousLoop tm found searching expected) s cost final ∧
      final.config = ⟨some found, BiTape.segment left (expected ++ blocks.flatten ++ suffix) tail⟩ ∧
      final.headPos = s.headPos - expected.length * (blocks.length + 1) ∧
      cost.steps ≤ 3 * expected.length * (blocks.length + 1) := by
  induction blocks using List.reverseRecOn generalizing suffix s with
  | nil =>
    obtain ⟨cost, final, hc, hf, hh, hb⟩ := previousWord_correct found searching expected expected
      rfl left tail suffix s (by simpa using htape)
    refine ⟨cost + 0, final, Completes.while_step (by simp [hstate, hne.symm]) hc
      (completes_while_false _ _ final (by simp [hf])), by simpa using hf,
      by simpa using hh, by simpa using hb⟩
  | append_singleton blocks block ih =>
    have hblock := hblocks block (by simp)
    have hrest : ∀ word ∈ blocks, word.length = expected.length ∧ word ≠ expected :=
      fun word hw => hblocks word (by simp [hw])
    obtain ⟨cost, middle, hc, hm, hh, hb⟩ := previousWord_correct found searching expected block
      hblock.1 (StackTape.prepend (expected ++ blocks.flatten).reverse left) tail suffix s (by
        simpa [List.flatten_append, List.reverse_append, StackTape.prepend_append] using htape)
    obtain ⟨more, final, hr, hf, hfpos, hbound⟩ :=
      ih hrest (block ++ suffix) middle (by simp [hm, hblock.2.symm]) (by simp [hm])
    refine ⟨cost + more, final, Completes.while_step (by simp [hstate, hne.symm]) hc hr,
      ?_, ?_, ?_⟩
    · simpa [List.flatten_append, List.append_assoc] using hf
    · rw [hfpos, hh]
      simp only [List.length_append, List.length_singleton]
      push_cast
      ring
    · simp only [TMCost.add_steps, List.length_append, List.length_singleton]
      calc
        cost.steps + more.steps ≤
            3 * expected.length + 3 * expected.length * (blocks.length + 1) :=
          Nat.add_le_add hb hbound
        _ = _ := by ring

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
  let initial : TMState tm := {s with config.state := some searching}
  obtain ⟨cost, final, hc, hf, hh, hb⟩ := previousLoop_correct found searching hne expected
    blocks hblocks left tail suffix initial rfl (by simpa [initial] using htape)
  exact ⟨0 + cost, final, (completes_update s searching).seq hc, hf, hh, by simpa using hb⟩

end Algolean.Algorithms.SingleTapeTuringMachines
