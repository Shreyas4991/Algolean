/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Tape

/-!
# Comparing the beginning of a tape region with a fixed word

`checkPrefix` tests whether the word beginning under the head starts with a chosen word.
It leaves every tape cell unchanged, returns to its starting position, and records its answer
in the control state. A blank before the comparison ends gives a negative answer.

This is a machine template instantiated within a containing Query program. The comparison
word and the two result states are fixed independently of the input and its length. This
lets a machine recognize fixed symbol encodings without adding symbols to its tape alphabet.
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
  | count + 1 => do
    FreeM.lift (.move direction)
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
  | [] => FreeM.lift (.update yes)
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

end Algolean.Algorithms.SingleTapeTuringMachines
