/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Tape

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning

/-!
# Erasing tape cells

* `eraseAndMove` erases the current cell and moves one cell to the right.
* `eraseRight` erases occupied cells while moving right and stops on the first blank. It preserves
  the tape beyond that blank and makes one head move for each erased cell.
* `eraseUntil` erases cells while moving right until it reaches a chosen symbol. It leaves that
  symbol and everything after it unchanged.
* `eraseLeft` erases occupied cells while moving left and stops on the first blank.
* `eraseToLeft` starts on the blank after a block, erases the block, and finishes where its first
  symbol used to be.
* `eraseBlock` clears the input and restores the head to its starting position. For an input of
  length `n`, including empty input, it uses exactly `2 * n + 2` head moves.

These are machine templates. The containing machine fixes their parameters once, independently
of the input and its length. Erasing a symbol leaves its cell in the recorded tape history, so
previously allocated space remains recorded after erasure.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type}

/-- Moving left on a completely blank tape leaves it blank. -/
private theorem nil_moveLeft : (BiTape.nil : BiTape Symbol).moveLeft = BiTape.nil := rfl

/-- Moving right on a completely blank tape leaves it blank. -/
private theorem nil_moveRight : (BiTape.nil : BiTape Symbol).moveRight = BiTape.nil := rfl

attribute [local simp] nil_moveLeft nil_moveRight

variable [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This Turing machine program erases the current cell and moves right. If all cells to its left
are blank, the remaining word then begins under the head.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseAndMove (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right

/-- Erasing and moving establishes the condition stated for the resulting machine state. -/
@[spec] theorem eraseAndMove_spec (post : Unit → TMCost → TMState tm → Prop) :
    ⦃ fun cost current => post () (cost + current.moveCost .Right)
        ((current.write none).move .Right) ⦄
      eraseAndMove tm ⦃ post ⦄ := by
  vcgen [eraseAndMove]
  rename_i initial current h
  have hcost : (current.write none).moveCost .Right = current.moveCost .Right := rfl
  rw [hcost]
  exact h

/-- Erasing the first symbol and moving right leaves exactly the remaining word on the tape. -/
theorem eraseAndMove_correct (symbol : Symbol) (rest : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] (symbol :: rest)) :
    Runs (eraseAndMove tm) s (cursor [] rest) (s.headPos + 1) 1 := by
  apply Spec.runs
  vcgen [eraseAndMove_spec]
  all_goals
    cases hcfg : s.config
    simp_all [TMState.move, TMState.write, TMState.moveCost, cursor, BiTape.write, BiTape.moveRight]

/--
This Turing machine program erases symbols while moving right and stops on the first blank.
When started at the first symbol of a word on an otherwise blank tape, it clears the whole tape.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseRight (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    eraseAndMove tm

/-- Erasing a region preserves its neighbors and leaves one blank for each removed symbol. -/
@[spec] theorem eraseRight_segment_spec (left tail : StackTape Symbol) (word : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left word tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseRight tm
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.blanks word.length left) [] tail⟩ ∧
        final.headPos = origin + word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  induction word generalizing left origin elapsed with
  | nil =>
    unfold eraseRight
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol rest ih =>
    unfold eraseRight
    vcgen [Spec.while_step_spec (loop := eraseRight tm) (hloop := rfl), eraseAndMove_spec,
      ih (StackTape.cons none left) (origin + 1) (elapsed + 1)]
    all_goals cases rest
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      BiTape.segment, BiTape.write, BiTape.moveRight, add_assoc]
    all_goals lia

/-- Erasing the first word preserves the following region and counts every head move. -/
@[spec] theorem eraseRight_spec (word : List Symbol) (tail : StackTape Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil word tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseRight tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil [] tail⟩ ∧
        final.headPos = origin + word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  vcgen [eraseRight_segment_spec StackTape.nil tail word label origin elapsed]
  all_goals simp_all

/--
Erasing the first word preserves the tape beyond its following blank and stops on that blank.
The number of head moves equals the erased word's length.
-/
theorem eraseRight_segment (word : List Symbol) (tail : StackTape Symbol) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment StackTape.nil word tail) :
    Runs (eraseRight tm) s (BiTape.segment StackTape.nil [] tail)
      (s.headPos + word.length) word.length := by
  apply Spec.runs
  vcgen [eraseRight_spec word tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all 

/-- Erasing a word to the right clears the tape and uses one head move for each input symbol. -/
theorem eraseRight_correct (word : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] word) :
    Runs (eraseRight tm) s BiTape.nil (s.headPos + word.length) word.length := by
  simpa [BiTape.segment, BiTape.nil] using eraseRight_segment word StackTape.nil s
    (by cases word <;> simpa [cursor, BiTape.segment] using htape)

/--
This Turing machine program erases cells while moving right until it reaches `ending`.
It leaves that symbol and everything after it untouched. Its correctness theorem requires
that an occurrence of `ending` lies at or to the right of the starting cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseUntil (tm : SingleTapeTM Symbol) (ending : Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some ending) do
    eraseAndMove tm

/-- Erasing stops at the next ending symbol and leaves that symbol and its suffix unchanged. -/
@[spec] theorem eraseUntil_spec (ending : Symbol) (crossed rest : List Symbol)
    (hcrossed : ending ∉ crossed) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] (crossed ++ ending :: rest)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseUntil tm ending
    ⦃ fun _ cost final => final.config = ⟨label, cursor [] (ending :: rest)⟩ ∧
        final.headPos = origin + crossed.length ∧ cost.steps = elapsed + crossed.length ⦄ := by
  induction crossed generalizing origin elapsed with
  | nil =>
    unfold eraseUntil
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol crossed ih =>
    have hparts : ending ≠ symbol ∧ ending ∉ crossed := by simpa using hcrossed
    unfold eraseUntil
    vcgen [Spec.while_step_spec (loop := eraseUntil tm ending) (hloop := rfl), eraseAndMove_spec,
      ih hparts.2 (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      cursor, BiTape.write, BiTape.moveRight, add_assoc]
    all_goals lia

/--
If `crossed` contains no `ending`, the program erases exactly `crossed` and stops on the next
occurrence of `ending`. The remaining word is the only occupied part of the tape.
-/
theorem eraseUntil_correct (ending : Symbol) (crossed rest : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] (crossed ++ ending :: rest))
    (hcrossed : ending ∉ crossed) :
    Runs (eraseUntil tm ending) s (cursor [] (ending :: rest))
      (s.headPos + crossed.length) crossed.length := by
  apply Spec.runs
  vcgen [eraseUntil_spec ending crossed rest hcrossed s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all 

/--
`eraseLeft tm` is a Turing machine program that replaces the current occupied cell with a blank and
moves left, repeating until it reaches an already blank cell. Starting on the last symbol of a
contiguous block erases the whole block and leaves the head on the blank just before it.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseLeft (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ none
    moveₜ .Left

/-- Starting the erasing loop on a blank tape leaves it unchanged. -/
private theorem eraseLeft_blank_spec (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.nil⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseLeft tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.nil⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  unfold eraseLeft
  vcgen [Spec.while_false_spec]
  simp_all [BiTape.nil]

/-- Erasing to the left clears the entire displayed word and counts one move per symbol. -/
@[spec] theorem eraseLeft_spec (left : List Symbol) (bit : Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left [bit]⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseLeft tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.nil⟩ ∧
        final.headPos = origin - (left.length + 1 : Nat) ∧
        cost.steps = elapsed + left.length + 1 ⦄ := by
  induction left generalizing bit origin elapsed with
  | nil =>
    unfold eraseLeft
    vcgen [Spec.while_step_spec (loop := eraseLeft tm) (hloop := rfl),
      eraseLeft_blank_spec label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      BiTape.nil, BiTape.moveLeft, BiTape.write, cursor, sub_eq_add_neg]
  | cons previous left ih =>
    unfold eraseLeft
    vcgen [Spec.while_step_spec (loop := eraseLeft tm) (hloop := rfl),
      ih previous (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      sub_eq_add_neg, add_assoc]
    all_goals lia

/--
Starting on the last symbol `bit`, this program erases that cell and the entire prefix `left`,
leaving a completely blank tape. The head finishes `left.length + 1` cells to the left of its
starting coordinate, using exactly that many head moves.
-/
theorem eraseLeft_correct (left : List Symbol) (bit : Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left [bit]) :
    Runs (eraseLeft tm) s BiTape.nil (s.headPos - (left.length + 1 : ℕ)) (left.length + 1) := by
  apply Spec.runs
  vcgen [eraseLeft_spec left bit s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`eraseToLeft tm` is a Turing machine program that starts on the blank immediately after a contiguous
block. It moves left, erases the block while moving backward, and then moves right onto the cell
that used to hold the first symbol. For an empty block, it returns to the starting blank after two
moves.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseToLeft (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  eraseLeft tm
  moveₜ .Right

/-- Erasing the preceding word clears the tape and returns to its former first cell. -/
@[spec] theorem eraseToLeft_spec (left : List Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left []⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseToLeft tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.nil⟩ ∧
        final.headPos = origin - left.length ∧ cost.steps = elapsed + left.length + 2 ⦄ := by
  cases left with
  | nil =>
    vcgen [eraseToLeft, eraseLeft_blank_spec label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost,
      BiTape.nil, BiTape.moveLeft, BiTape.moveRight, sub_eq_add_neg]
  | cons bit left =>
    vcgen [eraseToLeft, eraseLeft_spec left bit label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost,
      BiTape.nil, BiTape.moveRight, sub_eq_add_neg, add_assoc]
    all_goals lia

/--
Starting from `cursor left []`, this program leaves the tape blank and finishes at `s.headPos -
left.length`. It uses exactly `left.length + 2` head moves and preserves the control state,
including when `left` is empty.
-/
theorem eraseToLeft_correct (left : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left []) :
    Runs (eraseToLeft tm) s BiTape.nil (s.headPos - left.length) (left.length + 2) := by
  apply Spec.runs
  vcgen [eraseToLeft_spec left s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`eraseBlock tm` is a Turing machine program that starts at the beginning of the input block, scans
to the blank after it, and erases the symbols on the way back. It finishes at the original head
coordinate on a blank tape. The recorded allocation and visit histories are retained.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseBlock (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  eraseToLeft tm

/-- Erasing the input word restores the head and records the complete round trip. -/
@[spec] theorem eraseBlock_spec (bits : List Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] bits⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseBlock tm
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.nil⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * bits.length + 2 ⦄ := by
  vcgen [eraseBlock, seekRightBlank_spec [] bits label origin elapsed,
    eraseToLeft_spec bits.reverse label (origin + bits.length) (elapsed + bits.length)]
  all_goals simp_all
  all_goals lia

/--
Erasing `bits` leaves a completely blank tape and restores the initial head coordinate. The program
preserves the control state and uses exactly `2 * bits.length + 2` head moves, even when the input
is empty.
-/
theorem eraseBlock_correct (bits : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (eraseBlock tm) s BiTape.nil s.headPos (2 * bits.length + 2) := by
  apply Spec.runs
  vcgen [eraseBlock_spec bits s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.SingleTapeTuringMachines
