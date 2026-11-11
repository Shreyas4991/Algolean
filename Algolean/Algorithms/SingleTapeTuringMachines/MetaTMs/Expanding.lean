/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Writing

/-!
# Making room for the symbols of an encoding

* `shiftRight` shifts a word one cell to the right and leaves a blank at its old starting cell.
* The alphabet comparisons are fixed once with the program and cover its finite alphabet.
* Its correctness proof preserves the arbitrary contents beyond the blank to the left.

The serializer uses this shift to replace each input symbol with its fixed, nonempty code word.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private def shiftSymbolRight (symbol : Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right
  tape ←ₜ some symbol
  moveₜ .Left
  moveₜ .Left

private theorem shiftSymbolRight_spec (left : StackTape Symbol) (symbol : Symbol)
    (word : List Symbol) (tail : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, (segment (StackTape.cons none left) (symbol :: word) tail).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      shiftSymbolRight (tm := tm) symbol
    ⦃ fun _ cost final => final.config = ⟨label,
        (segment (StackTape.cons none (StackTape.cons (some symbol) left)) word tail).mirror⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps = elapsed + 3 ⦄ := by
  vcgen [shiftSymbolRight]
  cases word <;> simp_all [TMState.write, TMState.move, TMState.moveCost,
    BiTape.segment, BiTape.mirror, BiTape.write, BiTape.moveLeft, BiTape.moveRight,
    sub_eq_add_neg, add_assoc]

private def shiftRightLoop (symbols : List Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    select symbols (fun symbol => .tapeIs (some symbol)) (shiftSymbolRight (tm := tm))

private theorem shiftSelected_spec (symbols : List Symbol) (symbol : Symbol)
    (hmem : symbol ∈ symbols) (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, (segment (StackTape.cons none left) (symbol :: word) tail).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      select symbols (fun symbol => .tapeIs (some symbol)) (shiftSymbolRight (tm := tm))
    ⦃ fun _ cost final => final.config = ⟨label,
        (segment (StackTape.cons none (StackTape.cons (some symbol) left)) word tail).mirror⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps = elapsed + 3 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  vcgen [Spec.select_spec symbols (fun symbol => .tapeIs (some symbol))
    (shiftSymbolRight (tm := tm)) symbol hmem]
  constructor
  · intro candidate
    simp [hcfg, eq_comm]
  · vcgen [shiftSymbolRight_spec left symbol word tail label origin elapsed]
    all_goals simp_all

private theorem shiftRightLoop_spec (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, (segment (StackTape.cons none left) word tail).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      shiftRightLoop (tm := tm) symbols
    ⦃ fun _ cost final => final.config =
        ⟨label, (segment (StackTape.cons none (stackAppend word.reverse left)) [] tail).mirror⟩ ∧
        final.headPos = origin - word.length ∧ cost.steps = elapsed + 3 * word.length ⦄ := by
  induction word generalizing left origin elapsed with
  | nil =>
    unfold shiftRightLoop
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol word ih =>
    unfold shiftRightLoop
    vcgen [Spec.while_step_spec (loop := shiftRightLoop (tm := tm) symbols) (hloop := rfl),
      shiftSelected_spec symbols symbol (hcover symbol) left word tail label origin elapsed,
      ih (StackTape.cons (some symbol) left) (origin - 1) (elapsed + 3)]
    all_goals simp_all [List.reverse_cons, stackAppend_append, sub_eq_add_neg, add_assoc]
    all_goals lia

/--
This machine shifts the word under the head one cell to the right. A blank must lie immediately
before the word and another immediately after it. The blank after the word becomes the blank
at its old starting position. All other cells on either side are preserved. The head finishes
at that old starting position. The list `symbols` must contain every alphabet symbol.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def shiftRight (tm : SingleTapeTM Symbol) (symbols : List Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Left
  shiftRightLoop symbols
  moveₜ .Right

/-- Shifting right preserves every neighboring cell and restores the head in linear time. -/
@[spec] theorem shiftRight_spec (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (left : StackTape Symbol) (word : List Symbol) (tail : StackTape Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, segment (StackTape.cons none left) word tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      shiftRight tm symbols
    ⦃ fun _ cost final => final.config =
        ⟨label, segment (StackTape.cons none left) [] (stackAppend word tail)⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 4 * word.length + 2 ⦄ := by
  vcgen [shiftRight, seekRightBlank_segment_spec (StackTape.cons none left) tail word
      label origin elapsed,
    shiftRightLoop_spec symbols hcover tail word.reverse left
      label (origin + word.length - 1) (elapsed + word.length + 1)]
  all_goals cases hw : word.reverse
  all_goals simp_all [TMState.move, TMState.moveCost, BiTape.segment,
    BiTape.mirror, BiTape.moveLeft, BiTape.moveRight]
  all_goals lia

/-- Shifting preserves the word and the left region and uses `4 * word.length + 2` head moves. -/
theorem shiftRight_correct (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (left : StackTape Symbol) (word : List Symbol) (tail : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons none left) word tail) :
    Runs (shiftRight tm symbols) s
      (segment (StackTape.cons none left) [] (stackAppend word tail))
      s.headPos (4 * word.length + 2) := by
  apply Spec.runs
  vcgen [shiftRight_spec symbols hcover left word tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template writes a fixed word while moving left after each symbol. The containing
machine fixes the word when including the template and uses it for every input length.
-/
def writeLeft (tm : SingleTapeTM Symbol) : List Symbol → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: word => do [TMQuery tm]
    tape ←ₜ some symbol
    moveₜ .Left
    writeLeft tm word

/-- Writing left fills the blank cells and leaves the reversed word to the right of the head. -/
@[spec] theorem writeLeft_spec (word : List Symbol) (left right : StackTape Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment (StackTape.blanks word.length left) [] right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeLeft tm word
    ⦃ fun _ cost final => final.config = ⟨label, segment left [] (stackAppend word.reverse right)⟩ ∧
        final.headPos = origin - word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  induction word generalizing right origin elapsed with
  | nil =>
    vcgen [writeLeft]
    simp_all
  | cons symbol word ih =>
    vcgen [writeLeft, ih (StackTape.cons (some symbol) right) (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.write, TMState.move, TMState.moveCost, BiTape.segment,
      BiTape.write, BiTape.moveLeft,
      List.reverse_cons, stackAppend_append, sub_eq_add_neg, add_assoc]
    all_goals lia

/-- Writing left across blanks places the reversed word just to the right of the head. -/
theorem writeLeft_correct (word : List Symbol) (left right : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.blanks word.length left) [] right) :
    Runs (writeLeft tm word) s
      (segment left [] (stackAppend word.reverse right))
      (s.headPos - word.length) word.length := by
  apply Spec.runs
  vcgen [writeLeft_spec word left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

private def widen (symbols : List Symbol) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | k + 1 => do [TMQuery tm]
    moveₜ .Right
    shiftRight tm symbols
    widen symbols k

private theorem widen_spec (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (k : Nat) (left : StackTape Symbol) (suffix : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, segment left [] (StackTape.mapSome suffix)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      widen (tm := tm) symbols k
    ⦃ fun _ cost final => final.config =
        ⟨label, segment (StackTape.blanks k left) [] (StackTape.mapSome suffix)⟩ ∧
        final.headPos = origin + k ∧ cost.steps = elapsed + k * (4 * suffix.length + 3) ⦄ := by
  induction k generalizing left origin elapsed with
  | zero =>
    vcgen [widen]
    simp_all
  | succ k ih =>
    vcgen [widen, shiftRight_spec symbols hcover left suffix StackTape.nil
        label (origin + 1) (elapsed + 1),
      ih (StackTape.cons none left) (origin + 1) (elapsed + 1 + 4 * suffix.length + 2)]
    all_goals simp_all [TMState.move, TMState.moveCost, Nat.add_mul, add_assoc]
    all_goals lia

/--
This machine template inserts a fixed word just beyond the blank under the head. It shifts the
word already to the right to make room, then returns to the same blank. The containing machine
fixes the inserted word and alphabet comparisons once for all inputs.
-/
def insertAfterBlank (tm : SingleTapeTM Symbol) (symbols word : List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  widen symbols word.length
  writeLeft tm word.reverse

/-- Inserting the fixed word preserves both neighbors and returns to the starting blank. -/
@[spec] theorem insertAfterBlank_spec (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (left : StackTape Symbol) (suffix : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, segment left [] (StackTape.mapSome suffix)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      insertAfterBlank tm symbols word
    ⦃ fun _ cost final => final.config =
        ⟨label, segment left [] (StackTape.mapSome (word ++ suffix))⟩ ∧
        final.headPos = origin ∧
        cost.steps = elapsed + word.length * (4 * suffix.length + 3) + word.length ⦄ := by
  vcgen [insertAfterBlank, widen_spec symbols hcover word.length left suffix label origin elapsed,
    writeLeft_spec word.reverse left (StackTape.mapSome suffix) label (origin + word.length)
      (elapsed + word.length * (4 * suffix.length + 3))]
  all_goals simp_all

/-- Inserting preserves both neighboring regions and takes linearly many moves in their size. -/
theorem insertAfterBlank_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (left : StackTape Symbol) (suffix : List Symbol)
    (s : TMState tm) (hs : s.config.BiTape = segment left [] (StackTape.mapSome suffix)) :
    Runs (insertAfterBlank tm symbols word) s
      (segment left [] (StackTape.mapSome (word ++ suffix))) s.headPos
      (word.length * (4 * suffix.length + 3) + word.length) := by
  apply Spec.runs
  vcgen [insertAfterBlank_spec symbols word hcover left suffix s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template replaces the symbol under the head with a fixed nonempty word, leaving
one blank between that word and the unprocessed symbols to its left. The head then moves to
those symbols. There must already be a blank just to the right of the starting cell.
The containing machine fixes the replacement word and alphabet comparisons once for all inputs.
-/
def replaceBeforeBlank (tm : SingleTapeTM Symbol) (symbols word : List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right
  widen symbols word.tail.length
  writeLeft tm word.reverse
  moveₜ .Left

/-- Replacing the current symbol preserves both neighbors and moves one cell left. -/
@[spec] theorem replaceBeforeBlank_spec (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (first : Symbol) (rest : List Symbol)
    (symbol : Symbol) (remaining suffix : List Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome suffix))
          (symbol :: remaining) StackTape.nil).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      replaceBeforeBlank tm symbols (first :: rest)
    ⦃ fun _ cost final => final.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome ((first :: rest) ++ suffix)))
          remaining StackTape.nil).mirror⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps =
          elapsed + rest.length * (4 * suffix.length + 3) + (first :: rest).length + 2 ⦄ := by
  unfold replaceBeforeBlank
  simp only [List.tail_cons]
  vcgen [widen_spec symbols hcover rest.length (StackTape.cons none (StackTape.mapSome remaining))
      suffix label (origin + 1) (elapsed + 1),
    writeLeft_spec (first :: rest).reverse (StackTape.mapSome remaining) (StackTape.mapSome suffix)
      label (origin + 1 + rest.length) (elapsed + 1 + rest.length * (4 * suffix.length + 3))]
  all_goals cases remaining
  all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
    BiTape.segment, BiTape.mirror, BiTape.write, BiTape.moveRight, BiTape.moveLeft]
  all_goals lia

/-- Replacing preserves both neighboring words and moves to the next symbol on the left. -/
theorem replaceBeforeBlank_correct (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (first : Symbol) (rest : List Symbol)
    (symbol : Symbol) (remaining suffix : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape =
      (segment (StackTape.cons none (StackTape.mapSome suffix))
        (symbol :: remaining) StackTape.nil).mirror) :
    Runs (replaceBeforeBlank tm symbols (first :: rest)) s
      (segment (StackTape.cons none (StackTape.mapSome ((first :: rest) ++ suffix)))
        remaining StackTape.nil).mirror
      (s.headPos - 1) (rest.length * (4 * suffix.length + 3) + (first :: rest).length + 2) := by
  apply Spec.runs
  vcgen [replaceBeforeBlank_spec symbols hcover first rest symbol remaining suffix
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all [add_assoc]

end Algolean.Algorithms.SingleTapeTuringMachines
