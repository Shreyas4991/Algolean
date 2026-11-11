/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Verification

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Copying

/-!
# Writing fixed words and appending them to a tape region

* `writeRight` writes a fixed word to the right and stops on the following blank.
* `setLeftCell` changes the cell immediately to the left and returns to the starting cell.
* `appendWord` appends a fixed word to the current region and restores the starting position.

The words and symbols in these programs are fixed when constructing them. Their correctness
proofs allow arbitrary contents farther to the left. A separating cell lets `appendWord` find
its way back even when the current region is empty.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This writes the fixed word to the right, moving once after each symbol.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def writeRight (tm : SingleTapeTM Symbol) : List Symbol → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: word => do [TMQuery tm]
    tape ←ₜ some symbol
    moveₜ .Right
    writeRight tm word

/-- Writing replaces the chosen number of cells and preserves all cells farther to the right. -/
@[spec] theorem writeRight_overwrite_spec (left tail : StackTape Symbol)
    (word old suffix : List Symbol) (hlen : old.length = word.length)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left (old ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeRight tm word
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.prepend word.reverse left) suffix tail⟩ ∧
        final.headPos = origin + word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  induction word generalizing left old origin elapsed with
  | nil =>
    have hold : old = [] := List.eq_nil_of_length_eq_zero hlen
    subst old
    vcgen [writeRight]
    simp_all
  | cons symbol word ih =>
    cases old with
    | nil => simp at hlen
    | cons previous old =>
      vcgen [writeRight,
        ih (StackTape.cons (some symbol) left) old (by simpa using hlen)
          (origin + 1) (elapsed + 1)]
      all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
        List.reverse_cons, StackTape.prepend_append, add_assoc]
      all_goals lia

/--
Writing over an equally long prefix replaces just that prefix and advances by its length.
The rest of the word and the tape beyond its separating blank remain unchanged.
-/
theorem writeRight_overwrite (left tail : StackTape Symbol) (word old suffix : List Symbol)
    (hlen : old.length = word.length) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.segment left (old ++ suffix) tail) :
    Runs (writeRight tm word) s
      (BiTape.segment (StackTape.prepend word.reverse left) suffix tail)
      (s.headPos + word.length) word.length := by
  apply Spec.runs
  vcgen [writeRight_overwrite_spec left tail word old suffix hlen s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/-- Writing on a blank extends the region by the fixed word and stops on the following blank. -/
@[spec] theorem writeRight_spec (left : StackTape Symbol) (word : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left [] StackTape.nil⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeRight tm word
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.prepend word.reverse left) [] StackTape.nil⟩ ∧
        final.headPos = origin + word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  induction word generalizing left origin elapsed with
  | nil =>
    vcgen [writeRight]
    simp_all
  | cons symbol word ih =>
    vcgen [writeRight, ih (StackTape.cons (some symbol) left) (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
      List.reverse_cons, StackTape.prepend_append, add_assoc]
    all_goals lia

/-- Writing on the blank right of a region adds the word and uses one move per written symbol. -/
theorem writeRight_correct (left : StackTape Symbol) (word : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment left [] StackTape.nil) :
    Runs (writeRight tm word) s (segment (stackAppend word.reverse left) [] StackTape.nil)
      (s.headPos + word.length) word.length := by
  apply Spec.runs
  vcgen [writeRight_spec left word s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This writes the chosen value in the cell to the left and returns to the original cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def setLeftCell (tm : SingleTapeTM Symbol) (value : Option Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  tape ←ₜ value
  moveₜ .Right

/-- Changing the left neighboring cell preserves every other cell and uses two head moves. -/
@[spec] theorem setLeftCell_spec (old value : Option Symbol) (left : StackTape Symbol)
    (word : List Symbol) (tail : StackTape Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (StackTape.cons old left) word tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      setLeftCell tm value
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.cons value left) word tail⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 ⦄ := by
  vcgen [setLeftCell]
  cases word <;> simp_all [TMState.move, TMState.write, TMState.moveCost,
    BiTape.segment, BiTape.moveLeft, BiTape.moveRight, BiTape.write]

/-- Changing the left neighboring cell preserves every other cell and uses two head moves. -/
theorem setLeftCell_correct (old value : Option Symbol) (left : StackTape Symbol)
    (word : List Symbol) (tail : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons old left) word tail) :
    Runs (setLeftCell tm value) s (segment (StackTape.cons value left) word tail)
      s.headPos 2 := by
  apply Spec.runs
  vcgen [setLeftCell_spec old value left word tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This appends the fixed word to the region under the head and returns to its first cell. It uses
the cell immediately to the left as a temporary blank, then restores its value `separator`.
There must be no occupied cells beyond the blank ending the current region.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def appendWord (tm : SingleTapeTM Symbol) (separator : Option Symbol) (word : List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  setLeftCell tm none
  seekRightBlank tm
  writeRight tm word
  seekLeftEnd tm
  setLeftCell tm separator

/-- Appending preserves the neighboring regions and restores the head with the stated move count. -/
@[spec] theorem appendWord_spec (separator : Option Symbol) (left : StackTape Symbol)
    (input word : List Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (StackTape.cons separator left) input StackTape.nil⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendWord tm separator word
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.cons separator left) (input ++ word) StackTape.nil⟩ ∧
        final.headPos = origin ∧
        cost.steps = elapsed + 2 * (input.length + word.length) + 6 ⦄ := by
  vcgen [appendWord,
    setLeftCell_spec separator none left input StackTape.nil label origin elapsed,
    seekRightBlank_segment_spec (StackTape.cons none left) StackTape.nil input
      label origin (elapsed + 2),
    writeRight_spec (StackTape.prepend input.reverse (StackTape.cons none left)) word
      label (origin + input.length) (elapsed + 2 + input.length),
    seekLeftEnd_segment_spec left StackTape.nil (input ++ word).reverse []
      label (origin + input.length + word.length) (elapsed + 2 + input.length + word.length),
    setLeftCell_spec none separator left (input ++ word) StackTape.nil
      label origin (elapsed + 2 + input.length + word.length + (input ++ word).length + 2)]
  all_goals simp_all [List.reverse_append, StackTape.prepend_append, add_assoc]
  all_goals lia

/--
Appending a fixed word preserves all cells to the left of the separator and restores the head.
The number of moves is twice the combined word length plus six.
-/
theorem appendWord_correct (separator : Option Symbol) (left : StackTape Symbol)
    (input word : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons separator left) input StackTape.nil) :
    Runs (appendWord tm separator word) s
      (segment (StackTape.cons separator left) (input ++ word) StackTape.nil)
      s.headPos (2 * (input.length + word.length) + 6) := by
  apply Spec.runs
  vcgen [appendWord_spec separator left input word s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.SingleTapeTuringMachines
