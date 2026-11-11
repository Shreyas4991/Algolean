/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

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
open scoped TMQuery

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
  induction word generalizing left old s with
  | nil =>
    have hold : old = [] := List.eq_nil_of_length_eq_zero hlen
    subst old
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    change s.config = {s.config with BiTape := BiTape.segment left suffix tail}
    have ht : s.config.BiTape = BiTape.segment left suffix tail := by simpa using hs
    rw [← ht]
  | cons symbol word ih =>
    cases old with
    | nil => simp at hlen
    | cons previous old =>
      have hw := (write_correct s (some symbol)).append_move .Right
      have hrest := hw.seq (q := writeRight tm word) (by
        intro middle hm hp
        simpa [List.reverse_cons, StackTape.prepend_append, hp, add_assoc] using
          ih (StackTape.cons (some symbol) left) old (by simpa using hlen) middle
            (by simp [hm, hs]))
      simpa [writeRight, List.reverse_cons, StackTape.prepend_append,
        add_assoc, add_comm, add_left_comm] using hrest

/-- Writing on the blank right of a region adds the word and uses one move per written symbol. -/
theorem writeRight_correct (left : StackTape Symbol) (word : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment left [] StackTape.nil) :
    Runs (writeRight tm word) s (segment (stackAppend word.reverse left) [] StackTape.nil)
      (s.headPos + word.length) word.length := by
  induction word generalizing left s with
  | nil =>
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    change s.config = {s.config with BiTape := segment left [] StackTape.nil}
    rw [← hs]
  | cons symbol word ih =>
    have hw : Runs (writeAdvance tm (some symbol)) s
        (segment (StackTape.cons (some symbol) left) [] StackTape.nil) (s.headPos + 1) 1 := by
      simpa [writeAdvance, hs, Copying.segment, BiTape.segment, BiTape.write,
        BiTape.moveRight] using
        (write_correct s (some symbol)).append_move .Right
    have hr := hw.seq (q := writeRight tm word)
      (second := segment (stackAppend (symbol :: word).reverse left) [] StackTape.nil)
      (pos₂ := s.headPos + (symbol :: word).length) (time₂ := word.length) (by
        intro middle hm hp
        simpa [List.reverse_cons, stackAppend_append, hp, add_assoc, add_comm, add_left_comm] using
          ih (StackTape.cons (some symbol) left) middle (congrArg SingleTapeTM.Cfg.BiTape hm))
    simpa [writeRight, writeAdvance, Nat.add_comm] using hr

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
theorem setLeftCell_correct (old value : Option Symbol) (left : StackTape Symbol)
    (word : List Symbol) (tail : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons old left) word tail) :
    Runs (setLeftCell tm value) s (segment (StackTape.cons value left) word tail)
      s.headPos 2 := by
  refine ⟨_, _, ⟨3, rfl⟩, ?_, ?_, ?_⟩
  · cases word <;>
      simp [TMQuery.step, hs, Copying.segment, BiTape.segment, BiTape.moveLeft, BiTape.moveRight,
        BiTape.write]
  · simp [TMQuery.step, sub_eq_add_neg, add_assoc]
  · rfl

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
  have hm := setLeftCell_correct separator none left input StackTape.nil s hs
  have hr := hm.seq (q := seekRightBlank tm)
    (second := segment (stackAppend input.reverse (StackTape.cons none left)) [] StackTape.nil)
    (pos₂ := s.headPos + input.length) (time₂ := input.length) (by
      intro middle ht hp
      simpa [hp] using seekRightBlank_segment (StackTape.cons none left) input StackTape.nil
        middle (congrArg SingleTapeTM.Cfg.BiTape ht))
  have hw := hr.seq (q := writeRight tm word)
    (second := segment (stackAppend (input ++ word).reverse (StackTape.cons none left)) []
      StackTape.nil)
    (pos₂ := s.headPos + (input ++ word).length) (time₂ := word.length) (by
      intro middle ht hp
      simpa [hp, List.reverse_append, stackAppend_append, add_assoc] using
        writeRight_correct (stackAppend input.reverse (StackTape.cons none left)) word middle
          (congrArg SingleTapeTM.Cfg.BiTape ht))
  have hb := hw.seq (q := seekLeftEnd tm)
    (second := segment (StackTape.cons none left) (input ++ word) StackTape.nil)
    (pos₂ := s.headPos) (time₂ := (input ++ word).length + 2) (by
      intro middle ht hp
      convert seekLeftEnd_segment left (input ++ word).reverse [] StackTape.nil middle
        (congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
        simp [hp, add_comm, add_assoc])
  have hf := hb.seq (q := setLeftCell tm separator)
    (second := segment (StackTape.cons separator left) (input ++ word) StackTape.nil)
    (pos₂ := s.headPos) (time₂ := 2) (by
      intro middle ht hp
      simpa [hp] using setLeftCell_correct none separator left (input ++ word) StackTape.nil middle
        (congrArg SingleTapeTM.Cfg.BiTape ht))
  convert hf using 1
  · simp [appendWord, bind_assoc]
  · simp only [List.length_append]
    lia

end Algolean.Algorithms.SingleTapeTuringMachines
