/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Foundations.Data.BiTape

/-!
# Describing words and blank cells on a tape

* `StackTape.blanks` and `StackTape.prepend` put blank cells or symbols before existing contents.
* `StackTape.separateWords` describes words separated by blank cells.
* `BiTape.segment` describes a word beginning under the head, with other contents on either side.
* `BiTape.mirror` exchanges the two sides of the tape.

The lemmas describe how these tapes change when the head moves or writes. They support the
correctness proofs of machines that copy, write, and encode words; they do not execute a machine.
-/

@[expose] public section

namespace Cslib.Turing.StackTape

/-- Restoring a blank first cell reconstructs any tape stack whose first cell is blank. -/
@[simp, grind =] theorem cons_none_tail {Symbol : Type} (stack : StackTape Symbol)
    (h : stack.head = none) : cons none stack.tail = stack := by
  simpa only [h] using cons_head_tail stack

/-- This stores a finite list of tape cells, treating every later cell as blank. -/
def ofList {Symbol : Type} (cells : List (Option Symbol)) : StackTape Symbol :=
  cells.foldr cons nil

/-- An empty list describes a completely blank side of the tape. -/
@[simp] theorem ofList_nil {Symbol : Type} : ofList ([] : List (Option Symbol)) = nil := rfl

/-- Storing one more cell places it before the remaining cells. -/
@[simp] theorem ofList_cons {Symbol : Type} (cell : Option Symbol) (cells : List (Option Symbol)) :
    ofList (cell :: cells) = cons cell (ofList cells) := rfl

/-- A finite cell list describes a blank tape stack exactly when every listed cell is blank. -/
@[simp] theorem ofList_eq_nil_iff {Symbol : Type} (cells : List (Option Symbol)) :
    ofList cells = nil ↔ ∀ cell ∈ cells, cell = none := by
  induction cells with
  | nil => simp
  | cons cell cells ih =>
    rw [ofList_cons, StackTape.eq_iff]
    simp only [head_cons, tail_cons]
    change (cell = none ∧ ofList cells = nil) ↔ _
    simp only [ih, List.forall_mem_cons]

/-- A list of blank cells describes a completely blank side of the tape. -/
@[simp] theorem ofList_replicate_none {Symbol : Type} (n : Nat) :
    ofList (List.replicate n (none : Option Symbol)) = nil := by
  induction n <;> simp_all [List.replicate_succ, cons, nil]

/-- Blank cells after the described cells do not change the tape. -/
@[simp] theorem ofList_append_blanks {Symbol : Type} (cells : List (Option Symbol)) (n : Nat) :
    ofList (cells ++ List.replicate n none) = ofList cells := by
  simp only [ofList, List.foldr_append]
  simp only [← ofList.eq_def, ofList_replicate_none]

/-- A word of occupied cells has the same tape representation as `mapSome`. -/
@[simp] theorem ofList_map_some {Symbol : Type} (word : List Symbol) :
    ofList (word.map some) = mapSome word := by
  induction word <;> simp_all [mapSome, cons, nil]

/-- This puts the specified number of blank cells before an existing tape stack. -/
@[simp] def blanks {Symbol : Type} : Nat → StackTape Symbol → StackTape Symbol
  | 0, tail => tail
  | n + 1, tail => cons none (blanks n tail)

/-- Placing two sequences of blanks before a stack adds their lengths. -/
@[simp] theorem blanks_add {Symbol : Type} (n m : Nat) (tail : StackTape Symbol) :
    blanks (n + m) tail = blanks n (blanks m tail) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Nat.succ_add, blanks] using congrArg (cons none) ih

/-- A blank can be placed before or after the other blanks without changing the stack. -/
@[simp] theorem blanks_cons {Symbol : Type} (n : Nat) (tail : StackTape Symbol) :
    blanks n (cons none tail) = cons none (blanks n tail) := by
  induction n <;> simp_all

/-- Adding blanks to an entirely blank stack leaves it blank. -/
@[simp] theorem blanks_nil {Symbol : Type} (n : Nat) :
    blanks n (nil : StackTape Symbol) = nil := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cons none (blanks n nil) = nil
    rw [ih]
    rfl

end Cslib.Turing.StackTape

namespace Cslib.Turing

namespace StackTape

/-- This puts the occupied cells of a word before an existing side of the tape. -/
@[simp] def prepend {Symbol : Type} : List Symbol → StackTape Symbol → StackTape Symbol
  | [], tail => tail
  | symbol :: word, tail => cons (some symbol) (prepend word tail)

/-- Prepending concatenated words is the same as prepending them in sequence. -/
@[grind =] theorem prepend_append {Symbol : Type} (first second : List Symbol)
    (tail : StackTape Symbol) :
    prepend (first ++ second) tail = prepend first (prepend second tail) := by
  induction first <;> simp_all

/-- Prepending a word to an empty side of a tape stores exactly that word. -/
@[simp] theorem prepend_nil {Symbol : Type} (word : List Symbol) :
    prepend word nil = mapSome word := by
  induction word <;> simp_all [mapSome, cons, nil]

/-- Prepending to a stored word stores the concatenation. -/
@[simp] theorem prepend_mapSome {Symbol : Type} (first second : List Symbol) :
    prepend first (mapSome second) = mapSome (first ++ second) := by
  rw [← prepend_nil second, ← prepend_append, prepend_nil]

/-- This puts the given words before a tape tail, with a blank after each word. -/
@[simp] def separateWords {Symbol : Type} : List (List Symbol) → StackTape Symbol → StackTape Symbol
  | [], tail => tail
  | word :: rest, tail => prepend word (cons none (separateWords rest tail))

/-- Joining two lists of separated words places the second list after the first. -/
@[simp, grind =] theorem separateWords_append {Symbol : Type} (first second : List (List Symbol))
    (tail : StackTape Symbol) :
    separateWords (first ++ second) tail = separateWords first (separateWords second tail) := by
  induction first with
  | nil => rfl
  | cons word first ih => simp only [List.cons_append, separateWords, ih]

end StackTape

namespace BiTape

/-- Different words give different clean tapes with their first cells under the head. -/
theorem mk₁_injective {Symbol : Type} : Function.Injective (mk₁ (Symbol := Symbol)) := by
  let read (tape : BiTape Symbol) := tape.head.toList ++ tape.right.toList.filterMap id
  have hread (word : List Symbol) : read (mk₁ word) = word := by
    cases word <;> simp [read, mk₁, nil, StackTape.mapSome, StackTape.nil]
  intro first second h
  exact (hread first).symm.trans ((congrArg read h).trans (hread second))

/--
This describes a word beginning under the head, with an arbitrary tape on its left and another
region separated from it by a blank on its right. An empty word puts the head on that blank.
-/
@[simps head left right]
def segment {Symbol : Type} (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) : BiTape Symbol where
  head := word.head?
  left := left
  right := match word with
    | [] => tail
    | _ :: rest => StackTape.prepend rest (StackTape.cons none tail)

/-- This reflects the tape about its head by exchanging its left and right sides. -/
@[simps] def mirror {Symbol : Type} (contents : BiTape Symbol) : BiTape Symbol :=
  ⟨contents.head, contents.right, contents.left⟩

@[simp] theorem mirror_mirror {Symbol : Type} (contents : BiTape Symbol) :
    contents.mirror.mirror = contents := rfl

variable {Symbol : Type}

@[simp] theorem segment_moveRight (left : StackTape Symbol) (symbol : Symbol) (word : List Symbol)
    (tail : StackTape Symbol) :
    (segment left (symbol :: word) tail).moveRight =
      segment (StackTape.cons (some symbol) left) word tail := by
  cases word <;> simp [segment, moveRight]

@[simp] theorem segment_moveLeft (left : StackTape Symbol) (symbol : Symbol) (word : List Symbol)
    (tail : StackTape Symbol) :
    (segment (StackTape.cons (some symbol) left) word tail).moveLeft =
      segment left (symbol :: word) tail := by
  cases word <;> simp [segment, moveLeft]

/-- Moving left from a stored list crosses its first symbol and preserves the remaining cells. -/
@[simp, grind =] theorem segment_moveLeft_mapSome (left : List Symbol) (symbol : Symbol)
    (word : List Symbol) (tail : StackTape Symbol) :
    (segment (StackTape.mapSome (symbol :: left)) word tail).moveLeft =
      segment (StackTape.mapSome left) (symbol :: word) tail :=
  segment_moveLeft (StackTape.mapSome left) symbol word tail

/-- Crossing a word puts its symbols in reverse order to the left of the head. -/
theorem segment_moveRight_iterate (left : StackTape Symbol) (crossed suffix : List Symbol)
    (tail : StackTape Symbol) :
    moveRight^[crossed.length] (segment left (crossed ++ suffix) tail) =
      segment (StackTape.prepend crossed.reverse left) suffix tail := by
  induction crossed generalizing left with
  | nil => simp
  | cons symbol crossed ih =>
    simpa [Function.iterate_succ_apply, List.reverse_cons, StackTape.prepend_append] using
      ih (StackTape.cons (some symbol) left)

/-- Moving back across the displayed prefix restores the head to that prefix's first cell. -/
theorem segment_moveLeft_iterate (left : StackTape Symbol) (crossed suffix : List Symbol)
    (tail : StackTape Symbol) :
    moveLeft^[crossed.length] (segment (StackTape.prepend crossed.reverse left) suffix tail) =
      segment left (crossed ++ suffix) tail := by
  induction crossed generalizing left with
  | nil => simp
  | cons symbol crossed ih =>
    simp only [List.length_cons, List.reverse_cons, StackTape.prepend_append]
    rw [Function.iterate_succ_apply', ih]
    simp

@[simp] theorem segment_write (left : StackTape Symbol) (old symbol : Symbol) (word : List Symbol)
    (tail : StackTape Symbol) :
    (segment left (old :: word) tail).write (some symbol) =
      segment left (symbol :: word) tail := rfl

@[simp] theorem segment_moveLeft_gap (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) :
    (segment (StackTape.cons none left) word tail).moveLeft =
      segment left [] (StackTape.prepend word (StackTape.cons none tail)) := by
  cases word <;> simp [segment, moveLeft]

@[simp] theorem segment_moveRight_gap (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) :
    (segment left [] (StackTape.prepend word (StackTape.cons none tail))).moveRight =
      segment (StackTape.cons none left) word tail := by
  cases word <;> simp [segment, moveRight]

@[simp] theorem segment_erase_advance (left : StackTape Symbol) (symbol : Symbol)
    (word : List Symbol) (tail : StackTape Symbol) :
    ((segment left (symbol :: word) tail).write none).moveRight =
      segment (StackTape.cons none left) word tail := by
  cases word <;> simp [segment, write, moveRight]

@[simp] theorem segment_start (word : List Symbol) :
    segment StackTape.nil word StackTape.nil = mk₁ word := by
  have hempty : StackTape.cons none (StackTape.nil : StackTape Symbol) = StackTape.nil := rfl
  cases word <;> simp [segment, mk₁, BiTape.nil, hempty]

end BiTape

end Cslib.Turing
