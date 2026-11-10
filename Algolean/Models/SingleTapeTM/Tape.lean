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
theorem prepend_append {Symbol : Type} (first second : List Symbol) (tail : StackTape Symbol) :
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

end StackTape

namespace BiTape

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
