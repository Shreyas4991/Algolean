/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic
public import Algolean.Models.SingleTapeTM.Composition.Sequential
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Tape views and primitive programs

This file describes how the example Turing machine programs view a finite block of symbols on an
otherwise blank tape. In `cursor left right`, `left` lists the cells to the left of the head in
reverse order, and `right` starts at the head. If `right` is empty, the head is on the blank
immediately after the block. The view `before right` instead puts the head on the blank before the
block.

The correctness lemmas use `Runs` to state the resulting tape, the absolute head position,
preservation of the control state, and the number of head moves for primitive write and move
instructions. A write costs no head moves, although it still consumes interpreter fuel. Moving
with direction `.Stop` counts as one move even though the head stays in place.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {Symbol : Type}

/--
`cursor left right` is a pure Lean function that describes a contiguous block whose symbols, from
left to right, are `left.reverse ++ right`. The head is on the first symbol of `right`, or on the
blank just after the block when `right` is empty. All cells outside the block are blank.
-/
@[simps head left right]
def cursor (left right : List Symbol) : BiTape Symbol where
  head := right.head?
  left := StackTape.mapSome left
  right := StackTape.mapSome right.tail

/--
`before right` is a pure Lean function that describes a tape with the head on a blank cell and the
word `right` immediately to its right. Every cell to the left of the head and beyond the word is
blank.
-/
@[simps]
def before (right : List Symbol) : BiTape Symbol where
  head := none
  left := ∅
  right := StackTape.mapSome right

@[simp] theorem head_mapSome (bits : List Symbol) : (StackTape.mapSome bits).head = bits.head? := by
  cases bits <;> rfl

@[simp] theorem tail_mapSome (bits : List Symbol) :
    (StackTape.mapSome bits).tail = StackTape.mapSome bits.tail := by
  cases bits <;> rfl

@[simp] theorem cons_mapSome (bit : Symbol) (bits : List Symbol) :
    StackTape.cons (some bit) (StackTape.mapSome bits) = StackTape.mapSome (bit :: bits) := rfl

@[simp] theorem mapSome_nil : StackTape.mapSome ([] : List Symbol) = StackTape.nil := rfl

@[simp] theorem head_nil : (StackTape.nil : StackTape Symbol).head = none := rfl

@[simp] theorem tail_nil : (StackTape.nil : StackTape Symbol).tail = StackTape.nil := rfl

@[simp] theorem cons_none_nil :
    StackTape.cons none (StackTape.nil : StackTape Symbol) = StackTape.nil := rfl

theorem cursor_start (bits : List Symbol) : cursor [] bits = BiTape.mk₁ bits := by
  cases bits <;> rfl

@[simp] theorem before_nil : before ([] : List Symbol) = BiTape.nil := rfl

@[simp] theorem cursor_nil : cursor ([] : List Symbol) [] = BiTape.nil := rfl

@[simp] theorem cursor_moveRight (left : List Symbol) (bit : Symbol) (right : List Symbol) :
    (cursor left (bit :: right)).moveRight = cursor (bit :: left) right := by
  simp [cursor, BiTape.moveRight]

@[simp] theorem cursor_moveLeft (bit : Symbol) (left right : List Symbol) :
    (cursor (bit :: left) right).moveLeft = cursor left (bit :: right) := by
  cases right <;> simp [cursor, BiTape.moveLeft]

@[simp] theorem cursor_moveLeft_nil (right : List Symbol) :
    (cursor [] right).moveLeft = before right := by
  cases right <;> simp [cursor, before, BiTape.moveLeft]

@[simp] theorem before_moveRight (right : List Symbol) :
    (before right).moveRight = cursor [] right := by
  simp [before, cursor, BiTape.moveRight]

@[simp] theorem cursor_write (left : List Symbol) (old bit : Symbol) (right : List Symbol) :
    (cursor left (old :: right)).write (some bit) = cursor left (bit :: right) := rfl

@[simp] theorem cursor_write_blank (left : List Symbol) (bit : Symbol) :
    (cursor left []).write (some bit) = cursor left [bit] := rfl

@[simp] theorem cursor_erase_last (left : List Symbol) (bit : Symbol) :
    (cursor left [bit]).write none = cursor left [] := rfl

variable [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
A primitive write replaces the current cell with `symbol` and leaves the head and control state
unchanged. Passing `none` erases that cell, and passing `some value` writes an occupied cell. Both
cases use zero head moves.
-/
theorem write_correct (s : TMState tm) (symbol : Option Symbol) :
    Runs (FreeM.lift (.write symbol)) s (s.config.BiTape.write symbol) s.headPos 0 :=
  ⟨0, s.write symbol, completes_write s _, rfl, rfl, rfl⟩

/--
A primitive move leaves the tape symbols and control state unchanged and changes the absolute head
position by `dir.offset`. The cost is exactly one head move, including when `dir` is `.Stop`.
-/
theorem move_correct (s : TMState tm) (dir : Dir) :
    Runs (FreeM.lift (.move dir)) s (s.move dir).config.BiTape
      (s.headPos + dir.offset) 1 := by
  refine ⟨s.moveCost dir, s.move dir, completes_move s dir, ?_, rfl, rfl⟩
  cases dir <;> rfl

end Algolean.Algorithms.SingleTapeTuringMachines
