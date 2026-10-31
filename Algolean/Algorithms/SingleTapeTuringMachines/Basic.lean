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
# Contracts and tape views for single-tape procedures

`cursor left right` stores the prefix to the left of the head in reverse order, with `right`
starting at the head. The occupied block is `left.reverse ++ right`, surrounded by blanks.
`Runs` specifies tape contents, absolute head position, preserved control state, and exact
head-move cost. Its execution witness retains arbitrary pre-existing visited-cell history.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {Symbol : Type}

/-- A contiguous block, split at the head; the left part is in reverse order. -/
@[simps head left right]
def cursor (left right : List Symbol) : BiTape Symbol where
  head := right.head?
  left := StackTape.mapSome left
  right := StackTape.mapSome right.tail

/-- The blank immediately preceding a contiguous block. -/
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

variable [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- The identity procedure; its input is supplied exclusively by the initial tape. -/
def identity (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  pure ()

/-- Identity preserves the entire execution state and incurs zero cost. -/
theorem identity_correct (s : TMState tm) : Runs (identity tm) s s.config.BiTape s.headPos 0 := by
  exact ⟨0, s, completes_pure s, by cases s.config; rfl, rfl, rfl⟩

/-- Write a fixed Boolean constant at the current cell. -/
def writeBit (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ some bit

/-- A write preserves the head position, control state, and space history. -/
theorem writeBit_correct {tm : SingleTapeTM Bool} [DecidableEq tm.State]
    (s : TMState tm) (bit : Bool) :
    Runs (writeBit tm bit) s (s.config.BiTape.write (some bit)) s.headPos 0 :=
  ⟨0, s.write (some bit), completes_write s _, rfl, rfl, rfl⟩

/-- The primitive write contract also covers erasing a cell. -/
theorem write_correct (s : TMState tm) (symbol : Option Symbol) :
    Runs (FreeM.lift (.write symbol)) s (s.config.BiTape.write symbol) s.headPos 0 :=
  ⟨0, s.write symbol, completes_write s _, rfl, rfl, rfl⟩

/-- Moving preserves the control state and charges exactly one head move. -/
theorem move_correct (s : TMState tm) (dir : Dir) :
    Runs (FreeM.lift (.move dir)) s (s.move dir).config.BiTape
      (s.headPos + dir.offset) 1 := by
  refine ⟨s.moveCost dir, s.move dir, completes_move s dir, ?_, rfl, rfl⟩
  cases dir <;> rfl

end Algolean.Algorithms.SingleTapeTuringMachines
