/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Foundations.Data.StackTape

/-!
# Adding blank cells to one side of a tape

`StackTape.blanks` places a specified number of blank cells before an existing side of a tape.
The lemmas combine consecutive sequences of blanks and show that adding blanks to an entirely
blank side leaves it unchanged.
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
