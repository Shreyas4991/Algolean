/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch

/-! # Boolean single-cell procedures -/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

@[simp] theorem cursor_write (left : List Bool) (old bit : Bool) (right : List Bool) :
    (cursor left (old :: right)).write (some bit) = cursor left (bit :: right) := rfl

@[simp] theorem cursor_write_blank (left : List Bool) (bit : Bool) :
    (cursor left []).write (some bit) = cursor left [bit] := rfl

/-- Writing a bit at either a blank or occupied head preserves the suffix after that cell. -/
theorem cursor_write_any (left right : List Bool) (bit : Bool) :
    (cursor left right).write (some bit) = cursor left (bit :: right.tail) := by
  cases right <;> rfl

@[simp] theorem cursor_erase_last (left : List Bool) (bit : Bool) :
    (cursor left [bit]).write none = cursor left [] := rfl

/-- Negate a bit under the head; leave a blank cell blank. -/
def flipBit (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  ifₜ tape =ₜ some true then
    tape ←ₜ some false
  else
    ifₜ tape =ₜ some false then
      tape ←ₜ some true
    else
      tape ←ₜ none

/-- Negating a cell preserves its position and costs zero head moves and zero new cells. -/
theorem flipBit_correct (s : TMState tm) :
    Runs (flipBit tm) s (s.config.BiTape.write (s.config.BiTape.head.map Bool.not))
      s.headPos 0 := by
  refine ⟨0, s.write (s.config.BiTape.head.map Bool.not), ?_, rfl, rfl, rfl⟩
  unfold flipBit
  apply Completes.branch
  cases h : s.config.BiTape.head with
  | none =>
    simp only [TMCondition.eval, h, reduceCtorEq, decide_false, Bool.false_eq_true,
      ↓reduceIte, Option.map_none]
    apply Completes.branch
    simpa [h] using completes_write s none
  | some bit =>
    cases bit with
    | false =>
      simp only [TMCondition.eval, h, Option.map_some, Bool.not_false]
      apply Completes.branch
      simpa [h] using completes_write s (some true)
    | true => simpa [h] using completes_write s (some false)

end Algolean.Algorithms.SingleTapeTuringMachines
