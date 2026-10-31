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
