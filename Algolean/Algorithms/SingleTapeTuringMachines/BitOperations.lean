/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch

/-!
# Flipping the bit under the head

The Turing machine program `flipBit` exchanges `true` and `false` under the head and leaves a blank
cell blank. It preserves all other cells, the control state, and the head position. Its tests and
writes take execution steps but use no head moves or additional tape cells.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
This Turing machine program changes `true` to `false` and `false` to `true` under the head.
It leaves a blank cell blank and never moves the head.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def flipBit (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  ifₜ tape =ₜ some true then
    tape ←ₜ some false
  else
    ifₜ tape =ₜ some false then
      tape ←ₜ some true
    else
      tape ←ₜ none

/--
The program changes only the bit under the head and leaves a blank cell blank. It preserves the
head position and control state and uses no head moves or additional tape cells.
-/
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
