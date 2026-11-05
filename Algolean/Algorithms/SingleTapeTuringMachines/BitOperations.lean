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

The Turing machine program `flipBit` changes `true` to `false` and `false` to `true` in the current
tape cell. If the cell is blank, it remains blank. The program uses tests and writes inside the
machine, leaves all other tape cells unchanged, and never moves the head. Its correctness theorem
proves that it preserves the control state and uses zero head moves and zero additional tape cells.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
`flipBit tm` is a Turing machine program that inspects the current cell and replaces an occupied
Boolean value with its negation. A blank cell stays blank. The head remains in place, and no other
cell is changed.
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
Flipping the current cell produces its Boolean negation when occupied and preserves a blank when
empty. The program preserves the head position and control state and uses zero head moves; its
writes do not allocate additional tape cells.
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
