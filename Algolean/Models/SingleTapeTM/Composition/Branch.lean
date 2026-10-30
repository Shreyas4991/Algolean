/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic

/-!
# Branch composition of single-tape query procedures
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A branch executes only its selected procedure. -/
theorem Completes.branch {condition : TMCondition tm} {yes no : Prog (TMQuery tm) Unit}
    {s t : TMState tm} {cost : TMCost}
    (h : Completes (if condition.eval s.config then yes else no) s cost t) :
    Completes (branch condition yes no) s cost t := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  split at h <;> simp_all


end TMQuery

end Algolean.Algorithms
