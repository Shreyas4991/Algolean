/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Sequential

/-!
# While composition of single-tape query procedures
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Exiting a loop consumes a test but no machine cost. -/
theorem completes_while_false (condition : TMCondition tm) (body : Prog (TMQuery tm) Unit)
    (s : TMState tm) (h : condition.eval s.config = false) :
    Completes (whileLoop condition body) s 0 s :=
  ⟨1, by simp [execute_while_succ, h]⟩

/-- Compose one loop iteration with the remaining iterations. -/
theorem Completes.while_step {condition : TMCondition tm} {body : Prog (TMQuery tm) Unit}
    {s t u : TMState tm} {a b : TMCost} (h : condition.eval s.config = true)
    (hb : Completes body s a t) (hr : Completes (whileLoop condition body) t b u) :
    Completes (whileLoop condition body) s (a + b) u := by
  obtain ⟨fuel, hfuel⟩ := hb.seq hr
  exact ⟨fuel + 1, by simpa [execute_while_succ, h] using hfuel⟩


/-- An initially false loop preserves tape, head, and control state. -/
theorem runs_while_false (condition : TMCondition tm) (body : Prog (TMQuery tm) Unit)
    (s : TMState tm) (h : condition.eval s.config = false) :
    Runs (whileLoop condition body) s s.config.BiTape s.headPos 0 :=
  ⟨0, s, completes_while_false _ _ _ h, by cases s.config; rfl, rfl, rfl⟩

/-- Lift a composed iteration contract to the loop it implements. -/
theorem runs_while_step {condition : TMCondition tm} {body : Prog (TMQuery tm) Unit}
    {s : TMState tm} {outputTape : BiTape Symbol} {pos : ℤ} {time : ℕ}
    (h : condition.eval s.config = true)
    (hr : Runs (do body; whileLoop condition body) s outputTape pos time) :
    Runs (whileLoop condition body) s outputTape pos time := by
  obtain ⟨cost, final, ⟨fuel, hfuel⟩, hc, hp, ht⟩ := hr
  exact ⟨cost, final, ⟨fuel + 1, by simpa [execute_while_succ, h] using hfuel⟩, hc, hp, ht⟩


end TMQuery

end Algolean.Algorithms
