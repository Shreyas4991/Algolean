/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.NP
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Complexity classes using fixed TM query programs

The input varies only in the initial state. Completion, output, and resource bounds are
observed through the interpreter; exhausting fuel does not satisfy the computation relation.
-/

@[expose] public section

namespace AlgoleanTests.PolytimeBasicClasses

open Algolean Algolean.Algorithms Cslib.Turing TMQuery

open scoped TMQuery

/-- A machine with a single control-state label and a Boolean tape alphabet. -/
abbrev machine : SingleTapeTM Bool where
  State := PUnit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- The same closed program computes the identity for every input. -/
@[simp] def identity : Prog (TMQuery machine) Unit := do [TMQuery machine]
  pure ()

/-- Input is supplied only to the initial machine state, and output comes from the final tape. -/
theorem identity_outputs (input : List Bool) : OutputsWithinTime identity input input 0 := by
  exact ⟨0, ⟨(), 0⟩, ⟨TMState.init machine input, 0⟩, rfl, rfl, le_rfl⟩

example (input : List Bool) (time : ℕ) : OutputsWithinTime identity input input time :=
  (identity_outputs input).mono (Nat.zero_le time)

/-- The new polynomial-time witness gives a fixed-program decision procedure for a singleton. -/
theorem singleton_inP (yes : List Bool) : P (fun input => input = yes) := by
  exact ⟨id, yes, ⟨TMQuery.PolyTimeComputable.id⟩, by simp⟩

example (yes : List Bool) : NP (fun input => input = yes) :=
  NP.ofP (singleton_inP yes)

/-- A stationary move is a charged instruction even though it preserves the input tape. -/
@[simp] def stop : Prog (TMQuery machine) Unit := do [TMQuery machine]
  moveₜ .Stop

-- A completed execution with a cost exceeding the bound is not a time-bounded computation.
example (input : List Bool) : ¬OutputsWithinTime stop input input 0 := by
  rintro ⟨fuel, result, final, h, _, htime⟩
  cases fuel <;> simp_all [execute_eq_runCode, runCode, step]
  grind

/-- A closed program that never changes its true loop condition. -/
@[simp] def forever : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some ()) do
    pure ()

/-- No interpreter budget lets the infinite loop complete, on any input. -/
theorem forever_fails (fuel : ℕ) (input : List Bool) :
    execute fuel forever (TMState.init machine input) = none := by
  simp only [execute_eq_runCode, forever, whileLoop, instructions_lift, instructions_pure]
  induction fuel <;> simp_all [runCode, step, TMState.init, SingleTapeTM.initCfg]

-- A loop with no head moves still must terminate to satisfy the relation.
example (input output : List Bool) (time : ℕ) :
    ¬OutputsWithinTime forever input output time := by
  grind [OutputsWithinTime, forever_fails]

end AlgoleanTests.PolytimeBasicClasses
