/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Checking the fixed-program correctness interface

These examples require both language deciders and function computations to leave clean output. They
also check that space includes the initial head cell and that conversion to computation
records preserves the program and time bound.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMSolves

open Algolean.Algorithms Cslib Cslib.Turing TMQuery
open scoped TMQuery

/-- This machine has one control state and a Boolean tape alphabet. -/
abbrev machine : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This fixed program writes true under the head and leaves every other cell unchanged. -/
def writeTrue : Prog (TMQuery machine) Unit := do [TMQuery machine]
  tape ←ₜ some true

/--
Leaving the input unchanged decides whether it equals the fixed acceptance word. Every result
is a complete clean word; rejection need not use a single predetermined word.
-/
theorem identity_decides :
    DecidesWithin (pure () : Prog (TMQuery machine) Unit) {[true]} [true]
      (fun _ => 0) (fun n => max 1 n) := by
  intro input
  refine ⟨input, 0, TMState.init machine input, completes_pure _, rfl, ?_, by simp, ?_⟩
  · rfl
  · exact (TMState.spaceUsed_init machine input).le

/--
Writing true under the head does not compute the constant one-symbol output function: on a
two-symbol input, the second cell remains occupied. Larger resource bounds do not change this.
-/
theorem writeTrue_not_constant_computation (time space : ℕ → ℕ) :
    ¬ComputesWithin writeTrue (fun _ => [true]) time space := by
  intro h
  obtain ⟨cost, final, hc, ht, _⟩ :=
    (OutputsWithinTime.iff_completes (program := writeTrue)).mp
      (h.outputsWithinTime [false, false])
  have hfinal := (hc.unique (completes_write (TMState.init machine [false, false]) (some true))).2
  rw [hfinal] at ht
  have hright := congrArg (fun tape : BiTape Bool => tape.right.head) ht
  change some false = none at hright
  cases hright

/-- A true symbol with leftover input does not satisfy the clean-output decision convention. -/
theorem writeTrue_not_decides (time space : ℕ → ℕ) :
    ¬DecidesWithin writeTrue Set.univ [true] time space := by
  intro h
  apply writeTrue_not_constant_computation time space
  apply h.consequence
  intro input output houtput
  exact houtput.mpr (Set.mem_univ input)

/-- Even an empty input requires one tape cell, so a zero total space bound is impossible. -/
theorem not_zero_space (program : Prog (TMQuery machine) Unit)
    (spec : List Bool → Set (List Bool)) (time : ℕ → ℕ) :
    ¬TMSolves machine program spec time (fun _ => 0) := by
  intro h
  have := h.space_lower_bound []
  simp at this

/-- Converting to the common interface and back retains exactly the original program. -/
example {f : List Bool → List Bool} (computer : TimeComputable f) :
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    computer.computesWithin.timeComputable.program = computer.program := rfl

/-- The same conversions retain the original time-bound function. -/
example {f : List Bool → List Bool} (computer : TimeComputable f) :
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    computer.computesWithin.timeComputable.timeBound = computer.timeBound := rfl

end AlgoleanTests.SingleTapeTMSolves
