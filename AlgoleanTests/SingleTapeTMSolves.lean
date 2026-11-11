/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Computability

/-!
# Checking the fixed-program correctness interface

These examples distinguish deciding a language from producing a complete output word. They
also check that space includes the initial head cell and that conversion to computation
records preserves the program and time bound.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMSolves

open Algolean.Algorithms Cslib Cslib.Turing TMQuery

/-- This machine has one control state and a Boolean tape alphabet. -/
abbrev machine : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This fixed program writes true under the head and leaves every other cell unchanged. -/
def writeTrue : Prog (TMQuery machine) Unit := FreeM.lift (.write (some true))

/--
The program decides the language containing every word by leaving true under the head. It may
retain the rest of the input, uses no moves, and needs only the space occupied initially.
-/
theorem writeTrue_decides :
    DecidesWithin writeTrue Set.univ (.tapeIs (some true)) (fun _ => 0) (fun n => max 1 n) := by
  intro input
  let initial := TMState.init machine input
  refine ⟨0, initial.write (some true), completes_write initial (some true), ?_, by simp, ?_⟩
  · simp [TMState.write, BiTape.write]
  · change initial.spaceUsed ≤ _
    exact (TMState.spaceUsed_init machine input).le

/--
Writing true under the head does not compute the constant one-symbol output function: on a
two-symbol input, the second cell remains occupied. Larger resource bounds do not change this.
-/
theorem writeTrue_not_constant_computation (time space : ℕ → ℕ) :
    ¬ComputesWithin writeTrue (fun _ => [true]) time space := by
  intro h
  obtain ⟨cost, final, hc, ht, _, _⟩ := h [false, false]
  have hfinal := (hc.unique (completes_write (TMState.init machine [false, false]) (some true))).2
  rw [hfinal] at ht
  have hright := congrArg (fun tape : BiTape Bool => tape.right.head) ht
  change some false = none at hright
  cases hright

/-- Even an empty input requires one tape cell, so a zero total space bound is impossible. -/
theorem not_zero_space (program : Prog (TMQuery machine) Unit)
    (spec : List Bool → Set machine.Cfg) (time : ℕ → ℕ) :
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
