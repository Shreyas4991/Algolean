/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Constraints
public import Algolean.Complexity.Reductions.TMSATToSAT.Computation
public import Mathlib.Tactic.FinCases

/-!
# Checking clauses and bounded computation descriptions

These examples check repeated variable names, empty choices, early halting, and movement at
the edge of the recorded tape. They also distinguish writing an accepting symbol from halting
with that symbol under the head after a movement.
-/

@[expose] public section

namespace AlgoleanTests.TMSATToSAT

open Algolean.Problems.SAT Algolean.Problems.TMSAT
open Algolean.Algorithms.TMSATToSAT Cslib.Turing

/-- Listing the same variable twice still permits choosing it as the one true variable. -/
example : CNF.eval (CNF.exactlyOne ([0, 0, 1] : List Nat)) (fun name => name == 0) = true := by
  decide +kernel

/-- Two different chosen variables violate the requirement that exactly one be true. -/
example : CNF.eval (CNF.exactlyOne ([0, 0, 1] : List Nat)) (fun _ => true) = false := by
  decide +kernel

/-- There is no possible choice when the list is empty. -/
theorem empty_choice_unsatisfiable : CNF.exactlyOne ([] : List Bool) ∉ CNF.satisfiable := by
  simp [CNF.satisfiable]

/-- An implication with no premises requires its conclusion to be true. -/
example : Clause.eval (Clause.implies [] (0 : Nat)) (fun _ => false) = false := by
  decide +kernel

/-- Requiring a variable to imply itself allows either truth value. -/
example (value : Bool) : Clause.eval (Clause.implies [()] ()) (fun _ => value) = true := by
  cases value <;> decide +kernel

/-- This machine writes true, moves right, and halts in the same transition. -/
private def writeThenMove : SingleTapeTM.Description (TapeSymbol Bool) where
  states := 0
  initial := 0
  transition _ _ := (some (.inl true), some true, none)

/-- The three recorded cells are blank, blank under the head, and false to its right. -/
private def beforeMove : Row writeThenMove 3 where
  state := some 0
  left := [none]
  symbol := none
  right := [some (.inl false)]
  length_eq := rfl

/-- The written true moves to the left of the head, which halts over the existing false symbol. -/
example : beforeMove.step.map (fun row => (row.state, row.symbol, row.left, row.right)) =
    some (none, some (.inl false), [some (.inl true), none], []) := rfl

/-- Moving right past the last recorded cell fails, including when the transition would halt. -/
example : (Row.step (verifier := writeThenMove)
    ⟨some 0, [], none, [], by rfl⟩ : Option (Row writeThenMove 1)) = none := rfl

/-- A halted row is repeated without performing the verifier's write or movement. -/
example : (Row.step (verifier := writeThenMove)
    ⟨none, [], some (.inl false), [], by rfl⟩ : Option (Row writeThenMove 1)) =
      some ⟨none, [], some (.inl false), [], by rfl⟩ := rfl

/-- This machine writes true and halts without moving its head. -/
private def writeAndHalt : SingleTapeTM.Description (TapeSymbol Bool) where
  states := 0
  initial := 0
  transition _ _ := (some (.inl true), none, none)

/-- This instance allows three transitions even though its verifier halts after the first. -/
private def earlyHaltProblem : Instance Bool := ⟨writeAndHalt, [], 0, 3⟩

/-- The first transition accepts, and the next two rows repeat that same halted configuration. -/
private def earlyHaltComputation : Computation earlyHaltProblem where
  certificate := ⟨[], rfl⟩
  rows i :=
    let first := initialRow earlyHaltProblem ⟨[], rfl⟩
    if i.val = 0 then first else {first with state := none, symbol := some (.inl true)}
  initial := rfl
  next i := by fin_cases i <;> rfl

/-- The description with repeated halted rows proves acceptance within the original bound. -/
example : earlyHaltProblem ∈ satisfiable true := by
  rw [mem_satisfiable_iff_exists_computation]
  exact ⟨earlyHaltComputation, ⟨rfl, rfl⟩⟩

/-- Even an immediately accepting verifier has no accepting description with zero transitions. -/
example : ¬∃ computation : Computation (⟨writeAndHalt, [], 0, 0⟩ : Instance Bool),
    computation.Accepting true := by
  rw [← mem_satisfiable_iff_exists_computation]
  simp

end AlgoleanTests.TMSATToSAT
