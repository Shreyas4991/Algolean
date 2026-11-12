/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Formula
public import Mathlib.Tactic.FinCases

/-!
# Checking clauses and bounded computation descriptions

These examples check repeated variable names, empty choices, early halting, and movement at
the edge of the recorded tape. They also distinguish writing an accepting symbol from halting
with that symbol under the head after a movement.
The complete CNF construction is also checked against these acceptance conventions.
-/

open Cslib.Turing.SingleTapeTM

@[expose] public section

namespace AlgoleanTests.NPToSATFormula

open Algolean.Problems.SAT Cslib.Turing.SingleTapeTM.BoundedVerification
open Algolean.Algorithms.NPToTMSAT Cslib.Turing

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
private def earlyHaltProblem : BoundedVerification Bool := ⟨writeAndHalt, [], 0, 3⟩

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
  rw [mem_accepted_iff_exists_computation]
  refine ⟨earlyHaltComputation, ?_⟩
  rw [Computation.Accepting, ← Row.toCfg_mem_accepting]
  exact ⟨rfl, rfl⟩

/-- The complete CNF formula remains satisfiable when acceptance happens before the time bound. -/
example : formula earlyHaltProblem true ∈ CNF.satisfiable := by
  rw [formula_satisfiable_iff, mem_accepted_iff_exists_computation]
  refine ⟨earlyHaltComputation, ?_⟩
  rw [Computation.Accepting, ← Row.toCfg_mem_accepting]
  exact ⟨rfl, rfl⟩

/-- The complete formula is unsatisfiable when there is no time for the first transition. -/
example : formula (⟨writeAndHalt, [], 0, 0⟩ : BoundedVerification Bool) true ∉ CNF.satisfiable := by
  rw [formula_satisfiable_iff]
  simp

/-- The final clauses reject a halted accepting head when a separator remains on the tape. -/
example : formula (⟨writeAndHalt, [true], 0, 1⟩ : BoundedVerification Bool) true ∉ CNF.satisfiable := by
  rw [formula_satisfiable_iff, mem_satisfiable_zero_length]
  intro h
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff true _ _).mp h
  have hright := congrArg (fun result => result.map (fun cfg => cfg.BiTape.right.head)) hstep
  rw [Option.map_some, congrArg (fun tape => tape.right.head) hfinal.2] at hright
  simp [SingleTapeTM.Description.machine, writeAndHalt, SingleTapeTM.initCfg,
    Algolean.Algorithms.Alphabet.wordPair_encode, BiTape.mk₁, BiTape.optionMove,
    BiTape.write, StackTape.mapSome, StackTape.head] at hright

/-- Writing true does not make the formula satisfiable when the head then halts over false. -/
example : formula (⟨writeThenMove, [false, false], 0, 1⟩ : BoundedVerification Bool) true ∉
    CNF.satisfiable := by
  rw [formula_satisfiable_iff, mem_satisfiable_zero_length]
  intro h
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff true _ _).mp h
  have hhead := congrArg (fun result => result.map (fun cfg => cfg.BiTape.head)) hstep
  rw [Option.map_some, congrArg BiTape.head hfinal.2] at hhead
  simp [SingleTapeTM.Description.machine, writeThenMove, SingleTapeTM.initCfg,
    Algolean.Algorithms.Alphabet.wordPair_encode, BiTape.mk₁, BiTape.optionMove,
    BiTape.move, BiTape.moveRight, BiTape.write, StackTape.head, StackTape.mapSome] at hhead

/-- This verifier uses one ordinary symbol and accepts by writing that symbol and halting. -/
private def unaryAccept : SingleTapeTM.Description (TapeSymbol Unit) where
  states := 0
  initial := 0
  transition _ _ := (some (.inl ()), none, none)

/-- A verifier over a one-symbol alphabet still gives a satisfiable formula when it accepts. -/
example : formula (⟨unaryAccept, [], 0, 1⟩ : BoundedVerification Unit) () ∈ CNF.satisfiable := by
  rw [formula_satisfiable_iff, mem_satisfiable_zero_length]
  apply (acceptsWithin_one_iff () _ _).mpr
  exact ⟨⟨none, (BiTape.mk₁ _).write (some (.inl ()))⟩, ⟨rfl, rfl⟩, rfl⟩

/-- Even an immediately accepting verifier has no accepting description with zero transitions. -/
example : ¬∃ computation : Computation (⟨writeAndHalt, [], 0, 0⟩ : BoundedVerification Bool),
    computation.Accepting true := by
  rw [← mem_accepted_iff_exists_computation]
  simp

end AlgoleanTests.NPToSATFormula
