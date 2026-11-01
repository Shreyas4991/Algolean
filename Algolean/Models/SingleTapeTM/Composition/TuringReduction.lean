/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Oracle
public import Algolean.Complexity.PolytimeBasicClasses

/-!
# Solving one problem by asking questions about another

This file describes Turing reductions with polynomial time bounds. A fixed tape program solves
one yes/no problem using an assumed solver for another. The solver is called an oracle. The
program may ask several questions, and earlier answers may determine later questions.

[OracleInterface](##Algolean.Algorithms.OracleInterface) explains how a program asks a question
and receives its answer. Each request and each head move costs one time step; the oracle's own
work is outside this count. The program must finish for every input within a polynomial time
bound and with enough fuel to complete execution.

## Main definitions and results

* [languageOracle](##Algolean.Algorithms.languageOracle) gives the correct answers for a
  specified problem.
* [DecidesWithin](##Algolean.Algorithms.OracleInterface.DecidesWithin) requires termination with
  the correct answer within the time bound.
* [TuringReduction](##Algolean.Algorithms.TuringReduction) stores one program, its polynomial
  bound, and its correctness proof.
* [TuringReducible](##Algolean.Algorithms.TuringReducible) states that such a reduction exists.
* [TuringReduction.refl](##Algolean.Algorithms.TuringReduction.refl) reduces a problem to itself
  with one oracle question.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing Polynomial TMQuery

/--
This function gives the correct yes or no answer for every input to the specified problem. It
describes the oracle's answers without requiring an algorithm for finding them.
-/
noncomputable def languageOracle (language : Language Bool) (input : List Bool) : Bool :=
  @decide (language input) (Classical.propDecidable _)

/-- The oracle returns true exactly when the problem's answer is yes. -/
@[simp] theorem languageOracle_eq_true (language : Language Bool) (input : List Bool) :
    languageOracle language input = true ↔ language input := by
  simp [languageOracle]

/--
The program finishes in a yes or no state within the allowed time, and its answer agrees with
the required answer. The supplied solver answers any requests during execution.
-/
def OracleInterface.DecidesWithin {tm : SingleTapeTM Bool} [DecidableEq tm.State]
    (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (program : Prog (TMQuery tm) Unit) (input : List Bool) (accept : Prop) (time : ℕ) : Prop :=
  ∃ fuel result final, interface.execute oracle fuel program (TMState.init tm input) =
      some (result, final) ∧
    (final.machine.config.state = some interface.yes ∨
      final.machine.config.state = some interface.no) ∧
    (final.machine.config.state = some interface.yes ↔ accept) ∧ result.tell.steps ≤ time

/--
One fixed program solves the source problem using a solver for the target problem. Its head
moves and requests together have a polynomial time bound.
-/
structure TuringReduction (source target : Language Bool) where
  /-- This machine supplies the named states and the starting state. -/
  tm : SingleTapeTM Bool
  /-- This field supplies a way to check whether two machine states are equal. -/
  [stateDecidableEq : DecidableEq tm.State]
  /--
  This interface selects the request, yes, and no states described by
  [OracleInterface](##Algolean.Algorithms.OracleInterface).
  -/
  interface : OracleInterface tm
  /--
  The same program runs on every input and may use earlier answers to choose later questions.
  -/
  program : Prog (TMQuery tm) Unit
  /--
  This polynomial bounds the total number of head moves and requests in terms of input length.
  -/
  poly : Polynomial ℕ
  /--
  The program finishes within the time bound and answers the source problem correctly whenever the
  solver answers the target problem correctly.
  -/
  correct : ∀ input, interface.DecidesWithin (languageOracle target) program input
    (source input) (poly.eval input.length)

/-- A [TuringReduction](##Algolean.Algorithms.TuringReduction) exists between the two problems. -/
def TuringReducible (source target : Language Bool) : Prop :=
  Nonempty (TuringReduction source target)

namespace TuringReduction

/-- This machine has three states, enough to issue a request and record either answer. -/
abbrev identityControl : SingleTapeTM Bool where
  State := Fin 3
  q₀ := 2
  tr _ symbol := (⟨symbol, none⟩, none)

/-- State 0 issues a request, state 1 records yes, and state 2 records no. -/
def identityInterface : OracleInterface identityControl where
  request := 0
  yes := 1
  no := 2
  request_ne_yes := by decide
  request_ne_no := by decide
  yes_ne_no := by decide

/--
A problem reduces to itself by asking its oracle about the unchanged input. This program makes
one request and costs one time step.
-/
noncomputable def refl (language : Language Bool) : TuringReduction language language where
  tm := identityControl
  stateDecidableEq := inferInstanceAs (DecidableEq (Fin 3))
  interface := identityInterface
  program := identityInterface.ask
  poly := 1
  correct input := by
    let s := TMState.init identityControl input
    let answer :=
      if languageOracle language input then identityInterface.yes else identityInterface.no
    refine ⟨1, ⟨(), ⟨1, 0⟩⟩, ⟨{s with config.state := some answer}, 0⟩, ?_, ?_, ?_, ?_⟩
    · have hquery : OracleInterface.queryWord s.config.BiTape = input :=
        OracleInterface.queryWord_mk₁ input
      rw [OracleInterface.execute_ask_succ _ _ 0 s, hquery]
    · by_cases h : language input <;> simp [answer, languageOracle, h]
    · by_cases h : language input <;> simp [answer, languageOracle, h, identityInterface]
    · simp

end TuringReduction

/-- Every problem has a Turing reduction to itself. -/
theorem TuringReducible.refl (language : Language Bool) : TuringReducible language language :=
  ⟨TuringReduction.refl language⟩

end Algolean.Algorithms
