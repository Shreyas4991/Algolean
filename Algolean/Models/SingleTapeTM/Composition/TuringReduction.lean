/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Oracle
public import Algolean.Complexity.PolytimeBasicClasses

/-!
# Turing reductions

Suppose we want to answer a yes/no question called `source`. A Turing reduction is a machine
program that answers this question with help from another yes/no problem called `target`.

We assume there is a solver for the target problem that always answers correctly in one step.
This assumed solver is called an *oracle*. A reduction is the whole program; it may call this
solver many times. Earlier answers can affect both the next question and whether another
question is needed. The target problem need not have a known program that solves it: the
reduction describes how we could solve the source problem if we had such a solver.

For example, suppose the helper answers "Does this Boolean word contain a true bit?" To check
whether a word contains both true and false bits, first ask about the original word. If the
answer is no, return no. Otherwise, flip every bit and ask again. Return yes exactly when
the second answer is yes.

The same program must work for every input. We use the polynomial-time version here: a formula
such as `n² + 3n + 1` must limit its time on inputs of length `n`. Each tape-head move instruction
and each call to the solver costs one time step. This also bounds the number of calls, but
preparing the questions and processing the answers must fit within the time bound too.
The solver's own work is outside this count. Replacing it with an actual program would add
that program's running time for every call.

In this implementation, a question is the word on the tape starting at the head and ending
at the first blank. The program asks by entering its request state. The interpreter supplies
the helper's answer by putting the machine in its yes or no state. These are state names
the program can test while it runs. Finishing the program in the yes state means its answer
to the source question is yes; finishing in the no state means its answer is no.

The interpreter also has a separate instruction limit called `fuel`. Some finite limit must
let the program finish. Running out of this limit does not count as answering the question.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing Polynomial TMQuery

/-- Describe the assumed helper's answers: `true` means the input's answer is yes.
The interpreter uses this function to supply answers to questions about `language`. -/
noncomputable def languageOracle (language : Language Bool) (input : List Bool) : Bool :=
  @decide (language input) (Classical.propDecidable _)

/-- The helper says yes exactly when the language's question has a yes answer. -/
@[simp] theorem languageOracle_eq_true (language : Language Bool) (input : List Bool) :
    languageOracle language input = true ↔ language input := by
  simp [languageOracle]

/-- The program finishes in a yes or no state within `time` steps. It finishes in the yes state
exactly when `accept` is true. The helper supplies answers to any questions asked along the way. -/
def OracleInterface.DecidesWithin {tm : SingleTapeTM Bool} [DecidableEq tm.State]
    (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (program : Prog (TMQuery tm) Unit) (input : List Bool) (accept : Prop) (time : ℕ) : Prop :=
  ∃ fuel result final, interface.execute oracle fuel program (TMState.init tm input) =
      some (result, final) ∧
    (final.machine.config.state = some interface.yes ∨
      final.machine.config.state = some interface.no) ∧
    (final.machine.config.state = some interface.yes ↔ accept) ∧ result.tell.steps ≤ time

/-- A fixed machine program that answers `source` questions using a helper for `target`,
with a polynomial bound on its head moves and calls to that helper. -/
structure TuringReduction (source target : Language Bool) where
  /-- The machine's states and starting state. Its instructions are stored in `program`. -/
  tm : SingleTapeTM Bool
  /-- How the interpreter checks whether two state names are equal. -/
  [stateDecidableEq : DecidableEq tm.State]
  /-- The state names used to ask a question and record a yes or no answer. -/
  interface : OracleInterface tm
  /-- The same program runs on every input. It may use earlier answers to choose later questions. -/
  program : Prog (TMQuery tm) Unit
  /-- A polynomial limiting head moves plus helper calls as a function of the input length. -/
  poly : Polynomial ℕ
  /-- On every input, the program finishes within the bound and answers the source question
  correctly when the helper answers target questions correctly. -/
  correct : ∀ input, interface.DecidesWithin (languageOracle target) program input
    (source input) (poly.eval input.length)

/-- There is a Turing reduction from `source` to `target`, using the same program
for every input. -/
def TuringReducible (source target : Language Bool) : Prop :=
  Nonempty (TuringReduction source target)

namespace TuringReduction

/-- The three-state machine used to reduce a problem to itself. -/
abbrev identityControl : SingleTapeTM Bool where
  State := Fin 3
  q₀ := 2
  tr _ symbol := (⟨symbol, none⟩, none)

/-- State `0` asks the helper a question, state `1` records yes, and state `2` records no. -/
def identityInterface : OracleInterface identityControl where
  request := 0
  yes := 1
  no := 2
  request_ne_yes := by decide
  request_ne_no := by decide
  yes_ne_no := by decide

/-- Reduce a problem to itself: ask its helper about the unchanged input and return the answer.
This one-question program works for every input and costs one time step in this model. -/
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
