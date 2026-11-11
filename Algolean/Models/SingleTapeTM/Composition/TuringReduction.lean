/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Oracle
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing
public import Algolean.Problems.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Solving one problem by asking questions about another

This file describes Turing reductions with polynomial time bounds. A fixed tape program solves
one yes/no problem using an assumed solver for another. Both problems and the reduction machine
use the same fixed finite alphabet. The solver is called an oracle. The program may ask several
questions, and earlier answers may determine later questions.

[OracleInterface](##Algolean.Algorithms.OracleInterface) explains how a program asks a question
and receives its answer. Each request and each head move costs one time step; the oracle's own
work is outside this count. The program must finish for every input within a polynomial time
bound and with enough fuel to complete execution.
Its final tape contains a complete answer word, with the head at its first cell and blanks
outside the word. The acceptance word is fixed for the reduction, following CSLib's convention.

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

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
This function gives the correct yes or no answer for every input to the specified problem. It
describes the oracle's answers without requiring an algorithm for finding them.
-/
noncomputable def languageOracle (language : Language Symbol) (input : List Symbol) : Bool :=
  @decide (input ∈ language) (Classical.propDecidable _)

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The oracle returns true exactly when the problem's answer is yes. -/
@[simp] theorem languageOracle_eq_true (language : Language Symbol) (input : List Symbol) :
    languageOracle language input = true ↔ input ∈ language := by
  simp [languageOracle]

/--
The program finishes with a clean output word within the allowed time. Its output equals the
fixed acceptance word exactly when the required answer is yes. The oracle answers any requests
during execution; its intermediate answers may still be recorded in control states.
-/
def OracleInterface.DecidesWithin {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State]
    (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (program : Prog (TMQuery tm) Unit) (input acceptWord : List Symbol)
    (accept : Prop) (time : ℕ) : Prop :=
  ∃ output fuel result final, interface.execute oracle fuel program (TMState.init tm input) =
      some (result, final) ∧
    final.machine.config.BiTape = BiTape.mk₁ output ∧
    (output = acceptWord ↔ accept) ∧ result.tell.steps ≤ time

/--
One fixed program solves the source problem using a solver for the target problem. Its head
moves and requests together have a polynomial time bound. The source inputs, oracle queries,
and machine tape all use the same alphabet `Symbol`. Oracle requests record their answers in
control states. The complete program writes its final answer as a clean word. Even a one-symbol
alphabet permits two different answer words, such as an empty word and a one-symbol word.
-/
structure TuringReduction (source target : Language Symbol) where
  /-- This machine fixes the named states and the starting state. -/
  tm : SingleTapeTM Symbol
  /-- This field defines a way to check whether two tape symbols are equal. -/
  [symbolDecidableEq : DecidableEq Symbol]
  /-- This field defines a way to check whether two machine states are equal. -/
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
  /-- The final output equals this fixed word exactly on inputs in the source language. -/
  acceptWord : List Symbol
  /--
  This polynomial bounds the total number of head moves and requests in terms of input length.
  -/
  poly : Polynomial ℕ
  /--
  The program finishes within the time bound and answers the source problem correctly whenever the
  solver answers the target problem correctly.
  -/
  correct : ∀ input, interface.DecidesWithin (languageOracle target) program input acceptWord
    (input ∈ source) (poly.eval input.length)

/-- A [TuringReduction](##Algolean.Algorithms.TuringReduction) exists between the two problems. -/
def TuringReducible (source target : Language Symbol) : Prop :=
  Nonempty (TuringReduction source target)

namespace TuringReduction

open SingleTapeTuringMachines
open scoped TMQuery

section Cleanup

variable [DecidableEq Symbol] {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private theorem eraseRight_step (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (fuel : Nat) (s : TMState tm) (hhead : s.config.BiTape.head ≠ none) :
    interface.execute oracle (fuel + 3) (eraseRight tm) s =
      (interface.execute oracle fuel (eraseRight tm) ((s.write none).move .Right)).map
        (fun (result, final) => (⟨result.ret, s.moveCost .Right + result.tell⟩, final)) := by
  simp only [OracleInterface.execute,
    FuelExecMonad.execute_eq_run (I := interface.interpreter oracle)]
  change (interface.interpreter oracle).run (fuel + 1 + 1 + 1)
    (.liftBind (.whileCode (.not (.tapeIs none)) [.write none, .move .Right]) pure) s = _
  rw [FuelExecMonad.Interpreter.run]
  simp only [OracleInterface.interpreter, OracleInterface.step, TMQuery.step,
    TMCondition.eval, hhead, decide_false, Bool.not_false, ite_true]
  change ((interface.interpreter oracle).run (fuel + 1 + 1)
    (.liftBind (.write none) (fun _ => .liftBind (.move .Right) (fun _ => eraseRight tm))) s).bind
      (fun x => some ((⟨x.1.ret, 0 + x.1.tell⟩ : AddWriter TMCost Unit), x.2)) = _
  simp only [FuelExecMonad.Interpreter.run, OracleInterface.interpreter, OracleInterface.step,
    TMQuery.step]
  simp only [TMState.move, TMState.write, Dir.offset]
  generalize ((interface.interpreter oracle).run fuel (eraseRight tm)
    {s with
      config := {s.config with BiTape := (s.config.BiTape.write none).moveRight}
      headPos := s.headPos + 1
      cellsAllocated := insert (s.headPos + 1) s.cellsAllocated
      cellsVisited := insert (s.headPos + 1) s.cellsVisited}) = execution
  rcases execution with _ | ⟨⟨u, cost⟩, final⟩
  · rfl
  · simp [TMState.moveCost]
    rfl


private theorem eraseRight_execution (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (word : List Symbol) (s : TMState tm) (htape : s.config.BiTape = cursor [] word) :
    ∃ cost final, interface.execute oracle (3 * word.length + 1) (eraseRight tm) s =
      some (⟨(), cost⟩, ⟨final, 0⟩) ∧ final.config.BiTape = BiTape.nil ∧
      final.config.state = s.config.state ∧ cost.steps = word.length := by
  induction word generalizing s with
  | nil =>
    refine ⟨0, s, ?_, ?_, rfl, rfl⟩
    · simp only [OracleInterface.execute,
        FuelExecMonad.execute_eq_run (I := interface.interpreter oracle)]
      change (interface.interpreter oracle).run 1
        (.liftBind (.whileCode (.not (.tapeIs none)) [.write none, .move .Right]) pure) s = _
      simp [FuelExecMonad.Interpreter.run, OracleInterface.interpreter, OracleInterface.step,
        TMQuery.step, htape, cursor, -FreeM.liftBind_eq]
      rfl
    · simpa using htape
  | cons symbol rest ih =>
    let middle := (s.write none).move .Right
    have hmiddle : middle.config.BiTape = cursor [] rest := by
      simp [middle, TMState.move, TMState.write, htape, cursor, BiTape.write, BiTape.moveRight]
    obtain ⟨cost, final, hrun, ht, hs, hc⟩ := ih middle hmiddle
    refine ⟨s.moveCost .Right + cost, final, ?_, ht, ?_, ?_⟩
    · rw [show 3 * (symbol :: rest).length + 1 = (3 * rest.length + 1) + 1 + 1 + 1 by simp; lia]
      rw [eraseRight_step interface oracle _ s (by simp [htape])]
      simp [hrun, middle]
    · simpa [middle, TMState.move, TMState.write] using hs
    · simp [TMState.moveCost, hc, Nat.add_comm]

end Cleanup


/-- This machine has three states, enough to issue a request and record either answer. -/
abbrev identityControl (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] :
    SingleTapeTM Symbol where
  State := Fin 3
  q₀ := 2
  tr _ symbol := (⟨symbol, none⟩, none)

/-- State 0 issues a request, state 1 records yes, and state 2 records no. -/
def identityInterface (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] :
    OracleInterface (identityControl Symbol) where
  request := 0
  yes := 1
  no := 2
  request_ne_yes := (by decide : (0 : Fin 3) ≠ 1)
  request_ne_no := (by decide : (0 : Fin 3) ≠ 2)
  yes_ne_no := (by decide : (1 : Fin 3) ≠ 2)

/--
A problem reduces to itself by asking about its input, erasing that input, and writing a
one-symbol word for yes or an empty word for no. It uses one request and one head move per
input symbol. The final head points to the answer, which may lie beyond the original input.
-/
noncomputable def refl (language : Language Symbol) : TuringReduction language language where
  tm := identityControl Symbol
  symbolDecidableEq := Classical.decEq Symbol
  stateDecidableEq := inferInstanceAs (DecidableEq (Fin 3))
  interface := identityInterface Symbol
  program := do [TMQuery (identityControl Symbol)]
    (identityInterface Symbol).ask
    eraseRight (identityControl Symbol)
    ifₜ state =ₜ some (identityInterface Symbol).yes then
      tape ←ₜ some default
    else
      tape ←ₜ none
  acceptWord := [default]
  poly := Polynomial.X + 1
  correct input := by
    classical
    let interface := identityInterface Symbol
    let oracle := languageOracle language
    let s := TMState.init (identityControl Symbol) input
    let answer := if oracle input then interface.yes else interface.no
    let middle := {s with config.state := some answer}
    obtain ⟨cost, final, hrun, htape, hstate, hcost⟩ :=
      eraseRight_execution interface oracle input middle
        (by simp [middle, s, TMState.init, SingleTapeTM.initCfg, cursor_start])
    have hrun' := FuelExecMonad.execute_add_fuel
      (I := interface.interpreter oracle) (3 * input.length + 1) 2
      (eraseRight (identityControl Symbol)) middle ⟨(), cost⟩ ⟨final, 0⟩ hrun
    let output : List Symbol := if oracle input then [default] else []
    let written := if oracle input then some (default : Symbol) else none
    have hfinish : interface.execute oracle 2
        (branch (.stateIs (some interface.yes))
          (FreeM.lift (.write (some default))) (FreeM.lift (.write none))) final =
        some (⟨(), 0⟩, ⟨final.write written, 0⟩) := by
      simp only [OracleInterface.execute,
        FuelExecMonad.execute_eq_run (I := interface.interpreter oracle)]
      change (interface.interpreter oracle).run 2
        (.liftBind (.branchCode (.stateIs (some interface.yes))
          [.write (some default)] [.write none]) pure) final = _
      rw [FuelExecMonad.Interpreter.run]
      have hanswer : decide (final.config.state = some interface.yes) = oracle input := by
        by_cases h : oracle input <;> simp [hstate, middle, answer, h, interface, identityInterface]
      simp only [OracleInterface.interpreter, OracleInterface.step, TMQuery.step,
        TMCondition.eval, hanswer]
      cases h : oracle input <;> simp [h, written]
      all_goals rfl
    refine ⟨output, (3 * input.length + 1 + 2) + 1, ⟨(), ⟨1, 0⟩ + cost⟩,
      ⟨final.write written, 0⟩, ?_, ?_, ?_, ?_⟩
    · have hquery := interface.execute_ask_succ oracle (3 * input.length + 1 + 2) s
      have hqueryWord : OracleInterface.queryWord s.config.BiTape = input := by
        simp [s, TMState.init, SingleTapeTM.initCfg]
      rw [hqueryWord] at hquery
      change interface.execute oracle ((3 * input.length + 1 + 2) + 1) _ s = _
      simp only [OracleInterface.execute, FuelExecMonad.execute_bind] at hquery ⊢
      rw [hquery]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hrun']
      simp only [Option.bind_some]
      simp only [OracleInterface.execute] at hfinish
      rw [hfinish]
      simp
    · by_cases h : oracle input <;> simp [output, written, TMState.write, htape, h, BiTape.mk₁,
        BiTape.nil, BiTape.write, StackTape.mapSome, StackTape.nil]
    · simp [output, oracle, languageOracle]
    · simp [hcost, Nat.add_comm]

end TuringReduction

/-- Every problem has a Turing reduction to itself. -/
theorem TuringReducible.refl (language : Language Symbol) : TuringReducible language language :=
  ⟨TuringReduction.refl language⟩

end Algolean.Algorithms
