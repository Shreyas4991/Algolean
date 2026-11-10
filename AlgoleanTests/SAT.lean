/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Verification
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Parsing
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Lookup
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Evaluation
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier
public meta import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Parsing
public meta import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Lookup
public meta import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Evaluation
public meta import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier
public meta import Algolean.Models.SingleTapeTM.Alphabet.Pair
public meta import Algolean.Problems.SAT.Encoding

/-!
# Checking SAT encodings and certificates

* The flat alphabet uses six markers with distinct roles.
* Empty formulas and empty clauses retain their different meanings.
* Malformed words are rejected, including words with trailing data.
* Certificates use one assignment consistently across all clauses.
* The Turing machine rejects unfinished inputs and trailing data without changing the tape.
* Variable lookup compares complete names, uses the first listed value, and restores every symbol.
* Formula evaluation leaves only its answer on the tape and puts the head on that answer.
* The complete verifier rejects malformed inputs and checks correctly written pairs.
-/

@[expose] public section

namespace AlgoleanTests.SAT

open Algolean.Problems.SAT

-- An empty formula consists of its end marker.
example : encoding.encode [] = [(.inr 5 : CodeSymbol)] := by decide +kernel

-- An empty clause has a clause end, a clause separator, and a formula end.
example : encoding.encode [[]] = [(.inr 3 : CodeSymbol), .inr 4, .inr 5] := by decide +kernel

-- Markers zero and one are signs. Marker two ends a literal; markers three to five frame clauses.
example : encoding.encode [[.pos [false, true], .neg [true]]] =
    [(.inr 0 : CodeSymbol), .inl false, .inl true, .inr 2, .inr 1, .inl true,
      .inr 2, .inr 3, .inr 4, .inr 5] := by decide +kernel

-- The formula decoder rejects a missing end marker.
example : encoding.decode [] = none := by decide +kernel

-- Data after the formula end is rejected.
example : encoding.decode [(.inr 5 : CodeSymbol), .inl true] = none := by decide +kernel

-- Every formula survives encoding and decoding, including all binary variable names.
example (formula : CNF Variable) : encoding.decode (encoding.encode formula) = some formula := by
  simp

-- An empty assignment suffices for the empty conjunction.
example : verify (encoding.encode []) (certificateEncoding.encode []) = true := by decide +kernel

-- No assignment satisfies an empty clause.
example (certificate : List CodeSymbol) : verify (encoding.encode [[]]) certificate = false := by
  cases hc : certificateEncoding.decode certificate <;>
    simp [verify, hc, CNF.eval, Clause.eval]

-- Contradictory entries cannot give the same variable different values in different clauses.
example : verify (encoding.encode [[.pos [true]], [.neg [true]]])
    (certificateEncoding.encode [.pos [true], .neg [true]]) = false := by decide +kernel

-- Distinct binary words name distinct variables, even when one begins with an extra zero.
example : verify (encoding.encode [[.pos [true]], [.neg [false, true]]])
    (certificateEncoding.encode [.pos [true], .neg [false, true]]) = true := by decide +kernel

/-- Every satisfiable formula word has an accepted certificate no longer than that word. -/
theorem certificate_exists (word : List CodeSymbol) (h : word ∈ language) :
    ∃ certificate : List CodeSymbol,
      certificate.length ≤ word.length ∧ verify word certificate = true :=
  (certificate_characterization word).mp h

open Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Algolean.Algorithms.SingleTapeTuringMachines.SAT
open Cslib.Turing

/-- This compares every represented tape cell and the head position before and after execution. -/
private def sameTapeAndHead {tm : SingleTapeTM Symbol} (initial final : TMState tm) : Bool :=
  decide (initial.config.BiTape.head = final.config.BiTape.head ∧
    initial.config.BiTape.left.toList = final.config.BiTape.left.toList ∧
    initial.config.BiTape.right.toList = final.config.BiTape.right.toList ∧
    initial.headPos = final.headPos)

/-- This executes the format checker and checks its answer, unchanged tape, and exact move count. -/
private def checkFormatRun (word : List Symbol) (expected : Bool) : Bool :=
  let initial := TMState.init formatMachine word
  match TMQuery.execute 50000 checkFormat initial with
  | none => false
  | some (result, final) =>
    (decide (final.machine.config.state = some .inputEnd) == expected) &&
      sameTapeAndHead initial final.machine && decide (result.tell.steps = 2 * word.length + 2)

/-- These runs check the format itself, including correctly written unsatisfiable formulas. -/
private def testFormat : IO Unit := do
  let emptyPair := (Alphabet.wordPair CodeSymbol).encode
    (encoding.encode [], certificateEncoding.encode [])
  let cases : List (List Symbol × Bool) := [
    ([], false),
    (emptyPair, true),
    ((Alphabet.wordPair CodeSymbol).encode (encoding.encode [[]], certificateEncoding.encode []),
      true),
    ((Alphabet.wordPair CodeSymbol).encode
      (encoding.encode [[.pos [], .neg [false, true]]], certificateEncoding.encode []), true),
    (emptyPair ++ [digit true], false),
    (emptyPair.dropLast, false),
    ([certificateSeparator, clauseEnd], false),
    ([formulaEnd, clauseEnd], false),
    (emptyPair ++ [certificateSeparator], false),
    ([positiveSign, formulaEnd, certificateSeparator, clauseEnd], false),
    ([clauseEnd, formulaEnd, certificateSeparator, clauseEnd], false)]
  for ((word, expected), index) in cases.zipIdx do
    unless checkFormatRun word expected do
      throw (IO.userError s!"Format checker case {index} failed.")

run_cmd Lean.Elab.Command.liftIO testFormat

/--
This executes lookup from the supplied coordinate and an arbitrary incoming state. It checks the
returned value, every restored tape cell, the restored head position, and the cubic move bound.
-/
private def checkLookupRun (name : Variable) (certificate : Certificate) (expected : Bool)
    (origin : ℤ := 0) : Bool :=
  let word := name.map digit ++ nameEnd :: certificateSeparator ::
    (certificateEncoding.encode certificate).map Sum.inl
  let initial : TMState Lookup.machine :=
    {config := ⟨some (.value true), cursor [] word⟩, headPos := origin}
  match TMQuery.execute 50000 Lookup.lookup initial with
  | none => false
  | some (result, final) =>
    decide (final.machine.config.state = some (.value expected)) &&
      sameTapeAndHead initial final.machine &&
        decide (result.tell.steps ≤ 19 * (word.length + 1) ^ 3)

/-- These runs distinguish empty names, proper prefixes, missing names, and repeated assignments. -/
private def testLookup : IO Unit := do
  let cases : List (Variable × Certificate × Bool) := [
    ([], [], false),
    ([], [.neg []], false),
    ([], [.pos [], .neg []], true),
    ([false], [.neg [true], .pos [false]], true),
    ([false, true], [.pos [false]], false),
    ([false], [.pos [false, true], .neg [false]], false),
    ([false], [.pos [false, true], .pos [false]], true),
    ([false, true], [.pos [false], .neg [false, true]], false),
    ([true], [.neg [true], .pos [true]], false),
    ([true, false], [.pos [true], .neg [false, true], .pos [true, false]], true)]
  for ((name, certificate, expected), index) in cases.zipIdx do
    unless checkLookupRun name certificate expected do
      throw (IO.userError s!"Variable lookup case {index} failed.")
  unless checkLookupRun [false, true] [.pos [false, true]] true 37 do
    throw (IO.userError "Variable lookup failed when started at coordinate 37.")

run_cmd Lean.Elab.Command.liftIO testLookup

/--
This runs the evaluator from a chosen coordinate with an incoming state that records false.
It checks the expected answer, that all other tape cells are blank, that the head has moved to
one cell past the original input, and that the number of head moves satisfies the proved bound.
-/
private def checkEvaluationRun (formula : CNF Variable) (certificate : Certificate)
    (expected : Bool) (origin : ℤ := 0) : Bool :=
  let input := verifierEncoding.encode (formula, certificate)
  let initial : TMState Evaluation.machine :=
    {config := ⟨some (.inr .unsatisfied), BiTape.mk₁ input⟩, headPos := origin}
  match TMQuery.execute 100000 Evaluation.evaluate initial with
  | none => false
  | some (result, final) =>
    decide (final.machine.config.BiTape.head = some (digit expected)) &&
      decide (final.machine.config.BiTape.left.toList = []) &&
      decide (final.machine.config.BiTape.right.toList = []) &&
      decide (final.machine.headPos = origin + input.length) &&
      decide (result.tell.steps ≤ 25 * (input.length + 1) ^ 4)

/--
These runs check empty formulas, empty clauses, negation, and clauses that stop at a true literal.
They also check that every clause uses the same assignment, that missing values mean false, and
that the first listed value takes precedence when a certificate repeats a variable.
-/
private def testEvaluation : IO Unit := do
  let cases : List (CNF Variable × Certificate × Bool) := [
    ([], [], true),
    ([], [.pos [true]], true),
    ([[]], [], false),
    ([[], [.pos [true]]], [.pos [true]], false),
    ([[.pos [true]], []], [.pos [true]], false),
    ([[.pos []]], [.pos []], true),
    ([[.pos [true]]], [], false),
    ([[.neg [true]]], [], true),
    ([[.neg [true]]], [.pos [true]], false),
    ([[.pos [false], .pos [true]], [.neg [true]]], [.pos [false]], true),
    ([[.pos [true]], [.neg [true]]], [.pos [true], .neg [true]], false),
    ([[.pos [true]]], [.neg [true], .pos [true]], false),
    ([[.pos [true]], [.neg [false, true]]], [.pos [true], .neg [false, true]], true),
    ([[.pos [false, true]]], [.pos [false]], false)]
  for ((formula, certificate, expected), index) in cases.zipIdx do
    unless checkEvaluationRun formula certificate expected do
      throw (IO.userError s!"Formula evaluation case {index} failed.")
  unless checkEvaluationRun [[.neg []], [.pos [false]]] [.pos [false]] true (-37) do
    throw (IO.userError "Formula evaluation failed when started at coordinate -37.")

run_cmd Lean.Elab.Command.liftIO testEvaluation

/--
This executes the complete verifier on a supplied word and checks its answer, the absence of
other occupied cells, its final head coordinate, and the polynomial move bound. The starting
state says that the format is correct, so rejection also checks that the program resets its state.
-/
private def checkVerifierRun (word : List Symbol) (expected : Bool) (origin : ℤ := 0) : Bool :=
  let initial : TMState Verifier.machine :=
    {config := ⟨some (.inl .inputEnd), BiTape.mk₁ word⟩, headPos := origin}
  match TMQuery.execute 100000 Verifier.verify initial with
  | none => false
  | some (result, final) =>
    decide (final.machine.config.BiTape.head = some (digit expected)) &&
      decide (final.machine.config.BiTape.left.toList = []) &&
      decide (final.machine.config.BiTape.right.toList = []) &&
      decide (final.machine.headPos = origin + word.length) &&
      decide (result.tell.steps ≤ 27 * (word.length + 1) ^ 4)

/--
These runs check the complete program on true and false formulas and on incorrectly written
inputs. Rejection cases include missing endings, missing or repeated separators, trailing data,
and digits outside a variable name. The accepted cases include incomplete and repeated assignments.
-/
private def testVerifier : IO Unit := do
  let emptyPair := verifierEncoding.encode ([], [])
  let cases : List (List Symbol × Bool) := [
    (emptyPair, true),
    (verifierEncoding.encode ([[]], []), false),
    (verifierEncoding.encode ([[.pos []]], [.pos []]), true),
    (verifierEncoding.encode ([[.pos [true]]], []), false),
    (verifierEncoding.encode ([[.neg [true]]], []), true),
    (verifierEncoding.encode ([[.pos [true]]], [.pos [true], .neg [true]]), true),
    (verifierEncoding.encode ([[.pos [true]]], [.neg [true], .pos [true]]), false),
    (verifierEncoding.encode ([[.pos [true]], [.neg [true]]], [.pos [true]]), false),
    ([], false),
    ([digit true], false),
    ([certificateSeparator], false),
    ([formulaEnd, clauseEnd], false),
    ([certificateSeparator, clauseEnd], false),
    (emptyPair.dropLast, false),
    (emptyPair ++ [digit true], false),
    (emptyPair ++ [certificateSeparator], false),
    ([positiveSign, formulaEnd, certificateSeparator, clauseEnd], false),
    ([clauseEnd, formulaEnd, certificateSeparator, clauseEnd], false),
    ([formulaEnd, certificateSeparator, positiveSign, clauseEnd], false),
    ([formulaEnd, certificateSeparator, digit true, clauseEnd], false)]
  for ((word, expected), index) in cases.zipIdx do
    unless checkVerifierRun word expected do
      throw (IO.userError s!"SAT verifier case {index} failed.")
  unless checkVerifierRun emptyPair true (-37) do
    throw (IO.userError "SAT verifier acceptance failed when started at coordinate -37.")
  unless checkVerifierRun (emptyPair ++ [digit false]) false 37 do
    throw (IO.userError "SAT verifier rejection failed when started at coordinate 37.")

run_cmd Lean.Elab.Command.liftIO testVerifier

end AlgoleanTests.SAT
