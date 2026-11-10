/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.TMSATToSATTape
public import Algolean.Complexity.Reductions.TMSATToSAT.Parsing
public meta import Algolean.Complexity.Reductions.TMSATToSAT.Parsing
public meta import Algolean.Algorithms.SingleTapeTuringMachines.Reading

/-!
# Checking the TMSAT symbol reader and field boundaries

The fixed-word comparison is run on short Boolean inputs with other regions on both sides.
The field-reading states are checked against encoded instances and words with missing or
extra transition entries, missing separators, and false digits in unary bounds. A separate
case distinguishes checking field boundaries from validating numeric state references.
-/

@[expose] public section

namespace AlgoleanTests.TMSATParsing

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines NPToTMSAT
open Algolean.Problems.TMSAT Algolean.Algorithms.TMSATToSAT.Parsing

/--
This runs each fixed comparison on every Boolean word of length at most four. It includes
matches, mismatches, proper prefixes, and an empty comparison word. Neighboring regions contain
internal blanks, and each run checks their preservation and the restored head position.
-/
def checkComparisons : IO Unit := do
  let left := StackTape.cons (some true) (StackTape.cons none (StackTape.mapSome [false]))
  let tail := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true]))
  for expected in [[], [false], [true, false], [true, true, true]] do
    let program := checkPrefix TMSATToSATTape.control true false expected
    let mut words := [[]]
    for _ in [:5] do
      for word in words do
        let original := BiTape.segment left word tail
        let initial : TMState TMSATToSATTape.control :=
          { config := ⟨some false, original⟩, headPos := -3 }
        match execute 10000 program initial with
        | none => throw (IO.userError "The fixed-word comparison ran out of fuel.")
        | some (result, final) =>
          unless tapeView final.machine.config.BiTape = tapeView original ∧
              final.machine.config.state = some (decide (expected <+: word)) ∧
              final.machine.headPos = -3 ∧ result.tell.steps ≤ 2 * expected.length do
            throw (IO.userError "The comparison gave incorrect contents, answer, or cost.")
      words := words.flatMap (fun word => [false :: word, true :: word])

/--
These checks read valid instances with several verifier sizes and bounds. They then alter a
one-state verifier's description to check missing and extra transitions and malformed bounds.
An out-of-range initial state still has correct field boundaries, so it is checked separately
against the existing decoder.
-/
def checkFieldBoundaries : IO Unit := do
  let descriptionSymbol (symbol : SingleTapeTM.Description.CodeSymbol) : CodeSymbol :=
    .inl (.inl symbol)
  for largest in [:3] do
    let verifier : SingleTapeTM.Description (TapeSymbol Bool) := {
      states := largest
      initial := 0
      transition := fun _ _ => (none, none, none) }
    for input in [[], [false], [true, false]] do
      for certificate in [:3] do
        for time in [:3] do
          let word := encoding.encode (⟨verifier, input, certificate, time⟩ : Instance Bool)
          unless formatResult (Γ := Bool) word = .time do
            throw (IO.userError "The field reader rejected a correctly encoded instance.")
  let verifier : SingleTapeTM.Description (TapeSymbol Bool) := {
    states := 0
    initial := 0
    transition := fun _ _ => (none, none, none) }
  let word := encoding.encode (⟨verifier, [], 0, 0⟩ : Instance Bool)
  let transitionEnd := descriptionSymbol (.inl (.inl (.inl (.inr 0))))
  let rowEnd := descriptionSymbol (.inl (.inl (.inl (.inr 1))))
  let initialEnd := descriptionSymbol (.inl (.inr 0))
  let falseDigit := descriptionSymbol (SingleTapeTM.Description.bitSymbol false)
  let trueDigit := descriptionSymbol (SingleTapeTM.Description.bitSymbol true)
  let missing := word.erase transitionEnd
  let extra := word.insertIdx (word.idxOf rowEnd) transitionEnd
  let noSeparator := word.erase (.inr 0)
  for malformed in [missing, extra, noSeparator, word ++ [falseDigit], word ++ [.inl (.inr 0)]] do
    unless formatResult (Γ := Bool) malformed ≠ .time do
      throw (IO.userError "The field reader accepted a malformed table or bound.")
  for length in [:word.length] do
    unless formatResult (Γ := Bool) (word.take length) ≠ .time do
      throw (IO.userError "The field reader accepted an unfinished instance.")
  let symbolWord := encoding.encode (⟨verifier, [true], 0, 0⟩ : Instance Bool)
  let badSymbol := symbolWord.map fun symbol => if symbol = trueDigit then falseDigit else symbol
  unless formatResult (Γ := Bool) badSymbol ≠ .time do
    throw (IO.userError "The field reader accepted a symbol number outside its alphabet.")
  let threeSymbols : SingleTapeTM.Description (TapeSymbol (Fin 3)) := {
    states := 0
    initial := 0
    transition := fun _ _ => (none, none, none) }
  let canonical := encoding.encode (⟨threeSymbols, [2], 0, 0⟩ : Instance (Fin 3))
  let alternative := canonical.erase trueDigit
  unless formatResult (Γ := Fin 3) alternative = .time ∧
      ((encoding (Γ := Fin 3)).decode alternative).map (·.input) = some [2] do
    throw (IO.userError "The field reader rejected an accepted alternative symbol number.")
  let badInitial := word.insertIdx (word.idxOf initialEnd) trueDigit
  unless formatResult (Γ := Bool) badInitial = .time ∧
      ((encoding (Γ := Bool)).decode badInitial).isNone do
    throw (IO.userError "Field-boundary checks were confused with state-reference checks.")

run_cmd Lean.Elab.Command.liftIO do
  checkComparisons
  checkFieldBoundaries

end AlgoleanTests.TMSATParsing
