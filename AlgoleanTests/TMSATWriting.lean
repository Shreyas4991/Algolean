/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Writing
public import AlgoleanTests.NPToTMSAT
public meta import Algolean.Complexity.Reductions.TMSATToSAT.Writing

/-!
# Checking the SAT literal writer

The tests run the same program on a variable and its negation for every binary name of length
at most five. They check that the original sign and name, previous output, and other data
farther left are unchanged. They also check what the program writes, where the head stops,
and how many moves it makes.

Another program finishes the clause and the whole formula. Its output must match the word
produced by SAT's existing encoder for a formula with one literal. This is checked both on a
tape with eight symbols and on a Boolean tape, where each SAT symbol occupies eight cells.
-/

public section

namespace AlgoleanTests.TMSATWriting

open Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines Algolean.Problems.SAT
open Algolean.Algorithms.TMSATToSAT.Writing
open AlgoleanTests.NPToTMSAT (tapeView)
open scoped TMQuery

/-- This machine has two states and uses the tape symbols chosen for the test. -/
abbrev control (Γ : Type) [Inhabited Γ] [Fintype Γ] : SingleTapeTM Γ where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

private def names : List (List Bool) :=
  (List.range 6).flatMap fun length =>
    (List.range (2 ^ length)).map fun value => (List.range length).map value.testBit

private def earlierCells : StackTape CodeSymbol :=
  StackTape.cons (some (.inr 5))
    (StackTape.cons none (StackTape.mapSome [.inr 4, .inl true]))

private def program : Prog (TMQuery (control CodeSymbol)) Unit :=
  appendLiteral (control CodeSymbol) (.inl false) (.inl true) List.singleton

private def formulaProgram : Prog (TMQuery (control CodeSymbol)) Unit :=
    do [TMQuery (control CodeSymbol)]
  program
  nextRegion (control CodeSymbol)
  endClause (control CodeSymbol) List.singleton
  endFormula (control CodeSymbol) List.singleton

private def booleanCode (symbol : CodeSymbol) : List Bool :=
  List.ofFn fun position : Fin 8 => position.val == match symbol with
    | .inl false => 0
    | .inl true => 1
    | .inr marker => marker.val + 2

private def booleanProgram : Prog (TMQuery (control Bool)) Unit := do [TMQuery (control Bool)]
  appendLiteral (control Bool) false true booleanCode
  nextRegion (control Bool)
  endClause (control Bool) booleanCode
  endFormula (control Bool) booleanCode

/--
This runs the same literal writer on short names with both signs and several previous outputs.
It checks that the original sign and name and the cells farther left are unchanged and that
the head returns to the sign. The added word must match the existing certificate encoder's
word for one literal, without the symbol that ends the clause. Each run checks the move count.
-/
def checkLiterals : Bool :=
  [false, true].all fun negative => names.all fun name =>
    [[], [.inr 5], [.inr 0, .inl false, .inr 2, .inr 3, .inr 4]].all fun output =>
    [none, some false, some true].all fun label =>
      let source : List CodeSymbol := .inl negative :: name.map Sum.inl
      let literal := if negative then Literal.neg name else Literal.pos name
      let original := BiTape.segment (StackTape.cons none earlierCells) source
        (StackTape.mapSome output)
      let initial : TMState (control CodeSymbol) := { config := ⟨label, original⟩, headPos := -13 }
      let expected := BiTape.segment (StackTape.cons none earlierCells) source
        (StackTape.mapSome (output ++ (certificateEncoding.encode [literal]).dropLast))
      match execute 20000 program initial with
      | none => false
      | some (result, final) =>
        decide (tapeView final.machine.config.BiTape = tapeView expected ∧
          final.machine.config.state = label ∧ final.machine.headPos = -13 ∧
          result.tell.steps = 2 * name.length ^ 2 + 2 * name.length * output.length +
            20 * name.length + 4 * output.length + 30)

/--
This runs a program that writes one literal and then finishes the clause and formula. Its
output must match SAT's existing formula encoder. The original sign and name and all cells
farther left must be unchanged. The head must stop at the first output cell, and the number
of moves must equal the stated count.
-/
def checkFormulas : Bool :=
  [false, true].all fun negative => names.all fun name =>
    [[], [.inr 5], [.inl true, .inr 2]].all fun output =>
      let source : List CodeSymbol := .inl negative :: name.map Sum.inl
      let literal := if negative then Literal.neg name else Literal.pos name
      let original := BiTape.segment (StackTape.cons none earlierCells) source
        (StackTape.mapSome output)
      let initial : TMState (control CodeSymbol) :=
        { config := ⟨some true, original⟩, headPos := -13 }
      let expected := BiTape.segment
        (StackTape.cons none (StackTape.prepend source.reverse (StackTape.cons none earlierCells)))
        (output ++ encoding.encode [[literal]]) StackTape.nil
      match execute 30000 formulaProgram initial with
      | none => false
      | some (result, final) =>
        decide (tapeView final.machine.config.BiTape = tapeView expected ∧
          final.machine.config.state = some true ∧
          final.machine.headPos = -13 + (name.length + 2 : Nat) ∧
          result.tell.steps = 2 * name.length ^ 2 + 2 * name.length * output.length +
            25 * name.length + 8 * output.length + 62)

/--
This runs the formula writer on a Boolean tape. Each SAT symbol is written as eight cells
with exactly one true cell. The expected word is obtained by applying that same representation
to the result of SAT's existing encoder. Each run checks the entire tape, machine state, final
head position, and number of moves.
-/
def checkBooleanCodes : Bool :=
  let earlier := StackTape.cons (some false)
    (StackTape.cons none (StackTape.mapSome [true, false]))
  [false, true].all fun negative => names.all fun name =>
    [[], [true, false], [false, false, false]].all fun output =>
      let source := negative :: name
      let literal := if negative then Literal.neg name else Literal.pos name
      let original := BiTape.segment (StackTape.cons none earlier) source
        (StackTape.mapSome output)
      let initial : TMState (control Bool) := { config := ⟨some true, original⟩, headPos := -13 }
      let expected := BiTape.segment
        (StackTape.cons none (StackTape.prepend source.reverse (StackTape.cons none earlier)))
        (output ++ (encoding.encode [[literal]]).flatMap booleanCode) StackTape.nil
      match execute 30000 booleanProgram initial with
      | none => false
      | some (result, final) =>
        decide (tapeView final.machine.config.BiTape = tapeView expected ∧
          final.machine.config.state = some true ∧
          final.machine.headPos = -13 + (name.length + 2 : Nat) ∧
          result.tell.steps = 9 * name.length ^ 2 + 2 * name.length * output.length +
            88 * name.length + 8 * output.length + 230)

run_cmd do
  unless checkLiterals do
    throwError "The literal writer gave incorrect contents, position, or cost."
  unless checkFormulas do
    throwError "The complete formula writer disagreed with SAT's encoder or its exact move count."
  unless checkBooleanCodes do
    throwError "The Boolean formula writer gave incorrect contents, position, or cost."

end AlgoleanTests.TMSATWriting
