/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.TapeChoices
public meta import Algolean.Complexity.Reductions.TMSATToSAT.TapeChoices
public import AlgoleanTests.NPToTMSAT

/-!
# Running the tape-cell clause writer

The checks run one fixed Query program on different time and position bounds. They compare
its entire output with the existing SAT encoder and computation-variable names. Empty bounds,
empty and repeated choices, binary carries, preserved input, and earlier output are included.
-/

@[expose] public section

namespace AlgoleanTests.TMSATTapeChoices

open Algolean Algolean.Algorithms Cslib Cslib.Turing Computability
open Algolean.Problems Algolean.Problems.SAT Algolean.Algorithms.TMSATToSAT

/-- This fixed machine has one control state and stores all indices on its tape. -/
abbrev control : SingleTapeTM CodeSymbol where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This checks complete executions against the existing formula encoding for every cell. -/
private def checkWriter : IO Unit := do
  let zero : CodeSymbol := .inl false
  let one : CodeSymbol := .inl true
  let tick : CodeSymbol := .inr 0
  let first : Option (TMSAT.TapeSymbol CodeSymbol) := none
  let second : Option (TMSAT.TapeSymbol CodeSymbol) := some (.inl (.inl false))
  for symbols in [[], [first], [first, second], [first, first, second]] do
    let program := TapeChoices.writeChoices control zero one tick (fun symbol => [symbol]) symbols
    for (times, positions) in [(0, 0), (0, 3), (2, 0), (1, 1), (2, 3), (4, 1)] do
      let input : List CodeSymbol := [.inr 4, .inl true, .inr 0]
      let output : List CodeSymbol := [.inr 5, .inl false]
      let original := TapeChoices.layout tick times positions input output
      let initial : TMState control := {config := ⟨some (), original⟩, headPos := -5}
      let expected := (List.range times).flatMap fun time =>
        (List.range positions).flatMap fun position =>
          formulaPrefix ((CNF.exactlyOne symbols).rename fun symbol =>
            true :: false :: BooleanTapeEncoding.pair (encodingNatBool.encode time)
              (BooleanTapeEncoding.pair (encodingNatBool.encode position)
                (encodingNatBool.encode (Encodable.encode symbol))))
      match TMQuery.execute 10000000 program initial with
      | none => throw (IO.userError "The tape-cell clause writer ran out of fuel.")
      | some (_, final) =>
        unless NPToTMSAT.tapeView final.machine.config.BiTape =
            NPToTMSAT.tapeView
              (TapeChoices.layout tick times positions input (output ++ expected)) ∧
            final.machine.config.state = some () ∧ final.machine.headPos = -5 do
          throw (IO.userError
            s!"Incorrect tape-cell clauses for {times} times and {positions} cells.")

run_cmd Lean.Elab.Command.liftIO checkWriter

end AlgoleanTests.TMSATTapeChoices
