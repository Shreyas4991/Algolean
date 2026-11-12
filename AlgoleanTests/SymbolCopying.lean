/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.WordCopying
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.WordCopying
public import AlgoleanTests.NPToTMSAT

/-!
# Copying symbols across other tape words

These checks run one fixed copying program on all short words over a three-symbol alphabet.
They compare the entire tape and exact move count, including cells farther left, intervening
empty words, and earlier output. The program must restore its head and control state.
-/

@[expose] public section

namespace AlgoleanTests.SymbolCopying

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines
open AlgoleanTests.NPToTMSAT (tapeView)

/-- This fixed machine has one control state and three tape symbols. -/
abbrev control : SingleTapeTM (Fin 3) where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- Every short input must give the specified copied word without changing surrounding cells. -/
def checkSymbolCopying : IO Unit := do
  let symbols : List (Fin 3) := [0, 1, 2]
  let code := fun symbol : Fin 3 => [symbol, 2, symbol]
  let left := StackTape.mapSome ([2, 0, 1] : List (Fin 3))
  let mut inputs : List (List (Fin 3)) := [[]]
  for _ in [:4] do
    for input in inputs do
      for parts in [[], [[]], [[2, 1], [], [0, 2]]] do
        for output in [[], [1, 0]] do
          let program := copySymbolsAcross control symbols code parts.length
          let initial : TMState control := { config := ⟨some (),
            BiTape.segment (StackTape.cons none left) input
              (StackTape.separateWords parts (StackTape.mapSome output))⟩, headPos := -5 }
          let expected := BiTape.segment (StackTape.cons none left) input
            (StackTape.separateWords parts (StackTape.mapSome (output ++ input.flatMap code)))
          match execute 200000 program initial with
          | none => throw (IO.userError "Copying a symbol word ran out of fuel.")
          | some (result, final) =>
            unless tapeView final.machine.config.BiTape = tapeView expected ∧
                final.machine.config.state = some () ∧ final.machine.headPos = -5 ∧
                result.tell.steps = copyBitsMoves 3 input.length (regionSpan parts) output.length do
              throw (IO.userError "Copying changed a preserved cell, head, state, or move count.")
    inputs := inputs.flatMap fun input => symbols.map (fun symbol => symbol :: input)

run_cmd Lean.Elab.Command.liftIO checkSymbolCopying

end AlgoleanTests.SymbolCopying
