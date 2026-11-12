/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Output
public meta import Algolean.Complexity.Reductions.NPtoSAT.Output
public import AlgoleanTests.Tape

/-!
# Running the direct reduction's output cleanup

These checks require the final tape to contain only the accumulated output followed by the
formula's ending symbol in its chosen encoding. They check the final head position and move
bound, including zero bounds, empty inputs and outputs, and inputs containing the extra symbol
used to locate the start of the input.
-/

open Cslib.Turing.SingleTapeTM

@[expose] public section

namespace AlgoleanTests.NPToSATOutput

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.NPToSAT
open AlgoleanTests.Tape (tapeView)

/-- This fixed machine has one control state and three tape symbols. -/
abbrev control : SingleTapeTM (Fin 3) where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- Cleanup must erase every source cell and leave the head at the first output symbol. -/
def checkCleanup : IO Unit := do
  let tick : Fin 3 := 1
  let code := fun _ : Problems.SAT.CodeSymbol => ([2, 0] : List (Fin 3))
  let program := Output.finish control code
  for (times, positions, states) in [(0, 0, 0), (1, 1, 1), (2, 3, 2), (0, 2, 0)] do
    for input in [[], [1], [0, 1, 2]] do
      for output in [[], [2], [1, 0, 2]] do
        let original := NPToSAT.Computation.ChoiceIteration.layout tick times positions states
          (tick :: input) (tick :: output)
        let initial : TMState control := { config := ⟨some (), original⟩, headPos := -5 }
        let size := times + 2 * positions + 2 * states + input.length + 7
        match execute 10000 program initial with
        | none => throw (IO.userError "Cleaning the reduction's output ran out of fuel.")
        | some (result, final) =>
          unless tapeView final.machine.config.BiTape = tapeView (BiTape.mk₁ (output ++ [2, 0])) ∧
              final.machine.config.state = some () ∧ final.machine.headPos = -5 + size + 1 ∧
              result.tell.steps ≤ 3 * size + 2 * output.length + 21 do
            throw (IO.userError
              "Output cleanup left a source cell or the wrong head, state, or cost.")

run_cmd Lean.Elab.Command.liftIO checkCleanup

end AlgoleanTests.NPToSATOutput
