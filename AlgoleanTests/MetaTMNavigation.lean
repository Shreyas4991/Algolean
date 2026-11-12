/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.Tape
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions

/-!
# Running the word-navigation programs

The checks cross the blank between two words in both directions. They include empty words
and extra tape contents on both sides. Every run checks the whole tape, the control state,
the head position, and the exact number of head moves.
-/

@[expose] public section

namespace AlgoleanTests.MetaTMNavigation

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines
open AlgoleanTests.Tape (tapeView)

/-- This machine has two Boolean control states. Its Query instructions determine the execution. -/
abbrev control : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This crosses a separating blank in both directions. It checks each intermediate tape and the
restored tape, including words farther away that contain internal blanks. Empty region contents
still have markers, so the program must stop at the correct neighboring region.
-/
private def checkNavigation : IO Unit := do
  let next := nextRegion control
  let previous := previousRegion control
  let left := StackTape.cons (some true) (StackTape.cons none (StackTape.mapSome [false]))
  let tail := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true]))
  for marker in [false, true] do
    for first in [[], [false], [true, false]] do
      for second in [[], [true], [false, true]] do
        let first := marker :: first
        let second := marker :: second
        let original := BiTape.segment (StackTape.cons none left) first
          (StackTape.prepend second (StackTape.cons none tail))
        let initial : TMState control := { config := ⟨some true, original⟩, headPos := -7 }
        let expected := BiTape.segment
          (StackTape.cons none (StackTape.prepend first.reverse (StackTape.cons none left)))
          second tail
        match execute 10000 next initial with
        | none => throw (IO.userError "Moving to the next region ran out of fuel.")
        | some (result, final) =>
          unless tapeView final.machine.config.BiTape = tapeView expected ∧
              final.machine.config.state = some true ∧
              final.machine.headPos = -7 + (first.length + 1 : Nat) ∧
              result.tell.steps = first.length + 1 do
            throw (IO.userError "Moving right damaged a region or gave the wrong position or cost.")
          match execute 10000 previous final.machine with
          | none => throw (IO.userError "Returning to the previous region ran out of fuel.")
          | some (result, restored) =>
            unless tapeView restored.machine.config.BiTape = tapeView original ∧
                restored.machine.config.state = some true ∧ restored.machine.headPos = -7 ∧
                result.tell.steps = first.length + 3 do
              throw (IO.userError "Returning left gave incorrect contents, position, or cost.")

run_cmd Lean.Elab.Command.liftIO do
  checkNavigation

end AlgoleanTests.MetaTMNavigation
