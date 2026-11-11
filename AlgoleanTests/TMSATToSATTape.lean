/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.NPToTMSAT
public import Algolean.Complexity.Reductions.TMSATToSAT.Tape
public meta import Algolean.Complexity.Reductions.TMSATToSAT.Tape

/-!
# Running the machines that prepare and navigate the reduction's tape

Initialization is checked on every Boolean input of length at most four, including empty
input and inputs containing the chosen marker. Each fixed program is run on all these inputs.
Navigation is checked with empty and nonempty region contents and with other words on both
sides. The checks compare the entire tape, control state, head position, and head-move count.
Cleanup is checked with empty and nonempty temporary regions and outputs. Every run must
leave only its output, with the head at the first output cell.
-/

@[expose] public section

namespace AlgoleanTests.TMSATToSATTape

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines NPToTMSAT

/-- This machine has two Boolean control states. Its Query instructions determine the execution. -/
abbrev control : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This runs each fixed initializer on all short inputs. It checks preservation of the input and
the exact number and positions of empty regions, including the case with no working regions.
The initial control state and head coordinate differ from those of a fresh machine.
-/
private def checkPreparation : IO Unit := do
  for marker in [false, true] do
    for count in [0, 1, 3] do
      let program := Algorithms.TMSATToSAT.Tape.prepare control marker count
      let mut words := [[]]
      for _ in [:5] do
        for input in words do
          let initial : TMState control := { TMState.init control input with
            config.state := some true
            headPos := -7 }
          let expected := Algorithms.TMSATToSAT.Tape.layout marker
            (List.replicate count [] ++ [input, []])
          match execute 10000 program initial with
          | none => throw (IO.userError "Tape initialization ran out of fuel.")
          | some (result, final) =>
            unless tapeView final.machine.config.BiTape = tapeView expected ∧
                final.machine.config.state = some true ∧
                final.machine.headPos = -7 - (2 * count + 1 : Nat) ∧
                result.tell.steps = 2 * input.length + 2 * count + 7 do
              throw (IO.userError "Tape initialization gave incorrect contents, position, or cost.")
        words := words.flatMap (fun word => [false :: word, true :: word])

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

/-- Cleanup erases all earlier regions and their markers, including when the output is empty. -/
private def checkCleanup : IO Unit := do
  for marker in [false, true] do
    for regions in [[], [[]], [[true]], [[], [false, true], []], [[true, false], [false]]] do
      for output in [[], [false], [true, false, true]] do
        let program := Algorithms.TMSATToSAT.Tape.finish control regions.length
        let initial : TMState control := {
          config := ⟨some true, Algorithms.TMSATToSAT.Tape.layout marker (regions ++ [output])⟩
          headPos := -7 }
        let moves : Nat := (regions.map fun region => region.length + 2).sum + 1
        match execute 10000 program initial with
        | none => throw (IO.userError "Tape cleanup ran out of fuel.")
        | some (result, final) =>
          unless tapeView final.machine.config.BiTape = tapeView (BiTape.mk₁ output) ∧
              final.machine.config.state = some true ∧
              final.machine.headPos = -7 + (moves : Int) ∧ result.tell.steps = moves do
            throw (IO.userError "Tape cleanup gave incorrect contents, position, or cost.")

run_cmd Lean.Elab.Command.liftIO do
  checkPreparation
  checkNavigation
  checkCleanup

end AlgoleanTests.TMSATToSATTape
