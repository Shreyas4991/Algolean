/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.MetaTMNavigation
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading

/-!
# Running the fixed-word comparison program

The checks compare each short Boolean word with several fixed prefixes, including the empty
word. They verify the answer, the whole tape, the restored head position, and the move bound.
-/

public section

namespace AlgoleanTests.MetaTMReading

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines
open AlgoleanTests.Tape (tapeView)

/--
This runs each fixed comparison on every Boolean word of length at most four. It includes
matches, mismatches, proper prefixes, and an empty comparison word. Neighboring regions contain
internal blanks, and each run checks their preservation and the restored head position.
-/
def checkComparisons : IO Unit := do
  let left := StackTape.cons (some true) (StackTape.cons none (StackTape.mapSome [false]))
  let tail := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true]))
  for expected in [[], [false], [true, false], [true, true, true]] do
    let program := checkPrefix MetaTMNavigation.control true false expected
    let mut words := [[]]
    for _ in [:5] do
      for word in words do
        let original := BiTape.segment left word tail
        let initial : TMState MetaTMNavigation.control :=
          { config := ⟨some false, original⟩, headPos := -3 }
        match execute 10000 program initial with
        | none => throw (IO.userError "The fixed-word comparison ran out of fuel.")
        | some (result, final) =>
          unless tapeView final.machine.config.BiTape = tapeView original ∧
              final.machine.config.state = some (decide (expected <+: word)) ∧
              final.machine.headPos = -3 ∧ result.tell.steps ≤ 2 * expected.length do
            throw (IO.userError "The comparison gave incorrect contents, answer, or cost.")
      words := words.flatMap (fun word => [false :: word, true :: word])

run_cmd Lean.Elab.Command.liftIO do
  checkComparisons

end AlgoleanTests.MetaTMReading
