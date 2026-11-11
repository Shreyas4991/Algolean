/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.TMSATToSATTape
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement

/-!
# Running the binary-counter program

Subtraction is checked on all positive Boolean words of length at most seven, including words
with leading zeros. The checks verify the output's numeric value, the neighboring tape contents,
the final head position, and the proved move bound.
-/

public section

namespace AlgoleanTests.TMSATNumbers

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines NPToTMSAT

/--
This runs subtraction on short positive counters. It checks that the digits still occupy the
same cells, their value decreased by one, and the neighboring tape contents stayed unchanged.
Every initial control state is included, and the head must return to its starting coordinate.
-/
def checkSubtraction : IO Unit := do
  let mut words := [[]]
  for _ in [:8] do
    for word in words do
      let value := binaryValue word.reverse
      if value > 0 then
        for label in [none, some false, some true] do
          for tail in [StackTape.nil, StackTape.cons (some true)
              (StackTape.cons none (StackTape.mapSome [false, true]))] do
            let initial : TMState TMSATToSATTape.control := {
              config := ⟨label, BiTape.segment StackTape.nil word tail⟩
              headPos := -9 }
            match execute 10000 (decrementLeft TMSATToSATTape.control false true) initial with
            | none => throw (IO.userError "Subtraction ran out of fuel.")
            | some (result, final) =>
              let contents := (List.range word.length).map fun index =>
                (BiTape.moveRight^[index] final.machine.config.BiTape).head
              let output := contents.filterMap id
              unless contents.all Option.isSome ∧ output.length = word.length ∧
                  binaryValue output.reverse + 1 = value ∧
                  tapeView final.machine.config.BiTape =
                    tapeView (BiTape.segment StackTape.nil output tail) ∧
                  final.machine.config.state = label ∧ final.machine.headPos = -9 ∧
                  result.tell.steps ≤ 4 * word.length + 4 do
                throw (IO.userError "Subtraction changed the wrong number, cells, head, or state.")
    words := words.flatMap fun word => [false :: word, true :: word]

run_cmd Lean.Elab.Command.liftIO checkSubtraction

end AlgoleanTests.TMSATNumbers
