/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.MetaTMNavigation
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement
public meta import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading

/-!
# Running the counter and backward-search programs

Subtraction is checked on all positive Boolean words of length at most seven, including words
with leading zeros. The output is checked by its numeric value. The backward search is checked
with several intervening words and with other tape contents on both sides. Both checks verify
the final head position and the proved move bounds.
-/

public section

namespace AlgoleanTests.MetaTMCounters

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines
open AlgoleanTests.Tape (tapeView)

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
            let initial : TMState MetaTMNavigation.control := {
              config := ⟨label, BiTape.segment StackTape.nil word tail⟩
              headPos := -9 }
            match execute 10000 (decrementLeft MetaTMNavigation.control false true) initial with
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

/--
This searches backward for a fixed three-bit word. The intervening three-bit words differ
from the target. Each run checks the whole tape, the found state, and the number of moves.
The tape on both sides of the searched words includes blanks that the search must preserve.
-/
def checkBackwardSearch : IO Unit := do
  let expected := [true, false, true]
  let left := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true]))
  let tail := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true, false]))
  let mut possibilities := [[]]
  for _ in [:5] do
    for blocks in possibilities do
      let crossed := expected ++ blocks.flatten
      for label in [none, some false, some true] do
        for suffix in [[], [false], [true, false], expected] do
          let initial : TMState MetaTMNavigation.control := {
            config := ⟨label,
              BiTape.segment (StackTape.prepend crossed.reverse left) suffix tail⟩
            headPos := 7 }
          let program := findPreviousWord MetaTMNavigation.control true false expected
          match execute 10000 program initial with
          | none => throw (IO.userError "The backward search ran out of fuel.")
          | some (result, final) =>
            unless tapeView final.machine.config.BiTape =
                  tapeView (BiTape.segment left (crossed ++ suffix) tail) ∧
                final.machine.config.state = some true ∧
                final.machine.headPos = 7 - 3 * (blocks.length + 1 : Nat) ∧
                result.tell.steps ≤ 9 * (blocks.length + 1) do
              throw (IO.userError "The backward search changed the tape or found the wrong cell.")
    possibilities := possibilities.flatMap fun blocks =>
      [[false, false, false] :: blocks, [true, true, true] :: blocks,
        [false, true, false] :: blocks]

run_cmd Lean.Elab.Command.liftIO do
  checkSubtraction
  checkBackwardSearch

end AlgoleanTests.MetaTMCounters
