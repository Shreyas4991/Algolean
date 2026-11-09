/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.TMComplexity

/-!
# Executing the append and complement programs

These examples check appending and complementing Boolean words, including empty inputs and
running both programs in sequence. Each observation records the complete tape, the control
label, the head coordinate, the number of head-move instructions, and the tape-storage counts.
A run that starts at coordinate 37 checks that the program preserves its starting label and
coordinate and includes previously counted tape cells in its storage count.

The examples with arbitrary input words check the correctness proofs for running the programs
in sequence. The final examples check that the values proving polynomial-time computability
store the original executable programs.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTuringMachines

open Algolean Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Cslib.Turing TMQuery

open scoped TMQuery Computer

/--
This machine supplies two control labels for executing Boolean query programs. Its transition
table preserves the current symbol and halts; the query programs specify the tested operations.
-/
abbrev machine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This value records the complete tape, control label, head coordinate, and execution counts.
It includes blanks between occupied cells and all represented cells to the left of the head,
so comparing observations can detect stray symbols anywhere on the tape.
-/
structure Observation where
  /-- This is the symbol under the head, or `none` if that cell is blank. -/
  head : Option Bool
  /-- These are the cells to the left of the head, nearest first, including internal blanks. -/
  left : List (Option Bool)
  /-- These are the cells to the right of the head, nearest first, including internal blanks. -/
  right : List (Option Bool)
  /-- This is the final control label, or `none` if the machine has no current label. -/
  label : Option Bool
  /-- This is the final head coordinate, with coordinates increasing to the right. -/
  headPos : ℤ
  /-- This is the number of head-move instructions executed by the program. -/
  moves : ℕ
  /-- This is the number of tape cells added to the storage count during this run. -/
  newCells : ℕ
  /-- This is the final storage count, including cells counted before this run began. -/
  totalCells : ℕ
deriving DecidableEq

/--
This function runs a Boolean Turing machine program from the supplied state with a limit of
100 execution steps. On success, it records the complete final tape, control label, head
coordinate, number of head-move instructions, and tape-storage counts. It returns `none` if
the limit is reached before the program finishes.
-/
def observe (p : Prog (TMQuery machine) Unit) (initial : TMState machine) : Option Observation :=
  (execute 100 p initial).map fun (result, final) =>
    ⟨final.machine.config.BiTape.head, final.machine.config.BiTape.left.toList,
      final.machine.config.BiTape.right.toList, final.machine.config.state,
      final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
      final.machine.cellsAllocated.card⟩

example : observe (appendBit machine true) (TMState.init machine []) =
    some ⟨some true, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (appendBit machine false) (TMState.init machine []) =
    some ⟨some false, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (appendBit machine false) (TMState.init machine [true, false]) =
    some ⟨some true, [], [some false, some false], some false, 0, 6, 2, 4⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine []) =
    some ⟨none, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine [false]) =
    some ⟨some true, [], [], some false, 0, 4, 2, 3⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine [true, false, true]) =
    some ⟨some false, [], [some true, some false], some false, 0, 8, 2, 5⟩ := by decide +kernel

/--
This Turing machine program appends `true` and then negates every bit of the resulting word.
It carries the correctness proofs for both programs. The second program uses the tape and the
recorded storage and head visits left by the first.
-/
def pipeline :=
  appendBitComputer (tm := machine) true ≫ₜ complementBlockComputer (tm := machine)

example : observe pipeline.program (TMState.init machine [true, false]) =
    some ⟨some false, [], [some true, some false], some false, 0, 14, 3, 5⟩ := by decide +kernel

example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 37 40
        cellsVisited := {37, 38}}
    observe (appendBit machine true) initial =
      some ⟨some true, [], [some false, some true], some true, 37, 6, 1, 5⟩ := by decide +kernel

-- The bundled proof applies to arbitrary words, starting labels, coordinates, and tape histories.
example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes pipeline.program s cost final ∧
      final.config = {s.config with BiTape := BiTape.mk₁ ((input ++ [true]).map Bool.not)} ∧
      final.headPos = s.headPos ∧
      cost.steps ≤ (2 * input.length + 2) + (2 * (input ++ [true]).length + 2) :=
  pipeline.correct input s hs

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (appendBit machine true) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsAllocated ≤ 2 * input.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * input.length + 2) :=
  (appendBit_computes (tm := machine) true).space input s hs

-- The values proving polynomial-time computability store the original executable programs.
example : (appendBitPolyTimeComputable (tm := machine) true).program =
    appendBit machine true := rfl

example : (complementBlockPolyTimeComputable (tm := machine)).program =
    complementBlock machine := rfl

end AlgoleanTests.SingleTapeTuringMachines
