/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Framed

/-!
# Executing Boolean-word programs and copying encoded pairs

These examples check Boolean-word programs on empty and nonempty inputs and in sequence.
Writing and flipping tests cover both bit values and blanks. Increment tests cover both a carry
that stops within the word and an overflow that adds a new bit. Each observation records the tape,
the control label, the head coordinate, the number of head-move instructions, and the tape-storage
counts.
A run that starts at coordinate 37 checks that the program preserves its starting label and
coordinate and includes previously counted tape cells in its storage count.

The copying examples check the encoded output, the final head position to the left of the input,
and the costs of duplicating a word and appending to its second copy. They also check that
appending to an encoded pair preserves its first word and length header.

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
`fuel` execution steps, defaulting to 100. On success, it records the complete final tape, control
label, head coordinate, number of head-move instructions, and tape-storage counts. It returns
`none` if the limit is reached before the program finishes.
-/
def observe (p : Prog (TMQuery machine) Unit) (initial : TMState machine) (fuel : ℕ := 100) :
    Option Observation :=
  (execute fuel p initial).map fun (result, final) =>
    ⟨final.machine.config.BiTape.head, final.machine.config.BiTape.left.toList,
      final.machine.config.BiTape.right.toList, final.machine.config.state,
      final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
      final.machine.cellsAllocated.card⟩

-- Writing creates a bit on empty input and replaces only the first bit of a nonempty word.
example : observe (writeBit machine true) (TMState.init machine []) =
    some ⟨some true, [], [], some false, 0, 0, 0, 1⟩ := by decide +kernel

example : observe (writeBit machine false) (TMState.init machine []) =
    some ⟨some false, [], [], some false, 0, 0, 0, 1⟩ := by decide +kernel

example : observe (writeBit machine false) (TMState.init machine [true, false]) =
    some ⟨some false, [], [some false], some false, 0, 0, 0, 2⟩ := by decide +kernel

-- Flipping preserves a blank and exchanges both possible bit values.
example : observe (flipBit machine) (TMState.init machine []) =
    some ⟨none, [], [], some false, 0, 0, 0, 1⟩ := by decide +kernel

example : observe (flipBit machine) (TMState.init machine [false, true]) =
    some ⟨some true, [], [some true], some false, 0, 0, 0, 2⟩ := by decide +kernel

example : observe (flipBit machine) (TMState.init machine [true, false]) =
    some ⟨some false, [], [some false], some false, 0, 0, 0, 2⟩ := by decide +kernel

-- The two verified programs can run in sequence without changing position or storage counts.
example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 41
        cellsVisited := {37, 40}}
    observe (writeBitComputer (tm := machine) true ≫ₜ flipBitComputer (tm := machine)).program
      initial = some ⟨some false, [], [some false], some true, 37, 0, 0, 7⟩ := by decide +kernel

example : (writeBitComputer (tm := machine) true).program = writeBit machine true := rfl

example : (flipBitComputer (tm := machine)).program = flipBit machine := rfl

-- The stored scan programs can run in sequence on empty input and an earlier storage history.
example : observe (do
    (seekRightBlankComponent (tm := machine)).program
    (seekLeftEndComponent (tm := machine)).program) (TMState.init machine []) =
      some ⟨none, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 41
        cellsVisited := {37, 40}}
    observe (do
      (seekRightBlankComponent (tm := machine)).program
      (seekLeftEndComponent (tm := machine)).program) initial =
        some ⟨some true, [], [some false], some true, 37, 6, 0, 7⟩ := by decide +kernel

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

-- A false bit is an occupied cell and must be erased along with the true bits.
example : observe (eraseBlock machine) (TMState.init machine []) =
    some ⟨none, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (eraseBlock machine) (TMState.init machine [false]) =
    some ⟨none, [], [], some false, 0, 4, 2, 3⟩ := by decide +kernel

example : observe (eraseBlock machine) (TMState.init machine [true, false, true]) =
    some ⟨none, [], [], some false, 0, 8, 2, 5⟩ := by decide +kernel

-- The least significant bit comes first, and empty input represents zero.
example : observe (increment machine) (TMState.init machine []) =
    some ⟨some true, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (increment machine) (TMState.init machine [false, true]) =
    some ⟨some true, [], [some true], some false, 0, 2, 1, 3⟩ := by decide +kernel

example : observe (increment machine) (TMState.init machine [true, true, false]) =
    some ⟨some false, [], [some false, some true], some false, 0, 6, 1, 4⟩ := by decide +kernel

example : observe (increment machine) (TMState.init machine [true, true, true]) =
    some ⟨some false, [], [some false, some false, some true], some false, 0, 8, 2, 5⟩ := by
  decide +kernel

/--
This Turing machine program appends `true` and then negates every bit of the resulting word.
It carries the correctness proofs for both programs. The second program uses the tape and the
recorded storage and head visits left by the first.
-/
def pipeline :=
  appendBitComputer (tm := machine) true ≫ₜ complementBlockComputer (tm := machine)

/--
This Turing machine program increments the input and then erases the result. Erasure runs on
the actual incremented word, including the extra bit when incrementing overflows. Both programs
return to the starting head coordinate, and the stored proof adds their head-move bounds.
-/
def incrementThenErase :
    Computer machine (fun _ => [])
      (fun bits => (2 * bits.length + 2) + (2 * (incrementBits bits).length + 2)) :=
  incrementComputer (tm := machine) ≫ₜ eraseBlockComputer (tm := machine)

example : observe pipeline.program (TMState.init machine [true, false]) =
    some ⟨some false, [], [some true, some false], some false, 0, 14, 3, 5⟩ := by decide +kernel

example : observe incrementThenErase.program (TMState.init machine [true, true, true]) =
    some ⟨none, [], [], some false, 0, 18, 3, 6⟩ := by decide +kernel

example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 37 40
        cellsVisited := {37, 38}}
    observe (appendBit machine true) initial =
      some ⟨some true, [], [some false, some true], some true, 37, 6, 1, 5⟩ := by decide +kernel

-- Incrementing and erasing preserve the starting label and include earlier tape-storage counts.
example :
    let initial : TMState machine :=
      {TMState.init machine [true, true, true] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 41
        cellsVisited := {37, 40}}
    observe (increment machine) initial =
      some ⟨some false, [], [some false, some false, some true], some true, 37, 8, 0, 7⟩ := by
  decide +kernel

example :
    let initial : TMState machine :=
      {TMState.init machine [true, false, true] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 41
        cellsVisited := {37, 40}}
    observe (eraseBlock machine) initial =
      some ⟨none, [], [], some true, 37, 8, 0, 7⟩ := by decide +kernel

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

-- Incrementing adds one even when its result needs an extra most significant bit.
example (input : List Bool) : binaryValue (incrementBits input) = binaryValue input + 1 :=
  binaryValue_incrementBits input

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (increment machine) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsAllocated ≤ 2 * input.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * input.length + 2) :=
  increment_complexity input s (by simpa [cursor_start] using hs)

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (eraseBlock machine) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsAllocated ≤ 2 * input.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * input.length + 2) :=
  (eraseBlock_computes (tm := machine)).space input s hs

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes incrementThenErase.program s cost final ∧
      final.config = {s.config with BiTape := BiTape.mk₁ []} ∧ final.headPos = s.headPos ∧
      cost.steps ≤ (2 * input.length + 2) + (2 * (incrementBits input).length + 2) :=
  incrementThenErase.correct input s hs

-- The values proving polynomial-time computability store the original executable programs.
example : (appendBitPolyTimeComputable (tm := machine) true).program =
    appendBit machine true := rfl

example : (complementBlockPolyTimeComputable (tm := machine)).program =
    complementBlock machine := rfl

example : (eraseBlockPolyTimeComputable (tm := machine)).program = eraseBlock machine := rfl

example : (incrementPolyTimeComputable (tm := machine)).program = increment machine := rfl

-- The length header preserves both word boundaries, even when either word is empty.
example (first second : List Bool) :
    BooleanTapeEncoding.unpair (BooleanTapeEncoding.pair first second) = some (first, second) := by
  simp

example (first second suffix : List Bool) :
    BooleanTapeEncoding.unpair (BooleanTapeEncoding.pair first (second ++ suffix)) =
      some (first, second ++ suffix) := by simp

-- Decoding rejects a missing delimiter and a first word shorter than the header claims.
example : BooleanTapeEncoding.unpair [true, true] = none := by decide +kernel

example : BooleanTapeEncoding.unpair [true, true, false, true] = none := by decide +kernel

-- Empty input still produces the false delimiter of an encoded pair of empty words.
example : observe (Copying.duplicate machine) (TMState.init machine []) 1000 =
    some ⟨some false, [], [], some false, -1, 5, 3, 4⟩ := by decide +kernel

example : observe (Copying.duplicate machine) (TMState.init machine [false]) 1000 =
    some ⟨some true, [], [some false, some false, some false], some false, -2, 20, 6, 7⟩ := by
  decide +kernel

example : observe (Copying.duplicate machine) (TMState.init machine [true]) 1000 =
    some ⟨some true, [], [some false, some true, some true], some false, -2, 20, 6, 7⟩ := by
  decide +kernel

example : observe (Copying.duplicate machine) (TMState.init machine [true, false]) 1000 =
    some ⟨some true, [], [some true, some false, some true, some false, some true, some false],
      some false, -3, 43, 8, 10⟩ := by decide +kernel

-- Appending to an encoded pair keeps the first word and its length header unchanged.
example : observe (appendRightComputer (tm := machine) true).program
    (TMState.init machine [false]) =
      some ⟨some false, [], [some true], some false, 0, 4, 2, 3⟩ := by decide +kernel

example : observe (appendRightComputer (tm := machine) false).program
    (TMState.init machine (BooleanTapeEncoding.pair [false, true] [true])) =
      some ⟨some true, [], [some true, some false, some false, some true, some true, some false],
        some false, 0, 14, 2, 8⟩ := by decide +kernel

-- The composed program includes the physical copying cost before extending the second copy.
example : observe (duplicateAppendRightComputer (tm := machine) true).program
    (TMState.init machine []) 1000 =
      some ⟨some false, [], [some true], some false, -1, 9, 3, 4⟩ := by decide +kernel

example : observe (duplicateAppendRightComputer (tm := machine) false).program
    (TMState.init machine [false]) 1000 =
      some ⟨some true, [], [some false, some false, some false, some false],
        some false, -2, 30, 6, 7⟩ := by decide +kernel

example : observe (duplicateAppendRightComputer (tm := machine) true).program
    (TMState.init machine [true, false]) 1000 =
      some ⟨some true, [], [some true, some false, some true, some false, some true,
        some false, some true], some false, -3, 59, 8, 10⟩ := by decide +kernel

-- The shifted output position is relative to the supplied origin, and earlier cells remain counted.
example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 41
        cellsVisited := {37, 40}}
    observe (duplicateAppendRightComputer (tm := machine) true).program initial 1000 =
      some ⟨some true, [], [some true, some false, some true, some false, some true,
        some false, some true], some true, 34, 59, 3, 10⟩ := by decide +kernel

-- The exact copying cost and storage bound hold for every input and earlier tape history.
example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (Copying.duplicate machine) s cost final ∧
      cost.steps = 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      cost.cellsAllocated ≤ 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      final.cellsAllocated.card ≤
        s.cellsAllocated.card + (4 * input.length ^ 2 + 11 * input.length + 5) :=
  Copying.duplicate_space input s hs

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final,
      Completes (duplicateAppendRightComputer (tm := machine) true).program s cost final ∧
      final.config = {s.config with
        BiTape := BiTape.mk₁ (BooleanTapeEncoding.pair input (input ++ [true]))} ∧
      final.headPos = s.headPos - (input.length + 1 : ℕ) ∧
      cost.steps ≤ 4 * input.length ^ 2 + 17 * input.length + 9 :=
  (duplicateAppendRightComputer (tm := machine) true).correct input s hs

-- The polynomial-time values retain the programs that perform the physical tape operations.
example : (Copying.duplicatePolyTimeComputable (tm := machine)).program =
    Copying.duplicate machine := rfl

example : (duplicateAppendRightPolyTimeComputable (tm := machine) true).program =
    (duplicateAppendRightComputer (tm := machine) true).program := rfl

end AlgoleanTests.SingleTapeTuringMachines
