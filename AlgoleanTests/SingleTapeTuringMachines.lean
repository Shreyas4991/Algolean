/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Augmented
public import Algolean.Algorithms.SingleTapeTuringMachines.Framed
public import Algolean.Complexity.NP
public import Algolean.Models.SingleTapeTM.Composition.MachineComposition

/-!
# Executing the verified single-tape programs

These examples run Boolean Turing machine programs on concrete input tapes and check their outputs,
final head positions, head-move counts, and tape-allocation counts. They cover primitive writes and
flips, scans, erasure, appending, complementation, binary increment, and compositions of these
programs. The copying examples also check the Boolean pair encoding and the shifted output
coordinate, including runs that begin with previously allocated tape cells.

The separator examples use an alphabet with one added marker and check first-word extraction on
ordinary pairs, empty input, a missing separator, and repeated separators. The observation functions
inspect the final machine state after execution; the programs themselves obtain their input from the
tape. The generic examples also exercise the correctness statements for arbitrary input words and
initial cell histories.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTuringMachines

open Algolean Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Cslib.Turing TMQuery

open scoped TMQuery
open scoped Computer

/--
This machine supplies a Boolean tape and a single control-state label for executing the example
query programs. Its transition table preserves the current symbol and halts; the tested tape
operations come from the query programs passed to `execute`.
-/
abbrev machine : SingleTapeTM Bool where
  State := PUnit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/--
`observe p input` initializes the Boolean machine with `input` and runs `p` with 100 units of
interpreter fuel. On success it returns the nonblank symbols at and to the right of the final head,
the head coordinate, the number of head moves, the additional allocation count, and the total
allocation count. It returns `none` if execution runs out of fuel.
-/
@[simp] def observe (p : Prog (TMQuery machine) Unit) (input : List Bool) :
    Option (List Bool × ℤ × ℕ × ℕ × ℕ) :=
  (execute 100 p (TMState.init machine input)).map fun r =>
    (r.2.machine.config.BiTape.head.toList ++
      r.2.machine.config.BiTape.right.toList.filterMap id,
      r.2.machine.headPos, r.1.tell.steps, r.1.tell.cellsAllocated, r.2.machine.cellsAllocated.card)

attribute [local simp] execute_while_succ step
  TMState.init SingleTapeTM.initCfg BiTape.mk₁ BiTape.nil
  BiTape.moveLeft BiTape.moveRight BiTape.write
  StackTape.head StackTape.tail StackTape.mapSome StackTape.nil StackTape.cons
  StackTape.length
  identity writeBit flipBit seekRightBlank seekLeftBlank seekLeftEnd
  appendBit complementRight complementBlock eraseLeft eraseToLeft eraseBlock carryRight increment

example : observe (do [TMQuery machine] identity machine) [true, false] =
    some ([true, false], 0, 0, 0, 2) := by simp

example : observe (do [TMQuery machine] writeBit machine true) [] =
    some ([true], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] flipBit machine) [] =
    some ([], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] flipBit machine) [false, true] =
    some ([true, true], 0, 0, 0, 2) := by simp

example : observe (do [TMQuery machine] seekRightBlank machine) [true, false] =
    some ([], 2, 2, 1, 3) := by simp

example : observe (do [TMQuery machine]
    seekRightBlank machine
    seekLeftEnd machine) [true, false] = some ([true, false], 0, 6, 2, 4) := by simp

example : observe (do [TMQuery machine] eraseBlock machine) [] =
    some ([], 0, 2, 1, 2) := by simp

example : observe (do [TMQuery machine] eraseBlock machine) [true, false, true] =
    some ([], 0, 8, 2, 5) := by simp

example : observe (do [TMQuery machine] appendBit machine false) [true, false] =
    some ([true, false, false], 0, 6, 2, 4) := by simp

example : observe (do [TMQuery machine] complementBlock machine) [true, false, true] =
    some ([false, true, false], 0, 8, 2, 5) := by simp

example : observe (do [TMQuery machine] increment machine) [] =
    some ([true], 0, 2, 1, 2) := by simp

example : observe (do [TMQuery machine] increment machine) [false, true] =
    some ([true, true], 0, 2, 1, 3) := by simp

-- Carry overflow extends the word by one bit and restores the head.
example : observe (do [TMQuery machine] increment machine) [true, true, true] =
    some ([false, false, false, true], 0, 8, 2, 5) := by simp

-- The second routine revisits the first routine's cells; space history is not reset.
example : observe (do [TMQuery machine]
    appendBit machine true
    complementBlock machine) [true, false] = some ([false, true, false], 0, 14, 3, 5) := by simp

-- Existing history and an arbitrary head origin are respected by the same fixed program.
example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        headPos := 37
        cellsAllocated := Finset.Icc 37 40
        cellsVisited := {37, 38}}
    (execute 100 (do [TMQuery machine] appendBit machine true) initial).map
      (fun r => (r.2.machine.headPos, r.1.tell.cellsAllocated, r.2.machine.cellsAllocated.card)) =
        some (37, 1, 5) := by simp [Int.card_Icc]

-- Generic correctness and complexity do not rely on these particular test inputs.
example (input : List Bool) : binaryValue (incrementBits input) = binaryValue input + 1 :=
  binaryValue_incrementBits input

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (increment machine) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsAllocated ≤ 2 * input.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * input.length + 2) :=
  (increment_computes (tm := machine)).space input s hs

-- Composition computes function composition and adds the phase bounds on the intermediate word.
example : Computes (do [TMQuery machine]
    appendBit machine true
    complementBlock machine)
      ((List.map Bool.not) ∘ (fun bits => bits ++ [true]))
      (fun bits => (2 * bits.length + 2) + (2 * (bits ++ [true]).length + 2)) :=
  (appendBit_computes (tm := machine) true).comp (complementBlock_computes (tm := machine))

/--
This pipeline appends `true` to the input, negates every bit of the resulting word, and then adds
one with the least significant bit first. It composes the three verified computers so that their
programs and correctness proofs are carried together.
-/
def pipeline :=
  appendBitComputer (tm := machine) true ≫ₜ
    complementBlockComputer (tm := machine) ≫ₜ incrementComputer (tm := machine)

example : observe pipeline.program [true, false] = some ([true, true, false], 0, 16, 3, 5) := by
  simp [pipeline, appendBitComputer, complementBlockComputer, incrementComputer]

-- The proof is carried by the composite value and applies to every input and history.
example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes pipeline.program s cost final ∧
      final.config = {s.config with
        BiTape := BiTape.mk₁ (incrementBits ((input ++ [true]).map Bool.not))} ∧
      final.headPos = s.headPos ∧
      cost.steps ≤ (2 * input.length + 2) +
        ((2 * (input ++ [true]).length + 2) +
          (2 * ((input ++ [true]).map Bool.not).length + 2)) :=
  pipeline.correct input s hs

example (first second : List Bool) :
    BooleanTapeEncoding.unpair (BooleanTapeEncoding.pair first second) = some (first, second) := by
  simp

example : BooleanTapeEncoding.unpair [true, true, false, true] = none := by
  simp [BooleanTapeEncoding.unpair, BooleanTapeEncoding.readLength]

/--
`observeComponent component input` runs the component's stored program on the Boolean input tape
with 1000 units of interpreter fuel. On success it reports the nonblank output symbols at and to the
right of the final head, the head coordinate, the head-move count, and the additional and total
tape-allocation counts.
-/
def observeComponent {ι : Type} {pre : ι → TMState machine → Prop}
    {post : ι → TMState machine → TMCost → TMState machine → Prop}
    (component : Component machine pre post) (input : List Bool) :
    Option (List Bool × ℤ × ℕ × ℕ × ℕ) :=
  (execute 1000 component.program (TMState.init machine input)).map fun (result, final) =>
    (final.machine.config.BiTape.head.toList ++
      final.machine.config.BiTape.right.toList.filterMap id,
      final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
      final.machine.cellsAllocated.card)

example : observeComponent (Copying.duplicateComputer (tm := machine)) [] =
    some ([false], -1, 5, 3, 4) := by decide
example : observeComponent (Copying.duplicateComputer (tm := machine)) [true] =
    some ([true, false, true, true], -2, 20, 6, 7) := by decide
example : observeComponent (Copying.duplicateComputer (tm := machine)) [true, false] =
    some ([true, true, false, true, false, true, false], -3, 43, 8, 10) := by decide

-- Actual fan-out includes physical copying and the framed right-word computation.
example : observeComponent (duplicateAppendRightComputer (tm := machine) true) [] =
    some ([false, true], -1, 9, 3, 4) := by decide
example : observeComponent (duplicateAppendRightComputer (tm := machine) true) [true, false] =
    some ([true, true, false, true, false, true, false, true], -3, 59, 8, 10) := by decide

example :
    let initial : TMState machine := {TMState.init machine [true, false] with
      headPos := 37
      cellsAllocated := Finset.Icc 35 41
      cellsVisited := Finset.Icc 35 41}
    (execute 1000 (Copying.duplicateComputer (tm := machine)).program initial).map
      (fun (result, final) => (final.machine.headPos, result.tell.steps,
        result.tell.cellsAllocated, final.machine.cellsAllocated.card)) = some (34, 43, 3, 10) := by
  decide

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final,
      Completes (duplicateAppendRightComputer (tm := machine) true).program s cost final ∧
      final.config = {s.config with
        BiTape := BiTape.mk₁ (BooleanTapeEncoding.pair input (input ++ [true]))} ∧
      final.headPos = s.headPos - (input.length + 1 : ℕ) ∧
      cost.steps ≤ 4 * input.length ^ 2 + 17 * input.length + 9 :=
  (duplicateAppendRightComputer (tm := machine) true).correct input s hs

/--
This machine supplies a tape alphabet containing Boolean values tagged by `.inl` and one separator
represented by `.inr 0`. It has a single control-state label, and its transition table preserves the
current symbol and halts. The first-word query program supplies the operations used in the separator
examples.
-/
abbrev separatorMachine : SingleTapeTM (Alphabet.Extended Bool 1) where
  State := PUnit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/--
`observeFirstWord input` runs the verified first-word program on the separator machine with 1000
units of interpreter fuel. On success it reports the retained nonblank symbols, the restored head
coordinate, the head-move count, and the total allocated tape space. It returns `none` if execution
runs out of fuel.
-/
def observeFirstWord (input : List (Alphabet.Extended Bool 1)) :
    Option (List (Alphabet.Extended Bool 1) × ℤ × ℕ × ℕ) :=
  (execute 1000 (firstWord separatorMachine) (TMState.init separatorMachine input)).map
    fun (result, final) =>
      (final.machine.config.BiTape.head.toList ++
        final.machine.config.BiTape.right.toList.filterMap id,
        final.machine.headPos, result.tell.steps, final.machine.spaceUsed)

example : observeFirstWord [.inl true, .inl false, .inr 0, .inl false] =
    some ([.inl true, .inl false], 0, 10, 6) := by decide

example : observeFirstWord [] = some ([], 0, 4, 3) := by decide

example : observeFirstWord [.inr 0] = some ([], 0, 4, 3) := by decide

example : observeFirstWord [.inl true, .inl false] =
    some ([.inl true, .inl false], 0, 8, 5) := by decide

example : observeFirstWord [.inl true, .inr 0, .inr 0, .inl false] =
    some ([.inl true], 0, 10, 6) := by decide

/--
The language containing only the empty Boolean word belongs to `P`. Its Turing machine program
appends `true` and accepts exactly when the resulting word is `[true]`, using the polynomial-time
witness from `TMComplexity.lean`.
-/
theorem emptyWord_inP : P (fun input : List Bool => input = []) := by
  refine ⟨fun input => input ++ [true], [true],
    ⟨appendBitPolyTimeComputable (tm := machine) true⟩, ?_⟩
  intro input
  simp

example : NP (fun input : List Bool => input = []) := NP.ofP emptyWord_inP

/--
This function executes a polynomial-time Turing machine witness using its own machine and
reports the output word, head coordinate, and head-move count.
-/
def observePolyTime {f : List Bool → List Bool} (computer : TMQuery.PolyTimeComputable f)
    (input : List Bool) : Option (List Bool × ℤ × ℕ) :=
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  (execute 1000 computer.program (TMState.init computer.tm input)).map fun (result, final) =>
    (final.machine.config.BiTape.head.toList ++
      final.machine.config.BiTape.right.toList.filterMap id,
      final.machine.headPos, result.tell.steps)

-- Conversion to the foundational witness preserves the copier's shifted output coordinate.
example : observePolyTime (Copying.duplicatePolyTimeComputable (tm := machine)) [true, false] =
    some ([true, true, false, true, false, true, false], -3, 43) := by decide +kernel

-- The concrete witnesses compose through the existing polynomial-time composition theorem.
example : observePolyTime
    ((appendBitPolyTimeComputable (tm := machine) true).comp
      (incrementPolyTimeComputable (tm := machine))) [true, true] =
    some ([false, false, false, true], 0, 14) := by decide +kernel

end AlgoleanTests.SingleTapeTuringMachines
