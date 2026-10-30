/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Complexity

/-! # Executable examples and composed contracts for Boolean tape procedures -/

@[expose] public section

namespace AlgoleanTests.SingleTapeTuringMachines

open Algolean Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Cslib.Turing TMQuery

open scoped TMQuery

/-- A Boolean-tape machine with a single control-state label. -/
abbrev machine : SingleTapeTM Bool where
  State := PUnit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- Observe output only after execution, together with head position, time, and visited space. -/
@[simp] def observe (p : Prog (TMQuery machine) Unit) (input : List Bool) :
    Option (List Bool × ℤ × ℕ × ℕ × ℕ) :=
  (execute 100 p (TMState.init machine input)).map fun r =>
    (r.2.machine.config.BiTape.head.toList ++
      r.2.machine.config.BiTape.right.toList.filterMap id,
      r.2.machine.headPos, r.1.tell.steps, r.1.tell.cellsVisited, r.2.machine.cellsVisited.card)

attribute [local simp] execute_eq_runCode runCode step branch whileLoop
  TMState.init SingleTapeTM.initCfg BiTape.mk₁ BiTape.nil
  BiTape.moveLeft BiTape.moveRight BiTape.write
  StackTape.head StackTape.tail StackTape.mapSome StackTape.nil StackTape.cons
  identity writeBit flipBit seekRightBlank seekLeftBlank seekLeftEnd
  appendBit complementRight complementBlock eraseLeft eraseToLeft eraseBlock carryRight increment

example : observe (do [TMQuery machine] identity machine) [true, false] =
    some ([true, false], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] writeBit machine true) [] =
    some ([true], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] flipBit machine) [] =
    some ([], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] flipBit machine) [false, true] =
    some ([true, true], 0, 0, 0, 1) := by simp

example : observe (do [TMQuery machine] seekRightBlank machine) [true, false] =
    some ([], 2, 2, 2, 3) := by simp

example : observe (do [TMQuery machine]
    seekRightBlank machine
    seekLeftEnd machine) [true, false] = some ([true, false], 0, 6, 3, 4) := by simp

example : observe (do [TMQuery machine] eraseBlock machine) [] =
    some ([], 0, 2, 1, 2) := by simp

example : observe (do [TMQuery machine] eraseBlock machine) [true, false, true] =
    some ([], 0, 8, 4, 5) := by simp

example : observe (do [TMQuery machine] appendBit machine false) [true, false] =
    some ([true, false, false], 0, 6, 3, 4) := by simp

example : observe (do [TMQuery machine] complementBlock machine) [true, false, true] =
    some ([false, true, false], 0, 8, 4, 5) := by simp

example : observe (do [TMQuery machine] increment machine) [] =
    some ([true], 0, 2, 1, 2) := by simp

example : observe (do [TMQuery machine] increment machine) [false, true] =
    some ([true, true], 0, 2, 1, 2) := by simp

-- Carry overflow extends the word by one bit and restores the head.
example : observe (do [TMQuery machine] increment machine) [true, true, true] =
    some ([false, false, false, true], 0, 8, 4, 5) := by simp

-- The second routine revisits the first routine's cells; space history is not reset.
example : observe (do [TMQuery machine]
    appendBit machine true
    complementBlock machine) [true, false] = some ([false, true, false], 0, 14, 4, 5) := by simp

-- Existing history and an arbitrary head origin are respected by the same fixed program.
example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with headPos := 37, cellsVisited := {37, 38, 1000}}
    (execute 100 (do [TMQuery machine] appendBit machine true) initial).map
      (fun r => (r.2.machine.headPos, r.1.tell.cellsVisited, r.2.machine.cellsVisited.card)) =
        some (37, 2, 5) := by simp

-- Generic correctness and complexity do not rely on these particular test inputs.
example (input : List Bool) : binaryValue (incrementBits input) = binaryValue input + 1 :=
  binaryValue_incrementBits input

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (increment machine) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsVisited ≤ 2 * input.length + 2 ∧
      final.cellsVisited.card ≤ s.cellsVisited.card + (2 * input.length + 2) :=
  (increment_computes (tm := machine)).space input s hs

-- Composition computes function composition and adds the phase bounds on the intermediate word.
example : Computes (do [TMQuery machine]
    appendBit machine true
    complementBlock machine)
      ((List.map Bool.not) ∘ (fun bits => bits ++ [true]))
      (fun bits => (2 * bits.length + 2) + (2 * (bits ++ [true]).length + 2)) :=
  (appendBit_computes (tm := machine) true).comp (complementBlock_computes (tm := machine))

end AlgoleanTests.SingleTapeTuringMachines
