/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAMLinearSearch

/-!
# Register-based word-RAM examples

Instructions operate on register identifiers. Values are inspected only in the final machine
state, outside the program. The tracking interpreter uses `(RAMState, probedCells)` as its state;
`costM` counts queries, and `RAMCost.ofRun` reads the time and probe set from that execution.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMExamples

open Algolean.Algorithms Algolean.Algorithms.WordRAM

abbrev r0 : Register 4 := 0
abbrev r1 : Register 4 := 1
abbrev r2 : Register 4 := 2
abbrev r3 : Register 4 := 3

/-- Increment memory through an address register, a scratch register, and a register holding one. -/
def increment (w : Nat) : Prog (WordRAM w 4) Unit := do
  load (w := w) r1 r0
  binop (w := w) .add r1 r1 r3
  store (w := w) r0 r1

/-- Set up the address and constant registers, then increment a maximal byte. -/
def overflow : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 7
  set (w := 8) r1 255
  set (w := 8) r3 1
  store (w := 8) r0 r1
  increment 8

example : (overflow.evalM natCost RAMState.zero).2.Memory 7 = 0 := by decide
example : (overflow.evalM natCost RAMState.zero).2.Registers r1 = 0 := by decide
example : (overflow.costM natCost RAMState.zero).1 = 7 := by decide
example : (RAMCost.ofRun (overflow.costM timeAndSpaceCost (RAMState.zero, ∅))).addresses =
    {7} := by decide

/-- Copying a word between registers is an explicit charged instruction. -/
def copyExample : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 42
  copy (w := 8) r1 r0
  set (w := 8) r0 7

example : (copyExample.evalM natCost RAMState.zero).2.Registers r1 = 42 := by decide
example : (copyExample.costM natCost RAMState.zero).1 = 3 := by decide

/-- An address register can itself be overwritten by a load of a pointer. -/
def followPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  load (w := 8) r1 r0

/-- The pointer cell at zero chooses the next cell to probe. -/
def pointerState (ptr : Word 8) : RAMState 8 4 :=
  ⟨fun addr => if addr = 0 then ptr else 42, fun _ => 0⟩

-- The first load probes the old r0 (zero), even though it overwrites r0 with nine.
example : (followPointer.evalM natCost (pointerState 9)).2.Registers r1 = 42 := by decide
example : (RAMCost.ofRun (followPointer.costM timeAndSpaceCost (pointerState 9, ∅))).addresses =
    {0, 9} := by decide
example : (RAMCost.ofRun (followPointer.costM timeAndSpaceCost (pointerState 0, ∅))).addresses =
    {0} := by decide
example : (followPointer.costM timeAndSpaceCost (pointerState 9, ∅)).1 = 2 := by decide

-- Register words are counted in addition to the distinct probed cells.
example : (RAMCost.ofRun (followPointer.costM timeAndSpaceCost (pointerState 9, ∅))).space =
    6 := by decide
example : (RAMCost.ofRun (followPointer.costM timeAndSpaceCost
    (pointerState 9, ∅))).auxiliarySpace {0, 1} = 5 := by decide
example : (RAMCost.ofRun (followPointer.costM timeAndSpaceCost
    (pointerState 9, ∅))).totalSpace {0, 1} = 7 := by decide

/-- Store through the pointer just loaded into r0. -/
def storeThroughPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  store (w := 8) r0 r0

example : (storeThroughPointer.evalM natCost (pointerState 9)).2.Memory 9 = 9 := by decide
example : (RAMCost.ofRun (storeThroughPointer.costM timeAndSpaceCost
    (pointerState 9, ∅))).addresses = {0, 9} := by decide

/-- Repeat probes without allocating additional register slots. -/
def repeatIncrement (w : Nat) : Nat → Prog (WordRAM w 4) Unit
  | 0 => pure ()
  | n + 1 => do
    increment w
    repeatIncrement w n

def incrementState : RAMState 8 4 :=
  ⟨fun _ => 0, fun r => if r = r0 then 7 else if r = r3 then 1 else 0⟩

example : ((repeatIncrement 8 4).evalM natCost incrementState).2.Memory 7 = 4 := by decide
example : ((repeatIncrement 8 4).costM timeAndSpaceCost (incrementState, ∅)).1 = 12 := by decide
example : (RAMCost.ofRun ((repeatIncrement 8 4).costM timeAndSpaceCost
    (incrementState, ∅))).space = 5 := by decide

/-- Compare through registers and perform the store only on the true branch. -/
def raiseTo : Prog (WordRAM 8 4) Bool := do
  load (w := 8) r1 r0
  let below : Bool ← cmp (w := 8) .ult r1 r2
  if below then
    store (w := 8) r0 r2
    return true
  else return false

def raiseState (value : Word 8) : RAMState 8 4 :=
  ⟨fun _ => value, fun r => if r = r0 then 4 else if r = r2 then 10 else 0⟩

example : (raiseTo.evalM natCost (raiseState 0)).1 = true := by decide
example : (raiseTo.costM natCost (raiseState 0)).1 = 3 := by decide
example : (raiseTo.evalM natCost (raiseState 0)).2.Memory 4 = 10 := by decide
example : (raiseTo.evalM natCost (raiseState 255)).1 = false := by decide
example : (raiseTo.costM natCost (raiseState 255)).1 = 2 := by decide
example : (raiseTo.evalM natCost (raiseState 255)).2.Memory 4 = 255 := by decide

/-- Inspect a destination register after executing a single arithmetic instruction.
The destination aliases a source, exercising reads from the old register file. -/
def byteBinop (op : BinOp) (x y : Word 8) : Word 8 :=
  (Prog.evalM (binop (w := 8) op r0 r0 r1 : Prog (WordRAM 8 4) Unit) natCost
    ⟨fun _ => 0, fun r => if r = r0 then x else y⟩).2.Registers r0

example : byteBinop .sub 0 1 = 255 := by decide
example : byteBinop .band 170 204 = 136 := by decide
example : byteBinop .bor 170 204 = 238 := by decide
example : byteBinop .bxor 170 204 = 102 := by decide
example : byteBinop .shl 129 1 = 2 := by decide
example : byteBinop .shr 128 1 = 64 := by decide
example : byteBinop .shl 255 8 = 0 := by decide
example : byteBinop .shr 255 8 = 0 := by decide
example : byteBinop .shl 255 9 = 0 := by decide
example : byteBinop .shr 255 255 = 0 := by decide

/-- Arithmetic and complement use registers without probing memory. -/
def wordOnly : Prog (WordRAM 8 4) Bool := do
  binop (w := 8) .add r2 r0 r1
  bnot (w := 8) r2 r2
  cmp (w := 8) .eq r2 r0

example : (RAMCost.ofRun (wordOnly.costM timeAndSpaceCost (RAMState.zero, ∅))).addresses =
    ∅ := by decide
example : (RAMCost.ofRun (wordOnly.costM timeAndSpaceCost (RAMState.zero, ∅))).space = 4 := by
  decide
example : (wordOnly.costM natCost RAMState.zero).1 = 3 := by decide

section LinearSearch

def searchInput : Array (BitVec 8) := #[12, 7, 42, 7, 99]

def searchExample : Prog (WordRAM 8 4) (Option (Register 4)) :=
  linearSearch 8 searchInput.size

-- The key is supplied in the initial register file; the answer remains in the final register file.
example : (searchExample.evalM natCost (linearSearchState searchInput 7)).1 =
    some LinearSearch.index := by decide
example : (searchExample.evalM natCost (linearSearchState searchInput 7)).2.Registers
    LinearSearch.index = 1 := by decide
example : (searchExample.evalM natCost (linearSearchState searchInput 99)).2.Registers
    LinearSearch.index = 4 := by decide
example : (searchExample.evalM natCost (linearSearchState searchInput 18)).1 = none := by decide

-- Two initialization queries are included in all time counts.
example : (searchExample.costM natCost (linearSearchState searchInput 12)).1 = 4 := by decide
example : (searchExample.costM natCost (linearSearchState searchInput 7)).1 = 7 := by decide
example : (searchExample.costM natCost (linearSearchState searchInput 99)).1 = 16 := by decide
example : (searchExample.costM natCost (linearSearchState searchInput 18)).1 = 17 := by decide

example : (RAMCost.ofRun (searchExample.costM timeAndSpaceCost
    (linearSearchState searchInput 7, ∅))).addresses = {0, 1} := by decide
example (target : Word 8) : (RAMCost.ofRun (searchExample.costM timeAndSpaceCost
    (linearSearchState searchInput target, ∅))).auxiliarySpace (inputRegion searchInput) = 4 :=
  linearSearch_auxiliarySpace searchInput target
example (target : Word 8) : (RAMCost.ofRun (searchExample.costM timeAndSpaceCost
    (linearSearchState searchInput target, ∅))).totalSpace (inputRegion searchInput) = 9 :=
  linearSearch_totalSpace searchInput target (by decide)

example : ((linearSearch 8 0).evalM natCost (linearSearchState #[] 7)).1 = none := by decide
example : ((linearSearch 8 0).costM natCost (linearSearchState #[] 7)).1 = 2 := by decide

-- All cells of a two-bit-addressed memory are searchable, including the last cell.
example : ((linearSearch 2 4).evalM natCost (linearSearchState #[0, 1, 2, 3] 3)).2.Registers
    LinearSearch.index = 3 := by decide
example : ((linearSearch 0 1).evalM natCost (linearSearchState #[0] 0)).1 =
    some LinearSearch.index := by decide

end LinearSearch

end AlgoleanTests.WordRAMExamples
