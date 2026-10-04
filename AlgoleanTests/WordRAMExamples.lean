/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch

/-!
# Register-based word-RAM examples

Instructions operate on register identifiers. Values are inspected only in the final machine
state, outside the program. Joint execution tracks time and distinct probed cells in
`runM`; its `RAMCost` output also counts the fixed register storage.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMExamples

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM

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

example : ((overflow.runM timeAndSpaceCost).run RAMState.zero).snd.Memory 7 = 0 := by decide

example : ((overflow.runM timeAndSpaceCost).run RAMState.zero).snd.Registers r1 = 0 := by decide

example : ((overflow.runM timeAndSpaceCost).run RAMState.zero).fst.tell.time = 7 := by decide

example : ((overflow.runM timeAndSpaceCost).run RAMState.zero).fst.tell.addresses =
    {7} := by decide

/-- Copying a word between registers is an explicit charged instruction. -/
def copyExample : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 42
  copy (w := 8) r1 r0
  set (w := 8) r0 7

example : ((copyExample.runM timeAndSpaceCost).run
    RAMState.zero).snd.Registers r1 = 42 := by decide

example : ((copyExample.runM timeAndSpaceCost).run RAMState.zero).fst.tell.time = 3 := by decide

/-- An address register can itself be overwritten by a load of a pointer. -/
def followPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  load (w := 8) r1 r0

/-- The pointer cell at zero chooses the next cell to probe. -/
def pointerState (ptr : Word 8) : RAMState 8 4 :=
  ⟨fun addr => if addr = 0 then ptr else 42, fun _ => 0⟩

-- The first load probes the old r0 (zero), even though it overwrites r0 with nine.
example : ((followPointer.runM timeAndSpaceCost).run
    (pointerState 9)).snd.Registers r1 = 42 := by decide

example : ((followPointer.runM timeAndSpaceCost).run (pointerState 9)).fst.tell.addresses =
    {0, 9} := by decide

example : ((followPointer.runM timeAndSpaceCost).run (pointerState 0)).fst.tell.addresses =
    {0} := by decide

example : ((followPointer.runM timeAndSpaceCost).run
    (pointerState 9)).fst.tell.time = 2 := by decide

-- Sequential composition accumulates time but counts repeated probes only once.
example :
    (((followPointer *> followPointer).runM timeAndSpaceCost).run
      (pointerState 0)).fst.tell = ⟨4, {0}⟩ := by
  apply RAMCost.ext <;> decide

-- Register words are counted in addition to the distinct probed cells.
example : ((followPointer.runM timeAndSpaceCost).run (pointerState 9)).fst.tell.space =
    6 := by decide

example : ((followPointer.runM timeAndSpaceCost).run
    (pointerState 9)).fst.tell.auxiliarySpace {0, 1} = 5 := by decide

example : ((followPointer.runM timeAndSpaceCost).run
    (pointerState 9)).fst.tell.totalSpace {0, 1} = 7 := by decide

/-- Store through the pointer just loaded into r0. -/
def storeThroughPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  store (w := 8) r0 r0

example : ((storeThroughPointer.runM timeAndSpaceCost).run
    (pointerState 9)).snd.Memory 9 = 9 := by decide

example : ((storeThroughPointer.runM timeAndSpaceCost).run
    (pointerState 9)).fst.tell.addresses = {0, 9} := by decide

/-- Repeat probes without allocating additional register slots. -/
def repeatIncrement (w : Nat) : Nat → Prog (WordRAM w 4) Unit
  | 0 => pure ()
  | n + 1 => do
    increment w
    repeatIncrement w n

def incrementState : RAMState 8 4 :=
  ⟨fun _ => 0, fun r => if r = r0 then 7 else if r = r3 then 1 else 0⟩

example : (((repeatIncrement 8 4).runM timeAndSpaceCost).run
    incrementState).snd.Memory 7 = 4 := by
  simp [repeatIncrement, increment, evalQuery, queryProbes,
    incrementState, r0, r1, r3, BinOp.eval]

example : (((repeatIncrement 8 4).runM timeAndSpaceCost).run
    incrementState).fst.tell.time = 12 := by
  simp [repeatIncrement, increment, evalQuery, queryProbes, incrementState, r0, r1, r3,
    BinOp.eval]

example : (((repeatIncrement 8 4).runM timeAndSpaceCost).run
    incrementState).fst.tell.space = 5 := by
  simp [repeatIncrement, increment, evalQuery, queryProbes,
    incrementState, r0, r1, r3, BinOp.eval, RAMCost.space]

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

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 0)).fst.ret = true := by decide

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 0)).fst.tell.time = 3 := by decide

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 0)).snd.Memory 4 = 10 := by decide

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 255)).fst.ret = false := by decide

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 255)).fst.tell.time = 2 := by decide

example : ((raiseTo.runM timeAndSpaceCost).run (raiseState 255)).snd.Memory 4 = 255 := by decide

/-- Inspect a destination register after executing a single arithmetic instruction.
The destination aliases a source, exercising reads from the old register file. -/
def byteBinop (op : BinOp) (x y : Word 8) : Word 8 :=
  ((Prog.runM (binop (w := 8) op r0 r0 r1 : Prog (WordRAM 8 4) Unit) timeAndSpaceCost).run
    (⟨fun _ => 0, fun r => if r = r0 then x else y⟩ : RAMState 8 4)).snd.Registers r0

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

example : ((wordOnly.runM timeAndSpaceCost).run RAMState.zero).fst.tell.addresses =
    ∅ := by decide

example : ((wordOnly.runM timeAndSpaceCost).run RAMState.zero).fst.tell.space = 4 := by
  decide

example : ((wordOnly.runM timeAndSpaceCost).run RAMState.zero).fst.tell.time = 3 := by decide

section WeakestPreconditions

open Cslib.FreeM Std.Do

local instance : HasHandler (WordRAM 8 4) (.arg (RAMCost 8 4) (.arg (RAMState 8 4) .pure)) :=
  timeAndSpaceCost.hasCostHandler

-- The same query execution establishes the loaded value, time, and distinct probed cells.
set_option mvcgen.warning false in
example :
    ⦃fun cost s => ⌜cost = 0 ∧ s = pointerState 9⌝⦄ followPointer
      ⦃⇓ _ cost s => ⌜cost.time = 2 ∧ cost.addresses = {0, 9} ∧ s.Registers r1 = 42⌝⦄ := by
  mvcgen [followPointer]
  simp_all [HasHandler.handler, evalQuery, queryProbes, pointerState, r0, r1, Finset.pair_comm]

end WeakestPreconditions

section LinearSearch

def searchInput : Array (BitVec 8) := #[12, 7, 42, 7, 99]

def searchExample : Prog (WordRAM 8 4) (Option (Register 4)) :=
  linearSearch 8 searchInput.size

attribute [local simp] searchExample searchInput linearSearch LinearSearch.loop
  evalQuery queryProbes Finset.pair_comm
  linearSearchState arrayMemory LinearSearch.index LinearSearch.key
  LinearSearch.one LinearSearch.value BinOp.eval CmpOp.eval timeAndSpaceCost

-- The key is supplied in the initial register file; the answer remains in the final register file.
example : ((searchExample.runM timeAndSpaceCost).run (linearSearchState searchInput 7)).fst.ret =
    some LinearSearch.index := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 7)).snd.Registers
    LinearSearch.index = 1 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 99)).snd.Registers
    LinearSearch.index = 4 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 18)).fst.ret = none := by
  simp

-- Two initialization queries are included in all time counts.
example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 12)).fst.tell.time = 4 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 7)).fst.tell.time = 7 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 99)).fst.tell.time = 16 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 18)).fst.tell.time = 17 := by
  simp

example : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput 7)).fst.tell.addresses = {0, 1} := by
  simp

example (target : Word 8) : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput target)).fst.tell.auxiliarySpace
      (inputRegion searchInput) = 4 :=
  linearSearch_auxiliarySpace searchInput target

example (target : Word 8) : ((searchExample.runM timeAndSpaceCost).run
    (linearSearchState searchInput target)).fst.tell.totalSpace
      (inputRegion searchInput) = 9 :=
  linearSearch_totalSpace searchInput target (by decide)

example : (((linearSearch 8 0).runM timeAndSpaceCost).run
    (linearSearchState #[] 7)).fst.ret = none := by
  simp

example : (((linearSearch 8 0).runM timeAndSpaceCost).run
    (linearSearchState #[] 7)).fst.tell.time = 2 := by
  simp

-- All cells of a two-bit-addressed memory are searchable, including the last cell.
example : (((linearSearch 2 4).runM timeAndSpaceCost).run
    (linearSearchState #[0, 1, 2, 3] 3)).snd.Registers
    LinearSearch.index = 3 := by
  simp

example : (((linearSearch 0 1).runM timeAndSpaceCost).run (linearSearchState #[0] 0)).fst.ret =
    some LinearSearch.index := by
  simp

end LinearSearch

end AlgoleanTests.WordRAMExamples
