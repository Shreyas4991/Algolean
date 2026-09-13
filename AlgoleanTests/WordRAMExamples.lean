/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-!
# Word-RAM examples

Programs demonstrating mutable memory, indirect addressing, arithmetic overflow, bitwise operations,
and branch-dependent query costs. Every runtime word operation in these examples is a query.
Queries use Algolean's existing coercion into `Prog`; typed bindings fix the result type, and
explicit widths disambiguate queries whose operands are all literals.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMExamples

open Algolean.Algorithms Algolean.Algorithms.WordRAM

/-- Increment a memory cell using a load, a word addition, and a store. -/
def increment (addr : Word w) : Prog (WordRAM w) Unit := do
  let x : Word w ← load addr
  let y : Word w ← binop .add x 1
  store addr y

-- The increment works for arbitrary initial memory and preserves every other cell.
example (mem : Memory w) (addr : Word w) :
    ((increment addr).evalM natCost mem).2 addr = mem addr + 1 := by
  change Function.update mem addr (mem addr + 1) addr = _
  simp

example (mem : Memory w) (addr other : Word w) (h : other ≠ addr) :
    ((increment addr).evalM natCost mem).2 other = mem other := by
  change Function.update mem addr (mem addr + 1) other = _
  simp [h]

example (mem : Memory w) (addr : Word w) :
    ((increment addr).costM natCost mem).1 = 3 := rfl

/-- Write the largest byte, increment it, and read the wrapped result. -/
def overflow : Prog (WordRAM 8) (Word 8) := do
  store (w := 8) 7 255
  increment 7
  load (w := 8) 7

-- Evaluation returns the word and final memory; cost evaluation counts the queries.
example : (overflow.evalM natCost Memory.zero).1 = 0 := by decide
example : (overflow.costM natCost Memory.zero).1 = 5 := rfl
example : (overflow.evalM natCost Memory.zero).2 7 = 0 := by decide

/-- A pointer stored in one cell selects the cell to increment. -/
def indirectIncrement : Prog (WordRAM 8) (Word 8) := do
  store (w := 8) 0 42
  store (w := 8) 42 9
  let addr : Word 8 ← load (w := 8) 0
  increment addr
  load addr

example : (indirectIncrement.evalM natCost Memory.zero).1 = 10 := by decide
example : (indirectIncrement.costM natCost Memory.zero).1 = 7 := rfl
example : (indirectIncrement.evalM natCost Memory.zero).2 0 = 42 := by decide

/-- Replace a cell only if its unsigned value is below a threshold; return whether it changed.
The load and comparison cost two queries, with one additional query if the store is executed. -/
def raiseTo (addr threshold : Word w) : Prog (WordRAM w) Bool := do
  let x : Word w ← load addr
  let below : Bool ← cmp .ult x threshold
  if below then
    store addr threshold
    return true
  else
    return false

example : ((raiseTo (w := 8) 4 10).evalM natCost Memory.zero).1 = true := by
  decide

example : ((raiseTo (w := 8) 4 10).costM natCost Memory.zero).1 = 3 := rfl

example : ((raiseTo (w := 8) 4 10).evalM natCost Memory.zero).2 4 = 10 := by
  decide

-- 255 is larger than 10 in the unsigned ordering, so this execution skips the store.
example : ((raiseTo (w := 8) 4 10).evalM natCost (fun _ => 255)).1 = false := by
  decide

example : ((raiseTo (w := 8) 4 10).costM natCost (fun _ => 255)).1 = 2 := rfl

example : ((raiseTo (w := 8) 4 10).evalM natCost (fun _ => 255)).2 4 = 255 := by
  decide

/-- Evaluate one byte operation through the query interpreter. -/
def byteBinop (op : BinOp) (x y : Word 8) : Word 8 :=
  (Prog.evalM (binop op x y : Prog (WordRAM 8) (Word 8)) natCost Memory.zero).1

example : byteBinop .sub 0 1 = 255 := by decide
example : byteBinop .band 170 204 = 136 := by decide
example : byteBinop .bor 170 204 = 238 := by decide
example : byteBinop .bxor 170 204 = 102 := by decide
example : byteBinop .shl 129 1 = 2 := by decide
example : byteBinop .shr 128 1 = 64 := by decide

-- Shift counts are not masked modulo the word width, and right shifts do not extend the sign bit.
example : byteBinop .shl 255 8 = 0 := by decide
example : byteBinop .shr 255 8 = 0 := by decide
example : byteBinop .shl 255 9 = 0 := by decide
example : byteBinop .shr 255 255 = 0 := by decide

example :
    (Prog.evalM (bnot (w := 8) 170 : Prog (WordRAM 8) (Word 8)) natCost Memory.zero).1 = 85 := by
  decide

example :
    (Prog.evalM (cmp .eq (w := 8) 42 42 : Prog (WordRAM 8) Bool) natCost Memory.zero).1 = true := by
  decide

example :
    (Prog.evalM (cmp .eq (w := 8) 42 43 : Prog (WordRAM 8) Bool) natCost Memory.zero).1 =
      false := by
  decide

-- Word-only operations leave arbitrary memory unchanged.
example (mem : Memory w) (op : BinOp) (x y : Word w) :
    (Prog.evalM (binop op x y : Prog (WordRAM w) (Word w)) natCost mem).2 = mem := rfl

-- The same programs can track time and footprint without changing their definitions.
example (mem : Memory w) (addr : Word w) :
    ((increment addr).costM footprintCost mem).1 = ⟨3, {addr}⟩ := by
  change (⟨1, {addr}⟩ : RAMCost w) + (⟨1, ∅⟩ + (⟨1, {addr}⟩ + 0)) = ⟨3, {addr}⟩
  ext <;> simp

/-- Reuse a cell across several increments. -/
def repeatIncrement (addr : Word w) : Nat → Prog (WordRAM w) Unit
  | 0 => pure ()
  | n + 1 => do
    increment addr
    repeatIncrement addr n

example : ((repeatIncrement (w := 8) 7 0).costM footprintCost Memory.zero).1 = 0 := rfl

-- Twelve operations still access just one cell, even though it is read and written repeatedly.
example : ((repeatIncrement (w := 8) 7 4).costM footprintCost Memory.zero).1.time = 12 := rfl
example : ((repeatIncrement (w := 8) 7 4).costM footprintCost Memory.zero).1.space = 1 := by
  decide

example : (indirectIncrement.costM footprintCost Memory.zero).1.addresses = {0, 42} := by
  decide
example : (indirectIncrement.costM footprintCost Memory.zero).1.time = 7 := rfl
example : (indirectIncrement.costM footprintCost Memory.zero).1.space = 2 := by decide

-- Exclude the input cell at address 0; include an unread input cell at address 1 for total space.
example : (indirectIncrement.costM footprintCost Memory.zero).1.auxiliarySpace {0, 1} = 1 := by
  decide
example : (indirectIncrement.costM footprintCost Memory.zero).1.totalSpace {0, 1} = 3 := by
  decide

-- Both branches access the same cell, but only one branch writes it.
example : ((raiseTo (w := 8) 4 10).costM footprintCost Memory.zero).1 = ⟨3, {4}⟩ := by
  decide
example : ((raiseTo (w := 8) 4 10).costM footprintCost (fun _ => 255)).1 = ⟨2, {4}⟩ := by
  decide

/-- Load a pointer from a cell and then read the pointed-to cell. -/
def followPointer (slot : Word w) : Prog (WordRAM w) (Word w) := do
  let addr : Word w ← load slot
  load addr

-- The footprint depends on the address actually loaded, including when the pointer aliases itself.
example : ((followPointer (w := 8) 0).costM footprintCost Memory.zero).1 = ⟨2, {0}⟩ := by
  decide
example : ((followPointer (w := 8) 0).costM footprintCost (fun _ => 9)).1 = ⟨2, {0, 9}⟩ := by
  decide

/-- Word arithmetic, complement, and comparison require no memory queries. -/
def wordOnly (x y : Word w) : Prog (WordRAM w) Bool := do
  let sum : Word w ← binop .add x y
  let inverted : Word w ← bnot sum
  cmp .eq inverted x

example (mem : Memory w) (x y : Word w) :
    ((wordOnly x y).costM footprintCost mem).1 = ⟨3, ∅⟩ := by
  change (⟨1, ∅⟩ : RAMCost w) + (⟨1, ∅⟩ + (⟨1, ∅⟩ + 0)) = ⟨3, ∅⟩
  ext <;> simp

end AlgoleanTests.WordRAMExamples
