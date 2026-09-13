/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.ModelM
public import Mathlib.Data.Finset.Card

/-!
# Word-RAM queries

`WordRAM w` provides memory access, arithmetic, bitwise operations, and comparisons on
`w`-bit words. `WordRAM.natCost` interprets these queries in mutable memory and
charges one per query. Algorithms use the usual `Prog (WordRAM w)` combinators.
`WordRAM.timeAndSpaceCost` also records the set of addresses accessed. Its cost algebra adds time
and unions address sets, so repeated accesses increase time without counting a cell more than once.

Words and addresses have the same fixed width. Arithmetic wraps modulo `2 ^ w`; comparisons
are unsigned; shifts are logical and return zero when the shift amount is at least `w`.
All `2 ^ w` addresses are available. The caller supplies initial memory, with `Memory.zero`
as a convenient starting point. Allocation and input encoding are not part of this query type.
The definitions also support the degenerate width zero; ordinary word-RAM applications use `w > 0`.

Costs count primitive queries. Sequencing and branching are supplied by `Prog` combinators and carry
no additional cost. Runtime word operations must be exposed as queries to contribute to this count;
arbitrary Lean computation in continuations is not charged.

`RAMCost.space` counts distinct accessed cells in words. `RAMCost.auxiliarySpace` excludes an input
region. `RAMCost.totalSpace` includes that region even if some input cells are unread.
This is an accessed-memory footprint, not peak live allocation or storage in Lean continuations.

## References

* Pat Morin, *Open Data Structures*, §1.4:
  https://opendatastructures.org/ods-java/1_4_Model_Computation.html
* Harvard CS125, Lecture 6, §§6.6–6.7 (word-RAM instructions and modular arithmetic):
  https://people.seas.harvard.edu/~cs125/fall16/lec6.pdf
-/

@[expose] public section

namespace Algolean.Algorithms

namespace WordRAM

/-- A fixed-width word, used for both data and addresses. -/
abbrev Word (w : Nat) := BitVec w

/-- The contents of every address in the word-sized address space. -/
abbrev Memory (w : Nat) := Word w → Word w

/-- Initial memory with every cell set to zero. -/
def Memory.zero : Memory w := fun _ => 0

/-- Binary word operations in the basic instruction set. -/
inductive BinOp where
  | add | sub
  | band | bor | bxor
  | shl | shr
  deriving DecidableEq, Repr

/-- Word comparisons; ordering is unsigned. -/
inductive CmpOp where
  | eq | ult
  deriving DecidableEq, Repr

/-- Evaluate a binary operation. Shift amounts use the full unsigned value of the second word. -/
def BinOp.eval : BinOp → Word w → Word w → Word w
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .bxor, x, y => x ^^^ y
  | .shl, x, y => x <<< y.toNat
  | .shr, x, y => x >>> y.toNat

/-- Evaluate an equality or unsigned less-than comparison. -/
def CmpOp.eval : CmpOp → Word w → Word w → Bool
  | .eq, x, y => decide (x = y)
  | .ult, x, y => decide (x.toNat < y.toNat)

end WordRAM

/-- Primitive word-RAM queries, indexed by the type of their result. -/
inductive WordRAM (w : Nat) : Type → Type where
  | load (addr : WordRAM.Word w) : WordRAM w (WordRAM.Word w)
  | store (addr value : WordRAM.Word w) : WordRAM w Unit
  | binop (op : WordRAM.BinOp) (x y : WordRAM.Word w) : WordRAM w (WordRAM.Word w)
  | bnot (x : WordRAM.Word w) : WordRAM w (WordRAM.Word w)
  | cmp (op : WordRAM.CmpOp) (x y : WordRAM.Word w) : WordRAM w Bool

namespace WordRAM

/-- Stateful word-RAM semantics with unit cost for every primitive query. -/
@[simps]
def natCost : ModelM (WordRAM w) (StateM (Memory w)) Nat where
  evalQuery
    | .load addr => do
      let mem ← get
      pure (mem addr)
    | .store addr value => modify (fun mem => Function.update mem addr value)
    | .binop op x y => pure (op.eval x y)
    | .bnot x => pure (~~~x)
    | .cmp op x y => pure (op.eval x y)
  cost _ := 1

/-- Time and the set of memory addresses accessed by an execution. -/
@[ext]
structure RAMCost (w : Nat) where
  /-- Number of primitive queries executed. -/
  time : Nat
  /-- Distinct addresses loaded from or stored to. -/
  addresses : Finset (Word w)
  deriving DecidableEq

namespace RAMCost

@[simps]
instance : Zero (RAMCost w) := ⟨0, ∅⟩

@[simps]
instance : Add (RAMCost w) where
  add a b := ⟨a.time + b.time, a.addresses ∪ b.addresses⟩

instance : AddCommMonoid (RAMCost w) where
  nsmul := nsmulRec
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_assoc a b c := by ext <;> simp [Nat.add_assoc, Finset.union_assoc]
  add_comm a b := by ext <;> simp [Nat.add_comm, Finset.union_comm]

/-- Memory footprint in words: each accessed address is counted once. -/
def space (c : RAMCost w) : Nat := c.addresses.card

/-- Accessed words outside the designated input region. -/
def auxiliarySpace (c : RAMCost w) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses \ inputRegion).card

/-- Words in the footprint or the designated input region, including unread input cells. -/
def totalSpace (c : RAMCost w) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses ∪ inputRegion).card

end RAMCost

/-- The unit-time model augmented with the set of addresses accessed by each query. -/
@[simps]
def timeAndSpaceCost : ModelM (WordRAM w) (StateM (Memory w)) (RAMCost w) where
  evalQuery := natCost.evalQuery
  cost
    | .load addr => ⟨1, {addr}⟩
    | .store addr _ => ⟨1, {addr}⟩
    | .binop _ _ _ => ⟨1, ∅⟩
    | .bnot _ => ⟨1, ∅⟩
    | .cmp _ _ _ => ⟨1, ∅⟩

/-- Tracking the memory footprint does not change a program's evaluation or final memory. -/
@[simp]
theorem evalM_timeAndSpaceCost (P : Prog (WordRAM w) α) :
    P.evalM timeAndSpaceCost = P.evalM natCost := rfl

end WordRAM

end Algolean.Algorithms
