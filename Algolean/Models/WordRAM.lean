/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.QueryModel
public import Mathlib.Data.Finset.Card

/-!
# Strict Word-RAM queries

`WordRAM w k` describes a machine with `k` registers and `2 ^ w` memory cells.
Each register and memory cell holds a `w`-bit word. `RAMState` holds the memory,
register file, and comparison flags.

Inputs are supplied through the initial machine state. Instructions access words through
register identifiers, and comparisons write machine-local flags. Structured branches and
loops inspect flags inside the model. Every query returns `Unit`, so machine data
cannot enter a Lean continuation.

Words and addresses have the same fixed width. Arithmetic wraps modulo `2 ^ w`; comparisons
are unsigned; shifts are logical and return zero when the shift amount is at least `w`.
All `2 ^ w` addresses are available. `RAMState.zero` initializes memory, registers, and flags.
Allocation and input encoding are not part of this query type.
The definitions also support the degenerate width zero; ordinary word-RAM applications use `w > 0`.

Uniform algorithms use a fixed `Prog (WordRAM w k) Unit` across inputs at a given word width
and register count, with outputs observed in the final machine state. Unit-valued queries
prevent runtime data from escaping the model; they do not prevent Lean code from constructing
different programs for different inputs or input lengths.

`RAMCost.space` counts distinct accessed cells in words. `RAMCost.auxiliarySpace` excludes an input
region. `RAMCost.totalSpace` includes that region even if some input cells are unread.
Registers and flags do not contribute to this accessed-memory footprint.

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

/-- A register identifier, not a word value. There are exactly `k` available registers. -/
abbrev Register (k : Nat) := Fin k

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

/-- Physical memory, word registers, and machine-local comparison flags. -/
@[ext, grind]
structure RAMState (w k : Nat) where
  /-- The word stored at each memory address. -/
  Memory : WordRAM.Memory w
  /-- The words held in the fixed register file. -/
  Registers : Register k → Word w
  /-- One flag per comparison operation, separate from word registers. -/
  Flags : CmpOp → Bool := fun _ => false

/-- Zero-initialized memory and registers, with cleared comparison flags. -/
def RAMState.zero : RAMState w k := ⟨Memory.zero, fun _ => 0, fun _ => false⟩

/-- Update a register with a value computed from the incoming state. -/
def RAMState.writeRegister (s : RAMState w k) (r : Register k) (value : Word w) : RAMState w k :=
  { s with Registers := Function.update s.Registers r value }

/-- Update one flag, retaining memory, registers, and the other flags. -/
def RAMState.writeFlag (s : RAMState w k) (op : CmpOp) (value : Bool) : RAMState w k :=
  { s with Flags := Function.update s.Flags op value }

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

/-- Register instructions and structured control. Every query returns `Unit`, keeping
computed words and comparison results inside the machine state. -/
inductive WordRAM (w k : Nat) : Type → Type where
  /-- Leave the machine state unchanged, costing one time unit. -/
  | nop : WordRAM w k Unit
  | set (dst : WordRAM.Register k) (value : WordRAM.Word w) : WordRAM w k Unit
  | copy (dst src : WordRAM.Register k) : WordRAM w k Unit
  | load (dst addr : WordRAM.Register k) : WordRAM w k Unit
  | store (addr src : WordRAM.Register k) : WordRAM w k Unit
  | binop (op : WordRAM.BinOp) (dst x y : WordRAM.Register k) : WordRAM w k Unit
  | bnot (dst src : WordRAM.Register k) : WordRAM w k Unit
  | cmp (op : WordRAM.CmpOp) (x y : WordRAM.Register k) : WordRAM w k Unit
  | clearFlag (op : WordRAM.CmpOp) : WordRAM w k Unit
  | branchCode (op : WordRAM.CmpOp) (yes no : List (WordRAM w k Unit)) : WordRAM w k Unit
  | whileCode (op : WordRAM.CmpOp) (body : List (WordRAM w k Unit)) : WordRAM w k Unit

namespace WordRAM

/-- Machine data cannot pass to a continuation through an instruction's result. -/
theorem result_type (q : WordRAM w k α) : α = Unit := by
  cases q <;> rfl

/-- Time and the set of memory addresses accessed by an execution. -/
@[ext]
structure RAMCost (w : Nat) where
  /-- Number of primitive word and flag operations; branch and loop selection are free. -/
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

attribute [grind =] zero_time zero_addresses add_time add_addresses

instance : AddCommMonoid (RAMCost w) where
  nsmul := nsmulRec
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_assoc a b c := by ext <;> simp [Nat.add_assoc, Finset.union_assoc]
  add_comm a b := by ext <;> simp [Nat.add_comm, Finset.union_comm]

/-- Normalize addition to the time sum and the union of accessed addresses. -/
@[simp, grind =] theorem mk_add (time : Nat) (addresses : Finset (Word w)) (c : RAMCost w) :
    (⟨time, addresses⟩ : RAMCost w) + c = ⟨time + c.time, addresses ∪ c.addresses⟩ := rfl

/-- Memory footprint in words: each accessed address is counted once. -/
def space (c : RAMCost w) : Nat := c.addresses.card

/-- Accessed words outside the designated input region. -/
def auxiliarySpace (c : RAMCost w) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses \ inputRegion).card

/-- Words in the footprint or the designated input region, including unread input cells. -/
def totalSpace (c : RAMCost w) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses ∪ inputRegion).card

end RAMCost

end WordRAM

end Algolean.Algorithms
