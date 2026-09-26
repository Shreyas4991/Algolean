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

`WordRAM w k` operates on `w`-bit words held in memory and exactly `k` registers.
Registers are identifiers (`Fin k`), and data instructions write their result into a destination
register and return `Unit`. Comparisons read registers and return `Bool` for control flow.
Literals are introduced by the charged `set` instruction; input values can also be supplied in
`RAMState`. The program observes computed words only through register-based instructions.

Words and addresses have the same fixed width. Arithmetic wraps modulo `2 ^ w`;
- comparisons are unsigned;
- shifts are logical and return zero when the shift amount is at least `w`;
- all `2 ^ w` memory cells are available;
- allocation and input encoding specify the initial state.

`timeAndSpaceCost` interprets each query jointly in
`AddWriterT (RAMCost w k) (StateM (RAMState w k))`.
Time adds and probe sets union across queries. `runM` retains the result, cost, and final state;
`evalM` and `costM` project evaluation and resource usage from this semantics.

`RAMCost.space`, `auxiliarySpace`, and `totalSpace` include the fixed `k` register words.
The memory component counts distinct accessed cells. Auxiliary space excludes input memory;
total space includes input memory even if some cells were never read.

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
abbrev Word (w : ℕ) := BitVec w

/-- A register identifier, not a word value. There are exactly `k` available registers. -/
abbrev Register (k : ℕ) := Fin k

/-- The contents of the word-addressed memory. -/
abbrev Memory (w : ℕ) := Word w → Word w

/-- Machine words live in memory or one of the fixed `k` register slots. -/
structure RAMState (w k : ℕ) where
  /-- The word stored at each memory address. -/
  Memory : Word w → Word w
  /-- The words held in the fixed register file. -/
  Registers : Register k → Word w

/-- Zero-initialized memory and registers. -/
def RAMState.zero : RAMState w k := ⟨fun _ => 0, fun _ => 0⟩

/-- Update a register; values are computed from the old state before this update. -/
def RAMState.writeRegister (s : RAMState w k) (r : Register k) (value : Word w) : RAMState w k :=
  { s with Registers := Function.update s.Registers r value }

@[simp, grind =] theorem RAMState.writeRegister_memory (s : RAMState w k)
    (r : Register k) (value : Word w) : (s.writeRegister r value).Memory = s.Memory := rfl

@[simp, grind =] theorem RAMState.writeRegister_registers (s : RAMState w k)
    (r : Register k) (value : Word w) (r' : Register k) :
    (s.writeRegister r value).Registers r' = if r' = r then value else s.Registers r' := by
  simp [RAMState.writeRegister, Function.update_apply]

/-- A second write to the same register replaces the first. -/
@[simp, grind =] theorem RAMState.writeRegister_overwrite (s : RAMState w k)
    (r : Register k) (a b : Word w) :
    (s.writeRegister r a).writeRegister r b = s.writeRegister r b := by
  cases s
  simp [RAMState.writeRegister, Function.update_idem]

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

/-- Register-based word-RAM queries. Data operations return `Unit`; only comparisons
return a Boolean for branching. A word can enter a register through a literal or the initial state,
but no query exposes a word to its continuation. -/
inductive WordRAM (w k : Nat) : Type → Type where
  | set (dst : WordRAM.Register k) (value : WordRAM.Word w) : WordRAM w k Unit
  | copy (dst src : WordRAM.Register k) : WordRAM w k Unit
  | load (dst addr : WordRAM.Register k) : WordRAM w k Unit
  | store (addr src : WordRAM.Register k) : WordRAM w k Unit
  | binop (op : WordRAM.BinOp) (dst x y : WordRAM.Register k) : WordRAM w k Unit
  | bnot (dst src : WordRAM.Register k) : WordRAM w k Unit
  | cmp (op : WordRAM.CmpOp) (x y : WordRAM.Register k) : WordRAM w k Bool

namespace WordRAM

/-- Queries expose only unit results and comparison flags. -/
theorem result_type (q : WordRAM w k α) : α = Unit ∨ α = Bool := by
  cases q <;> simp

/-- Execute an instruction. All source registers are read before any destination is written. -/
def evalQuery : WordRAM w k α → StateM (RAMState w k) α
  | .set dst value, s => ((), s.writeRegister dst value)
  | .copy dst src, s => ((), s.writeRegister dst (s.Registers src))
  | .load dst addr, s => ((), s.writeRegister dst (s.Memory (s.Registers addr)))
  | .store addr src, s =>
      ((), { s with Memory := Function.update s.Memory (s.Registers addr) (s.Registers src) })
  | .binop op dst x y, s =>
      ((), s.writeRegister dst (op.eval (s.Registers x) (s.Registers y)))
  | .bnot dst src, s => ((), s.writeRegister dst (~~~s.Registers src))
  | .cmp op x y, s => (op.eval (s.Registers x) (s.Registers y), s)

/-- Time and the set of memory addresses accessed by an execution. -/
@[ext]
structure RAMCost (w k : Nat) where
  /-- Number of primitive queries executed. -/
  time : Nat
  /-- Distinct addresses loaded from or stored to. -/
  addresses : Finset (Word w)
  deriving DecidableEq

namespace RAMCost

@[simps]
instance : Zero (RAMCost w k) := ⟨0, ∅⟩

@[simps]
instance : Add (RAMCost w k) where
  add a b := ⟨a.time + b.time, a.addresses ∪ b.addresses⟩

attribute [grind =] zero_time zero_addresses add_time add_addresses

instance : AddCommMonoid (RAMCost w k) where
  nsmul := nsmulRec
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_assoc a b c := by ext <;> simp [Nat.add_assoc, Finset.union_assoc]
  add_comm a b := by ext <;> simp [Nat.add_comm, Finset.union_comm]

/-- Normalize addition to the time sum and the union of accessed addresses. -/
@[simp, grind =] theorem mk_add (time : Nat) (addresses : Finset (Word w)) (c : RAMCost w k) :
    (⟨time, addresses⟩ : RAMCost w k) + c = ⟨time + c.time, addresses ∪ c.addresses⟩ := rfl

/-- Register storage plus memory footprint, in words. -/
def space (c : RAMCost w k) : Nat := k + c.addresses.card

/-- Register storage plus accessed memory outside the designated input region. -/
def auxiliarySpace (c : RAMCost w k) (inputRegion : Finset (Word w)) : Nat :=
  k + (c.addresses \ inputRegion).card

/-- Registers and all words in the footprint or input region, including unread input cells. -/
def totalSpace (c : RAMCost w k) (inputRegion : Finset (Word w)) : Nat :=
  k + (c.addresses ∪ inputRegion).card

end RAMCost

/-- Memory probes performed by an instruction, resolved before it executes. -/
def queryProbes : WordRAM w k α → RAMState w k → Finset (Word w)
  | .load _ addr, s => {s.Registers addr}
  | .store addr _, s => {s.Registers addr}
  | _, _ => ∅

/-- Each instruction returns its result and actual resource cost in the same state transition.
Addresses are resolved from the incoming registers, before executing the instruction. -/
@[simps]
def timeAndSpaceCost : ModelM (WordRAM w k) (StateM (RAMState w k)) (RAMCost w k) where
  runQuery q := AddWriterT.mk fun s =>
    let result := evalQuery q s
    ((⟨result.fst, ⟨1, queryProbes q s⟩⟩ : AddWriter (RAMCost w k) _), result.snd)

/-- Forgetting the resource cost recovers the physical instruction semantics. -/
@[simp, grind =] theorem timeAndSpaceCost_evalQuery (q : WordRAM w k α) :
    timeAndSpaceCost.evalQuery q = evalQuery q := by
  funext s
  rfl

end WordRAM

end Algolean.Algorithms
