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
register and return `Unit`. Comparisons write flags indexed by `CmpOp`; structured branches
check those flags inside the model and return `Unit`. Branch bodies use ordinary `Prog` syntax;
`instructions` converts them to finite blocks before execution. The unselected body has no effects
or resource cost. `runM_ret_independent` proves that Lean return values cannot depend on
machine data.
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
total space includes input memory even if some cells were never read. Two fixed Boolean flags
are additional control storage. Program size and host-language construction costs are excluded.

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

/-- Word comparisons; ordering is unsigned. -/
inductive CmpOp where
  | eq | ult
  deriving DecidableEq, Repr

/-- Machine words live in memory or one of the fixed `k` register slots. -/
structure RAMState (w k : ℕ) where
  /-- The word stored at each memory address. -/
  Memory : Word w → Word w
  /-- The words held in the fixed register file. -/
  Registers : Register k → Word w
  /-- One comparison flag per operation, separate from word registers. -/
  Flags : CmpOp → Bool := fun _ => false

/-- Zero-initialized memory and registers, with cleared comparison flags. -/
def RAMState.zero : RAMState w k := ⟨fun _ => 0, fun _ => 0, fun _ => false⟩

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

/-- Register-based instructions with machine-local comparison flags and structured branches.
All instructions return `Unit`, including comparisons and branches. -/
inductive WordRAM (w k : Nat) : Type → Type where
  | set (dst : WordRAM.Register k) (value : WordRAM.Word w) : WordRAM w k Unit
  | copy (dst src : WordRAM.Register k) : WordRAM w k Unit
  | load (dst addr : WordRAM.Register k) : WordRAM w k Unit
  | store (addr src : WordRAM.Register k) : WordRAM w k Unit
  | binop (op : WordRAM.BinOp) (dst x y : WordRAM.Register k) : WordRAM w k Unit
  | bnot (dst src : WordRAM.Register k) : WordRAM w k Unit
  | cmp (op : WordRAM.CmpOp) (x y : WordRAM.Register k) : WordRAM w k Unit
  | clearFlag (op : WordRAM.CmpOp) : WordRAM w k Unit
  | branchCode (op : WordRAM.CmpOp) (yes no : List (WordRAM w k Unit)) : WordRAM w k Unit

namespace WordRAM

/-- Every instruction returns `Unit`; machine data never enters a continuation. -/
theorem result_type (q : WordRAM w k α) : α = Unit := by
  cases q <;> rfl

/-- Change one flag without altering memory, word registers, or other flags. -/
def RAMState.writeFlag (s : RAMState w k) (op : CmpOp) (flag : Bool) : RAMState w k :=
  { s with Flags := Function.update s.Flags op flag }

@[simp, grind =] theorem RAMState.writeFlag_memory (s : RAMState w k) (op : CmpOp) (b : Bool) :
    (s.writeFlag op b).Memory = s.Memory := rfl

@[simp, grind =] theorem RAMState.writeFlag_registers (s : RAMState w k) (op : CmpOp) (b : Bool) :
    (s.writeFlag op b).Registers = s.Registers := rfl

@[simp, grind =] theorem RAMState.writeFlag_flags (s : RAMState w k)
    (op : CmpOp) (b : Bool) (op' : CmpOp) :
    (s.writeFlag op b).Flags op' = if op' = op then b else s.Flags op' := by
  simp [RAMState.writeFlag, Function.update_apply]

@[simp, grind =] theorem RAMState.writeFlag_overwrite (s : RAMState w k)
    (op : CmpOp) (a b : Bool) :
    (s.writeFlag op a).writeFlag op b = s.writeFlag op b := by
  cases s
  simp [RAMState.writeFlag, Function.update_idem]

@[simp, grind =] theorem RAMState.writeRegister_flags (s : RAMState w k)
    (r : Register k) (v : Word w) : (s.writeRegister r v).Flags = s.Flags := rfl

/-- Compile a `Unit` program to a finite block without consulting machine state. -/
def instructions : Prog (WordRAM w k) Unit → List (WordRAM w k Unit)
  | .pure _ => []
  | .liftBind q cont =>
    (result_type q ▸ q) :: instructions (cont ((result_type q).symm ▸ ()))

@[simp] theorem instructions_pure :
    instructions (pure () : Prog (WordRAM w k) Unit) = [] := rfl

@[simp] theorem instructions_lift_bind (q : WordRAM w k Unit)
    (cont : Unit → Prog (WordRAM w k) Unit) :
    instructions (Cslib.FreeM.lift q >>= cont) = q :: instructions (cont ()) := rfl

/-- Branch on the flag indexed by `op`, without exposing it as a Lean Boolean. -/
def branch (op : CmpOp) (yes no : Prog (WordRAM w k) Unit) : Prog (WordRAM w k) Unit :=
  .liftBind (.branchCode op (instructions yes) (instructions no)) pure

/-- Time and the set of memory addresses accessed by an execution. -/
@[ext]
structure RAMCost (w k : Nat) where
  /-- Number of primitive word and flag operations executed; branch selection is free. -/
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

mutual

/-- Joint instruction semantics. Only the selected branch executes; branching itself is free. -/
def runQuery : WordRAM w k α → AddWriterT (RAMCost w k) (StateM (RAMState w k)) α
  | .set dst value => AddWriterT.mk fun s =>
    (⟨(), ⟨1, ∅⟩⟩, s.writeRegister dst value)
  | .copy dst src => AddWriterT.mk fun s =>
    (⟨(), ⟨1, ∅⟩⟩, s.writeRegister dst (s.Registers src))
  | .load dst addr => AddWriterT.mk fun s =>
    (⟨(), ⟨1, {s.Registers addr}⟩⟩, s.writeRegister dst (s.Memory (s.Registers addr)))
  | .store addr src => AddWriterT.mk fun s =>
    (⟨(), ⟨1, {s.Registers addr}⟩⟩,
      { s with Memory := Function.update s.Memory (s.Registers addr) (s.Registers src) })
  | .binop op dst x y => AddWriterT.mk fun s =>
    (⟨(), ⟨1, ∅⟩⟩, s.writeRegister dst (op.eval (s.Registers x) (s.Registers y)))
  | .bnot dst src => AddWriterT.mk fun s =>
    (⟨(), ⟨1, ∅⟩⟩, s.writeRegister dst (~~~s.Registers src))
  | .cmp op x y => AddWriterT.mk fun s =>
    (⟨(), ⟨1, ∅⟩⟩, s.writeFlag op (op.eval (s.Registers x) (s.Registers y)))
  | .clearFlag op => AddWriterT.mk fun s => (⟨(), ⟨1, ∅⟩⟩, s.writeFlag op false)
  | .branchCode op yes no => AddWriterT.mk fun s =>
    if s.Flags op then (runBlock yes).run s else (runBlock no).run s

/-- Execute a finite block using the same query semantics. -/
def runBlock : List (WordRAM w k Unit) → AddWriterT (RAMCost w k) (StateM (RAMState w k)) Unit
  | [] => pure ()
  | q :: qs => runQuery q >>= fun _ => runBlock qs

end

/-- The existing model machinery supplies joint execution, evaluation, costs, and WP. -/
def timeAndSpaceCost : ModelM (WordRAM w k) (StateM (RAMState w k)) (RAMCost w k) where
  runQuery := runQuery

@[simp, grind =] theorem timeAndSpaceCost_runQuery (q : WordRAM w k α) :
    timeAndSpaceCost.runQuery q = runQuery q := rfl

/-- Physical evaluation is a projection of the joint interpreter. -/
def evalQuery (q : WordRAM w k α) : StateM (RAMState w k) α :=
  timeAndSpaceCost.evalQuery q

/-- Actual memory probes, including only the selected branch. -/
def queryProbes (q : WordRAM w k α) (s : RAMState w k) : Finset (Word w) :=
  ((runQuery q).run s).fst.tell.addresses

@[simp, grind =] theorem timeAndSpaceCost_evalQuery (q : WordRAM w k α) :
    timeAndSpaceCost.evalQuery q = evalQuery q := rfl

@[simp] theorem runBlock_nil :
    runBlock ([] : List (WordRAM w k Unit)) = pure () := by rw [runBlock]

@[simp] theorem runBlock_cons (q : WordRAM w k Unit) (qs : List (WordRAM w k Unit)) :
    runBlock (q :: qs) = runQuery q >>= fun _ => runBlock qs := by rw [runBlock]

/-- Compiling a branch body preserves its joint execution. -/
@[simp] theorem runBlock_instructions (p : Prog (WordRAM w k) Unit) :
    runBlock (instructions p) = p.runM timeAndSpaceCost := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih =>
    cases q <;> simp [instructions, Prog.runM, Cslib.FreeM.liftM, ih]

/-- Branch on the incoming flag; charge only the executed body. -/
@[simp] theorem runM_branch (op : CmpOp) (yes no : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    ((branch op yes no).runM timeAndSpaceCost).run s =
      if s.Flags op then (yes.runM timeAndSpaceCost).run s
      else (no.runM timeAndSpaceCost).run s := by
  simp [branch, runQuery]

/-- Program syntax determines the Lean return value independently of machine data. -/
def returnValue : Prog (WordRAM w k) α → α
  | .pure a => a
  | .liftBind q cont => returnValue (cont ((result_type q).symm ▸ ()))

/-- Input-dependent results must remain in machine state. -/
@[simp] theorem runM_ret (p : Prog (WordRAM w k) α) (s : RAMState w k) :
    let result := (p.runM timeAndSpaceCost).run s
    result.fst.ret = returnValue p := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind q cont ih => cases q <;> simp [returnValue, ih]

/-- No program can recover a machine flag into a Lean return value. -/
theorem runM_ret_independent (p : Prog (WordRAM w k) α) (s t : RAMState w k) :
    let left := (p.runM timeAndSpaceCost).run s
    let right := (p.runM timeAndSpaceCost).run t
    left.fst.ret = right.fst.ret := by simp only [runM_ret]

end WordRAM

end Algolean.Algorithms
