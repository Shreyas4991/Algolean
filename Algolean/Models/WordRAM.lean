/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.FuelExecMonad
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

`execute fuel program state` uses the shared `FuelExecMonad` interpreter. Each instruction,
branch selection, and loop test consumes one unit of fuel. Exhaustion returns `none`, discarding
the result, final state, and costs. Primitive instructions cost one time unit; branch selection
and flag tests cost zero time. Fuel is separate from these machine costs.

## References

* Pat Morin, *Open Data Structures*, §1.4:
  https://opendatastructures.org/ods-java/1_4_Model_Computation.html
* Harvard CS125, Lecture 6, §§6.6–6.7 (word-RAM instructions and modular arithmetic):
  https://people.seas.harvard.edu/~cs125/fall16/lec6.pdf
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib

namespace Prog

/-- A model-controlled condition selects a body without returning its decision to Lean. -/
abbrev Condition (Q : Type u → Type v) := Prog Q Unit → Prog Q Unit → Prog Q Unit

/-- Execute the body selected by a model-controlled condition. -/
def ifThenElse (condition : Condition Q) (yes no : Prog Q Unit) : Prog Q Unit :=
  condition yes no

/-- Execute a body only when the model-controlled condition holds. -/
def when (condition : Condition Q) (body : Prog Q Unit) : Prog Q Unit :=
  ifThenElse condition body (pure ())

/-- Execute a body only when the model-controlled condition does not hold. -/
def unlessDo (condition : Condition Q) (body : Prog Q Unit) : Prog Q Unit :=
  ifThenElse condition (pure ()) body

/-- Negate a condition without exposing its decision. -/
def Condition.not (condition : Condition Q) : Condition Q := fun yes no => condition no yes

@[simp, grind =] theorem ifThenElse_not (condition : Condition Q) (yes no : Prog Q Unit) :
    ifThenElse condition.not yes no = ifThenElse condition no yes := rfl

@[simp] theorem Condition.not_not (condition : Condition Q) : condition.not.not = condition := rfl

/-- Test before each body, stopping after at most the supplied number of iterations.
Zero iterations perform no test. The bound is fixed when constructing the program. -/
def repeatLoop (condition : Condition Q) (body : Prog Q Unit) : Nat → Prog Q Unit
  | 0 => pure ()
  | fuel + 1 => ifThenElse condition (do body; repeatLoop condition body fuel) (pure ())

@[simp, grind =] theorem repeatLoop_zero (condition : Condition Q) (body : Prog Q Unit) :
    repeatLoop condition body 0 = pure () := rfl

@[simp, grind =] theorem repeatLoop_succ (condition : Condition Q) (body : Prog Q Unit) (n : Nat) :
    repeatLoop condition body (n + 1) =
      ifThenElse condition (do body; repeatLoop condition body n) (pure ()) := rfl

end Prog

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

@[simp, grind =] theorem RAMState.writeRegister_memory (s : RAMState w k)
    (r : Register k) (value : Word w) : (s.writeRegister r value).Memory = s.Memory := rfl

@[simp, grind =] theorem RAMState.writeRegister_registers (s : RAMState w k)
    (r : Register k) (value : Word w) (r' : Register k) :
    (s.writeRegister r value).Registers r' = if r' = r then value else s.Registers r' := by
  simp [RAMState.writeRegister, Function.update_apply]

@[simp, grind =] theorem RAMState.writeRegister_flags (s : RAMState w k)
    (r : Register k) (value : Word w) : (s.writeRegister r value).Flags = s.Flags := rfl

@[simp, grind =] theorem RAMState.writeRegister_overwrite (s : RAMState w k)
    (r : Register k) (a b : Word w) :
    (s.writeRegister r a).writeRegister r b = s.writeRegister r b := by
  cases s
  simp [RAMState.writeRegister, Function.update_idem]

@[simp, grind =] theorem RAMState.writeRegister_self (s : RAMState w k) (r : Register k) :
    s.writeRegister r (s.Registers r) = s := by
  simp [RAMState.writeRegister, Function.update_eq_self]

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

namespace Internal

/-- Store a fixed program as the body of a structured control instruction. -/
def instructions : Prog (WordRAM w k) Unit → List (WordRAM w k Unit)
  | .pure _ => []
  | .liftBind q next =>
    (result_type q ▸ q) :: instructions (next ((result_type q).symm ▸ ()))

private theorem forM_instructions (p : Prog (WordRAM w k) Unit) :
    (instructions p).forM (fun q => FreeM.lift q) = p := by
  induction p with
  | pure a => cases a; rfl
  | liftBind q next ih =>
    cases q <;> simp_all only [instructions, List.forM_eq_forM, List.forM_cons]
    all_goals rw [FreeM.liftBind_eq]; congr 1

end Internal

open Internal

/-- Branch on a machine flag without exposing it as a Lean Boolean. -/
def branch (op : CmpOp) (yes no : Prog (WordRAM w k) Unit) : Prog (WordRAM w k) Unit :=
  FreeM.lift (.branchCode op (instructions yes) (instructions no))

/-- Test an existing flag without performing another comparison. -/
def flag (op : CmpOp) : Prog.Condition (WordRAM w k) := branch op

/-- Compare two registers anew whenever this condition is tested. -/
def test (op : CmpOp) (x y : Register k) : Prog.Condition (WordRAM w k) := fun yes no => do
  cmp (w := w) op x y
  branch op yes no

@[simp, grind =] theorem ifThenElse_flag (op : CmpOp) (yes no : Prog (WordRAM w k) Unit) :
    Prog.ifThenElse (flag op) yes no = branch op yes no := rfl

@[simp, grind =] theorem ifThenElse_test (op : CmpOp) (x y : Register k)
    (yes no : Prog (WordRAM w k) Unit) :
    Prog.ifThenElse (test op x y) yes no = (do cmp (w := w) op x y; branch op yes no) := rfl

/-- Repeat while the designated machine flag is true. The body must update the flag to stop. -/
def whileLoop (op : CmpOp) (body : Prog (WordRAM w k) Unit) : Prog (WordRAM w k) Unit :=
  FreeM.lift (.whileCode op (instructions body))

/-- Recompute a charged comparison before every iteration and on exit. -/
def whileCompare (op : CmpOp) (x y : Register k) (body : Prog (WordRAM w k) Unit) :
    Prog (WordRAM w k) Unit := do
  cmp (w := w) op x y
  whileLoop op (do body; cmp (w := w) op x y)

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

/-- Physical RAM state paired with the shared interpreter's remaining fuel. -/
abbrev ExecutionState (w k : Nat) := FuelExecState (RAMState w k)

/-- Fuel exhaustion fails the whole execution, including its accumulated cost. -/
abbrev ExecutionM (w k : Nat) := FuelExecMonad (RAMState w k)

/-- Execute one instruction; structured control schedules its body before the continuation.
All source registers and memory addresses are read from the incoming state. -/
def step (q : WordRAM w k α) (next : α → Prog (WordRAM w k) β) (s : RAMState w k) :
    FuelExecMonad.Step (WordRAM w k) (RAMState w k) (RAMCost w) β :=
  match q with
  | .nop => ⟨⟨1, ∅⟩, s, next ()⟩
  | .set dst value => ⟨⟨1, ∅⟩, s.writeRegister dst value, next ()⟩
  | .copy dst src => ⟨⟨1, ∅⟩, s.writeRegister dst (s.Registers src), next ()⟩
  | .load dst addr =>
    ⟨⟨1, {s.Registers addr}⟩, s.writeRegister dst (s.Memory (s.Registers addr)), next ()⟩
  | .store addr src =>
    ⟨⟨1, {s.Registers addr}⟩,
      {s with Memory := Function.update s.Memory (s.Registers addr) (s.Registers src)}, next ()⟩
  | .binop op dst x y =>
    ⟨⟨1, ∅⟩, s.writeRegister dst (op.eval (s.Registers x) (s.Registers y)), next ()⟩
  | .bnot dst src => ⟨⟨1, ∅⟩, s.writeRegister dst (~~~s.Registers src), next ()⟩
  | .cmp op x y => ⟨⟨1, ∅⟩, s.writeFlag op (op.eval (s.Registers x) (s.Registers y)), next ()⟩
  | .clearFlag op => ⟨⟨1, ∅⟩, s.writeFlag op false, next ()⟩
  | .branchCode op yes no =>
    ⟨0, s, (if s.Flags op then yes else no).forM (fun q => FreeM.lift q) >>= next⟩
  | .whileCode op body =>
    ⟨0, s, if s.Flags op then do
      body.forM (fun q => FreeM.lift q)
      FreeM.lift (.whileCode op body) >>= next
    else next ()⟩

/-- WordRAM's small-step semantics, using the common fuelled runner. -/
abbrev interpreter (w k : Nat) :
    FuelExecMonad.Interpreter (WordRAM w k) (RAMState w k) (RAMCost w) where
  step := step
  step_bind := by
    intro α β γ q next cont s
    cases q <;> simp [step, bind_assoc]
    split <;> simp

/-- Joint machine-state and resource semantics; memory footprints depend on incoming registers. -/
abbrev timeAndSpaceCost : ModelStateM (WordRAM w k) (ExecutionM w k) (RAMCost w) :=
  (interpreter w k).toModel

/-- Run a fixed program on a separately supplied input state with an external fuel budget. -/
abbrev execute (fuel : Nat) (p : Prog (WordRAM w k) α) (s : RAMState w k) :
    Option (AddWriter (RAMCost w) α × ExecutionState w k) :=
  FuelExecMonad.execute timeAndSpaceCost fuel p s

/-- A no-op preserves state and costs one time unit and one unit of interpreter fuel. -/
@[simp, grind =] theorem execute_nop_succ (fuel : Nat) (s : RAMState w k) :
    execute (fuel + 1) (FreeM.lift (.nop : WordRAM w k Unit)) s =
      some (⟨(), ⟨1, ∅⟩⟩, ⟨s, fuel⟩) := by simp [step]

@[simp, grind =] theorem execute_set_succ (fuel : Nat) (s : RAMState w k)
    (dst : Register k) (value : Word w) :
    execute (fuel + 1) (FreeM.lift (.set dst value)) s =
      some (⟨(), ⟨1, ∅⟩⟩, ⟨s.writeRegister dst value, fuel⟩) := by simp [step]

@[simp, grind =] theorem execute_copy_succ (fuel : Nat) (s : RAMState w k)
    (dst src : Register k) :
    execute (fuel + 1) (FreeM.lift (.copy dst src)) s =
      some (⟨(), ⟨1, ∅⟩⟩, ⟨s.writeRegister dst (s.Registers src), fuel⟩) := by simp [step]

/-- Loading an address register into itself records its incoming value in the footprint. -/
@[simp, grind =] theorem execute_load_succ (fuel : Nat) (s : RAMState w k)
    (dst addr : Register k) :
    execute (fuel + 1) (FreeM.lift (.load dst addr)) s =
      some (⟨(), ⟨1, {s.Registers addr}⟩⟩,
        ⟨s.writeRegister dst (s.Memory (s.Registers addr)), fuel⟩) := by simp [step]

@[simp, grind =] theorem execute_store_succ (fuel : Nat) (s : RAMState w k)
    (addr src : Register k) :
    execute (fuel + 1) (FreeM.lift (.store addr src)) s =
      some (⟨(), ⟨1, {s.Registers addr}⟩⟩,
        ⟨{s with Memory := Function.update s.Memory (s.Registers addr) (s.Registers src)}, fuel⟩) := by
  simp [step]

@[simp, grind =] theorem execute_binop_succ (fuel : Nat) (s : RAMState w k)
    (op : BinOp) (dst x y : Register k) :
    execute (fuel + 1) (FreeM.lift (.binop op dst x y)) s =
      some (⟨(), ⟨1, ∅⟩⟩,
        ⟨s.writeRegister dst (op.eval (s.Registers x) (s.Registers y)), fuel⟩) := by
  simp [step]

@[simp, grind =] theorem execute_bnot_succ (fuel : Nat) (s : RAMState w k)
    (dst src : Register k) :
    execute (fuel + 1) (FreeM.lift (.bnot dst src)) s =
      some (⟨(), ⟨1, ∅⟩⟩, ⟨s.writeRegister dst (~~~s.Registers src), fuel⟩) := by simp [step]

@[simp, grind =] theorem execute_cmp_succ (fuel : Nat) (s : RAMState w k)
    (op : CmpOp) (x y : Register k) :
    execute (fuel + 1) (FreeM.lift (.cmp op x y)) s =
      some (⟨(), ⟨1, ∅⟩⟩,
        ⟨s.writeFlag op (op.eval (s.Registers x) (s.Registers y)), fuel⟩) := by simp [step]

@[simp, grind =] theorem execute_clearFlag_succ (fuel : Nat) (s : RAMState w k) (op : CmpOp) :
    execute (fuel + 1) (FreeM.lift (.clearFlag op)) s =
      some (⟨(), ⟨1, ∅⟩⟩, ⟨s.writeFlag op false, fuel⟩) := by simp [step]

/-- Branch selection consumes one unit of fuel and executes only the selected body. -/
@[simp, grind =] theorem execute_branch_succ (fuel : Nat) (op : CmpOp)
    (yes no : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    execute (fuel + 1) (branch op yes no) s =
      if s.Flags op then execute fuel yes s else execute fuel no s := by
  change FuelExecMonad.execute (interpreter w k).toModel (fuel + 1)
    (.liftBind (.branchCode op (instructions yes) (instructions no)) pure) s = _
  rw [FuelExecMonad.execute_liftBind_succ]
  simp only [step]
  split
  all_goals
    simp only [forM_instructions, bind_pure, zero_add]
    change (execute fuel _ s).bind some = _
    simp

@[simp, grind =] theorem execute_while_zero (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) : execute 0 (whileLoop op body) s = none := by
  simp only [whileLoop, FreeM.lift, FuelExecMonad.execute_zero_liftBind]

/-- Each flag test consumes fuel but no RAM resources, even for an empty loop body. -/
@[grind =] theorem execute_while_succ (fuel : Nat) (op : CmpOp)
    (body : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    execute (fuel + 1) (whileLoop op body) s =
      if s.Flags op then execute fuel (do body; whileLoop op body) s
      else some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  change FuelExecMonad.execute (interpreter w k).toModel (fuel + 1)
    (.liftBind (.whileCode op (instructions body)) pure) s = _
  rw [FuelExecMonad.execute_liftBind_succ]
  simp only [step, forM_instructions]
  split
  · simp only [bind_pure, zero_add]
    change (execute fuel (do body; whileLoop op body) s).bind some = _
    simp
  · simp

@[simp] theorem execute_while_false (fuel : Nat) (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) (h : s.Flags op = false) :
    execute (fuel + 1) (whileLoop op body) s = some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  simp [execute_while_succ, h]

@[simp] theorem execute_while_true (fuel : Nat) (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) (h : s.Flags op = true) :
    execute (fuel + 1) (whileLoop op body) s = execute fuel (do body; whileLoop op body) s := by
  simp [execute_while_succ, h]

/-- Completed execution with an exact cost and physical final state, hiding interpreter fuel. -/
def Completes (program : Prog (WordRAM w k) Unit) (s : RAMState w k)
    (cost : RAMCost w) (final : RAMState w k) : Prop :=
  ∃ fuel, execute fuel program s = some (⟨(), cost⟩, ⟨final, 0⟩)

@[simp] theorem completes_pure (s : RAMState w k) : Completes (pure ()) s 0 s := ⟨0, rfl⟩

/-- Any successful run supplies a completion witness by trimming its unused fuel. -/
theorem completes_of_execute {p : Prog (WordRAM w k) Unit} {fuel : Nat} {s : RAMState w k}
    {result : AddWriter (RAMCost w) Unit} {final : ExecutionState w k}
    (h : execute fuel p s = some (result, final)) : Completes p s result.tell final.machine := by
  have ht := (FuelExecMonad.execute_trim_fuel fuel p s result final h).2
  exact ⟨fuel - final.fuel, by simpa [AddWriter.ext_iff] using ht⟩

/-- Completed runs agree on their exact costs and physical final states, independently of fuel. -/
theorem Completes.unique {p : Prog (WordRAM w k) Unit} {s t u : RAMState w k} {a b : RAMCost w}
    (hp : Completes p s a t) (hq : Completes p s b u) : a = b ∧ t = u := by
  obtain ⟨fuel, hp⟩ := hp
  obtain ⟨extra, hq⟩ := hq
  have h₁ := FuelExecMonad.execute_add_fuel fuel extra p s _ _ hp
  have h₂ := FuelExecMonad.execute_add_fuel extra fuel p s _ _ hq
  grind [Nat.add_comm]

/-- Composing completed procedures threads their physical state and adds their exact costs. -/
theorem Completes.seq {p q : Prog (WordRAM w k) Unit} {s t u : RAMState w k} {a b : RAMCost w}
    (hp : Completes p s a t) (hq : Completes q t b u) : Completes (do p; q) s (a + b) u := by
  obtain ⟨fuel, hp⟩ := hp
  obtain ⟨extra, hq⟩ := hq
  exact ⟨fuel + extra, by simp [FuelExecMonad.execute_add_fuel fuel extra p s _ _ hp, hq]⟩

/-- Only the selected branch must complete; choosing it adds no RAM cost. -/
theorem Completes.branch {op : CmpOp} {yes no : Prog (WordRAM w k) Unit}
    {s t : RAMState w k} {cost : RAMCost w}
    (h : Completes (if s.Flags op then yes else no) s cost t) :
    Completes (branch op yes no) s cost t := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  split at h <;> simp_all

/-- A false loop flag exits with no physical state change or RAM cost. -/
theorem completes_while_false (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) (h : s.Flags op = false) : Completes (whileLoop op body) s 0 s :=
  ⟨1, by simp [h]⟩

/-- Compose one completed body with the remaining iterations; the test itself is free. -/
theorem Completes.while_step {op : CmpOp} {body : Prog (WordRAM w k) Unit}
    {s t u : RAMState w k} {a b : RAMCost w} (h : s.Flags op = true)
    (hb : Completes body s a t) (hr : Completes (whileLoop op body) t b u) :
    Completes (whileLoop op body) s (a + b) u := by
  obtain ⟨fuel, hfuel⟩ := hb.seq hr
  exact ⟨fuel + 1, by simpa [h] using hfuel⟩

/-- A body that clears the loop flag is its final iteration. -/
theorem Completes.while_stop {op : CmpOp} {body : Prog (WordRAM w k) Unit}
    {s t : RAMState w k} {cost : RAMCost w} (hb : Completes body s cost t)
    (hs : s.Flags op = true) (ht : t.Flags op = false) :
    Completes (whileLoop op body) s cost t := by
  simpa only [add_zero] using Completes.while_step hs hb (completes_while_false op body t ht)

/-- Host-language return values are fixed by syntax; all machine queries return `Unit`. -/
def returnValue : Prog (WordRAM w k) α → α
  | .pure a => a
  | .liftBind q next => returnValue (next ((result_type q).symm ▸ ()))

@[simp] theorem returnValue_unit (p : Prog (WordRAM w k) Unit) : returnValue p = () :=
  Subsingleton.elim _ _

/-- Replacing the final Lean result by its syntactically fixed value preserves the program. -/
theorem eq_bind_return (p : Prog (WordRAM w k) α) :
    p = (p >>= fun _ => pure (returnValue p)) := by
  induction p with
  | pure a => rfl
  | liftBind q next ih =>
    cases q <;> simp only [← FreeM.bind_eq_bind, FreeM.bind, returnValue]
    all_goals congr 1; funext u; cases u; simpa only [FreeM.bind_eq_bind] using ih ()

/-- Completed execution cannot reveal memory, register, or flag contents through its Lean result. -/
@[grind →] theorem execute_ret (p : Prog (WordRAM w k) α) (s : RAMState w k) (fuel : Nat)
    (result : AddWriter (RAMCost w) α) (final : ExecutionState w k)
    (h : execute fuel p s = some (result, final)) : result.ret = returnValue p := by
  have hr := h
  rw [eq_bind_return p] at hr
  simp only [FuelExecMonad.execute_bind, h, FuelExecMonad.execute_pure, Option.pure_def] at hr
  grind

/-- Successful runs of a fixed program return the same Lean value on all initial machine states. -/
theorem execute_ret_independent (p : Prog (WordRAM w k) α) (s t : RAMState w k)
    {fuel fuel' : Nat} {result result' : AddWriter (RAMCost w) α}
    {final final' : ExecutionState w k}
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret := by
  grind

end WordRAM

end Algolean.Algorithms
