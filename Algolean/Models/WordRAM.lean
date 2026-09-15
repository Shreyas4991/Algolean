/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.ModelStateM
public import Mathlib.Data.Finset.Card

/-!
# Word-RAM queries

`WordRAM w k` operates on `w`-bit words held in memory and exactly `k` registers.
Registers are identifiers (`Fin k`), and data instructions write their result into a destination
register and return `Unit`. Comparisons write flags indexed by `CmpOp`; structured branches
check those flags inside the model and return `Unit`. Branch bodies use ordinary `Prog` syntax;
`instructions` converts them to finite blocks before execution. The unselected body has no effects
or resource cost. `runStateM_ret_independent` proves that Lean return values cannot depend on
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
Time adds and probe sets union across queries.
`runStateM` retains the result, cost, and final state;
`evalStateM` and `costStateM` project evaluation and resource usage from this semantics.

`RAMCost.space`, `auxiliarySpace`, and `totalSpace` count memory words only.
The fixed register file and comparison flags are excluded from space accounting.
Space counts distinct accessed cells. Auxiliary space excludes input memory; total space
includes input memory even if some cells were never read. Program size and host-language
construction costs are excluded.

## Fuelled execution

`execute fuel program state` runs through `fuelledModel`, an instance of `ModelStateM`.
Each executed instruction consumes one unit of interpreter fuel, including branch selection.
Branch bodies and continuations share the remaining budget; unselected bodies consume none.
Fuel is not RAM time. Exhaustion returns `none`; success returns the result, `RAMCost`, final
RAM state, and remaining fuel. Pure programs require no fuel. Additional fuel preserves any
successful execution, changing only the unused budget.

## Control-flow sugar

`open scoped Prog` enables `ifₚ condition then ... else ...` and `repeat [fuel]`
with an indented body. Repetition executes the body exactly `fuel` times.
Use `flag op` to inspect an existing flag, or `test op x y` to compare registers afresh.
Both bodies return `Unit`. These definitions expand into the existing programs and do not
change instruction costs.

## References

* Pat Morin, *Open Data Structures*, §1.4:
  https://opendatastructures.org/ods-java/1_4_Model_Computation.html
* Harvard CS125, Lecture 6, §§6.6–6.7 (word-RAM instructions and modular arithmetic):
  https://people.seas.harvard.edu/~cs125/fall16/lec6.pdf
-/

@[expose] public section

namespace Algolean.Algorithms

namespace Prog

section ControlFlowDefinitions

/-- A model-controlled condition. Choosing a branch never returns its decision to Lean.
The condition may execute queries before selecting a `Unit` body. -/
abbrev Condition (Q : Type u → Type v) :=
  Prog Q Unit → Prog Q Unit → Prog Q Unit

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
def Condition.not (condition : Condition Q) : Condition Q :=
  fun yes no => condition no yes

@[simp, grind =] theorem ifThenElse_not (condition : Condition Q) (yes no : Prog Q Unit) :
    ifThenElse condition.not yes no = ifThenElse condition no yes := rfl

@[simp] theorem Condition.not_not (condition : Condition Q) : condition.not.not = condition := rfl

/-- Run at most `fuel` iterations, testing before each body. Zero fuel performs no test.
A condition that performs queries executes those queries anew on every test. -/
def repeatLoop (condition : Condition Q) (body : Prog Q Unit) : Nat → Prog Q Unit
  | 0 => pure ()
  | fuel + 1 => ifThenElse condition (do body; repeatLoop condition body fuel) (pure ())

@[simp, grind =] theorem repeatLoop_zero (condition : Condition Q) (body : Prog Q Unit) :
    repeatLoop condition body 0 = pure () := rfl

@[simp, grind =] theorem repeatLoop_succ
    (condition : Condition Q) (body : Prog Q Unit) (fuel : Nat) :
    repeatLoop condition body (fuel + 1) =
      ifThenElse condition (do body; repeatLoop condition body fuel) (pure ()) := rfl

end ControlFlowDefinitions

section ControlFlowNotation

/-- Model-controlled `if` inside a `do` block; enable with `open scoped Prog`. -/
scoped syntax "ifₚ " term " then " doSeq " else " doSeq : doElem

scoped macro_rules
  | `(doElem| ifₚ $condition then $yes else $no) =>
    `(doElem| Prog.ifThenElse $condition (do $yes) (do $no))

/-- Repeat an indented `Unit` body a fixed number of times; enable with `open scoped Prog`. -/
scoped macro "repeat " "[" fuel:term "]" ppLine body:doSeq : doElem =>
  `(doElem| Prog.repeatLoop (fun yes _ => yes) (do $body) $fuel)

end ControlFlowNotation

end Prog

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

section ControlFlowConditions

/-- Use an existing comparison flag as a condition, without running another comparison. -/
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

end ControlFlowConditions

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

/-- Distinct accessed memory cells, in words. -/
def space (c : RAMCost w k) : Nat := c.addresses.card

/-- Accessed memory outside the designated input region. -/
def auxiliarySpace (c : RAMCost w k) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses \ inputRegion).card

/-- All words in the footprint or input region, including unread input cells. -/
def totalSpace (c : RAMCost w k) (inputRegion : Finset (Word w)) : Nat :=
  (c.addresses ∪ inputRegion).card

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
def timeAndSpaceCost : ModelStateM (WordRAM w k) (StateM (RAMState w k)) (RAMCost w k) where
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
    runBlock (instructions p) = p.runStateM timeAndSpaceCost := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih =>
    cases q <;> simp [instructions, Prog.runStateM, Cslib.FreeM.liftM, ih]

/-- Branch on the incoming flag; charge only the executed body. -/
@[simp] theorem runStateM_branch (op : CmpOp) (yes no : Prog (WordRAM w k) Unit)
    (s : RAMState w k) :
    ((branch op yes no).runStateM timeAndSpaceCost).run s =
      if s.Flags op then (yes.runStateM timeAndSpaceCost).run s
      else (no.runStateM timeAndSpaceCost).run s := by
  simp [branch, runQuery]

/-- Program syntax determines the Lean return value independently of machine data. -/
def returnValue : Prog (WordRAM w k) α → α
  | .pure a => a
  | .liftBind q cont => returnValue (cont ((result_type q).symm ▸ ()))

/-- Input-dependent results must remain in machine state. -/
@[simp] theorem runStateM_ret (p : Prog (WordRAM w k) α) (s : RAMState w k) :
    let result := (p.runStateM timeAndSpaceCost).run s
    result.fst.ret = returnValue p := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind q cont ih => cases q <;> simp [returnValue, ih]

/-- No program can recover a machine flag into a Lean return value. -/
theorem runStateM_ret_independent (p : Prog (WordRAM w k) α) (s t : RAMState w k) :
    let left := (p.runStateM timeAndSpaceCost).run s
    let right := (p.runStateM timeAndSpaceCost).run t
    left.fst.ret = right.fst.ret := by simp only [runStateM_ret]

section FuelledExecution

/-- Interpreter fuel is separate from the machine state and its resource cost. -/
@[ext]
structure ExecutionState (w k : Nat) where
  /-- The physical memory, registers, and comparison flags. -/
  ram : RAMState w k
  /-- Remaining interpreter steps, excluded from RAM resource costs. -/
  fuel : Nat

/-- Exhaustion returns `none`, never a successful partial execution. -/
abbrev ExecutionM (w k : Nat) := StateT (ExecutionState w k) Option

mutual

/-- Consume one unit of interpreter fuel per instruction, including branch selection.
Primitive RAM costs are unchanged; branches consume fuel but no RAM time. -/
def runQueryWithFuel (q : WordRAM w k α) :
    AddWriterT (RAMCost w k) (ExecutionM w k) α := AddWriterT.mk fun s =>
  match s.fuel with
  | 0 => none
  | fuel + 1 =>
    match q with
    | .branchCode op yes no =>
      if s.ram.Flags op then (runBlockWithFuel yes).run { s with fuel }
      else (runBlockWithFuel no).run { s with fuel }
    | q =>
      let result := (runQuery q).run s.ram
      some (result.fst, ⟨result.snd, fuel⟩)

/-- Branch bodies share the remaining fuel with their enclosing program. -/
def runBlockWithFuel : List (WordRAM w k Unit) →
    AddWriterT (RAMCost w k) (ExecutionM w k) Unit
  | [] => pure ()
  | q :: qs => runQueryWithFuel q >>= fun _ => runBlockWithFuel qs

end

/-- Fuelled execution uses the existing joint model interface. -/
def fuelledModel : ModelStateM (WordRAM w k) (ExecutionM w k) (RAMCost w k) where
  runQuery := runQueryWithFuel

@[simp, grind =] theorem fuelledModel_runQuery (q : WordRAM w k α) :
    fuelledModel.runQuery q = runQueryWithFuel q := rfl

@[simp, grind =] theorem runQueryWithFuel_zero (q : WordRAM w k α) (s : RAMState w k) :
    (runQueryWithFuel q).run ⟨s, 0⟩ = none := by
  cases q <;> rfl

@[simp] theorem runBlockWithFuel_nil :
    runBlockWithFuel ([] : List (WordRAM w k Unit)) = pure () := by
  rw [runBlockWithFuel]

@[simp] theorem runBlockWithFuel_cons (q : WordRAM w k Unit) (qs : List (WordRAM w k Unit)) :
    runBlockWithFuel (q :: qs) =
      (runQueryWithFuel q >>= fun _ => runBlockWithFuel qs) := by
  rw [runBlockWithFuel]

@[simp] theorem runBlockWithFuel_instructions (p : Prog (WordRAM w k) Unit) :
    runBlockWithFuel (instructions p) = p.runStateM fuelledModel := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih =>
    cases q <;> simp [instructions, Prog.runStateM, Cslib.FreeM.liftM, ih]

/-- Run a program with a shared fuel budget, retaining unused fuel on success. -/
def execute (fuel : Nat) (p : Prog (WordRAM w k) α) (s : RAMState w k) :
    Option (AddWriter (RAMCost w k) α × ExecutionState w k) :=
  (p.runStateM fuelledModel).run ⟨s, fuel⟩

@[simp, grind =] theorem execute_pure (fuel : Nat) (a : α) (s : RAMState w k) :
    execute fuel (pure a) s = some (⟨a, 0⟩, ⟨s, fuel⟩) := rfl

@[simp] theorem execute_branch_succ (fuel : Nat) (op : CmpOp)
    (yes no : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    execute (fuel + 1) (branch op yes no) s =
      if s.Flags op then execute fuel yes s else execute fuel no s := by
  simp [execute, branch, Prog.runStateM, runQueryWithFuel]

/-- Sequence fuelled actions, threading both the RAM state and the remaining budget. -/
@[simp] theorem run_bind_execution
    (action : AddWriterT (RAMCost w k) (ExecutionM w k) α)
    (next : α → AddWriterT (RAMCost w k) (ExecutionM w k) β) (s : ExecutionState w k) :
    (action >>= next).run s = (do
      let (a, t) ← action.run s
      let (b, u) ← (next a.ret).run t
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := rfl

/-- Extra fuel preserves a successful result and is left unused. -/
def FuelStable (action : AddWriterT (RAMCost w k) (ExecutionM w k) α) : Prop :=
  ∀ (s : RAMState w k) fuel extra result final,
    action.run ⟨s, fuel⟩ = some (result, final) →
    action.run ⟨s, fuel + extra⟩ = some (result, { final with fuel := final.fuel + extra })

private theorem fuelStable_pure (a : α) :
    FuelStable (pure a : AddWriterT (RAMCost w k) (ExecutionM w k) α) := by
  intro s fuel extra result final h
  cases h
  rfl

private theorem fuelStable_bind
    (action : AddWriterT (RAMCost w k) (ExecutionM w k) α)
    (next : α → AddWriterT (RAMCost w k) (ExecutionM w k) β)
    (ha : FuelStable action) (hn : ∀ a, FuelStable (next a)) :
    FuelStable (action >>= next) := by
  intro s fuel extra result final h
  simp only [run_bind_execution] at h ⊢
  cases hf : action.run ⟨s, fuel⟩ with
  | none => simp [hf] at h
  | some first =>
    obtain ⟨a, t⟩ := first
    cases hs : (next a.ret).run t with
    | none => simp [hf, hs] at h
    | some second =>
      obtain ⟨b, u⟩ := second
      simp only [hf, Option.pure_def, Option.bind_eq_bind, Option.bind_some, hs,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [ha s fuel extra a t hf]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [hn a.ret t.ram t.fuel extra b u hs]
      rfl

mutual

private theorem runQueryWithFuel_stable (q : WordRAM w k α) :
    FuelStable (runQueryWithFuel q) := by
  intro s fuel extra result final h
  cases fuel with
  | zero => simp at h
  | succ fuel =>
    cases q with
    | branchCode op yes no =>
      simp only [runQueryWithFuel, AddWriterT.run_mk, Nat.succ_add] at h ⊢
      split at h
      · simpa only [if_pos ‹s.Flags op = true›] using
          runBlockWithFuel_stable yes s fuel extra result final h
      · simpa only [if_neg ‹¬s.Flags op = true›] using
          runBlockWithFuel_stable no s fuel extra result final h
    | _ =>
      simp only [runQueryWithFuel, AddWriterT.run_mk, Nat.succ_add,
        Option.some.injEq, Prod.mk.injEq] at h ⊢
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩

private theorem runBlockWithFuel_stable (qs : List (WordRAM w k Unit)) :
    FuelStable (runBlockWithFuel qs) := by
  cases qs with
  | nil => exact fuelStable_pure ()
  | cons q qs =>
    exact fuelStable_bind _ _ (runQueryWithFuel_stable q) (fun _ => runBlockWithFuel_stable qs)

end

/-- Once execution succeeds, additional fuel changes only the remaining fuel. -/
theorem execute_add_fuel (p : Prog (WordRAM w k) α) (s : RAMState w k)
    (fuel extra : Nat) (result : AddWriter (RAMCost w k) α) (final : ExecutionState w k)
    (h : execute fuel p s = some (result, final)) :
    execute (fuel + extra) p s = some (result, { final with fuel := final.fuel + extra }) := by
  have stable : ∀ (p : Prog (WordRAM w k) α), FuelStable (p.runStateM fuelledModel) := by
    intro p
    induction p with
    | pure a => exact fuelStable_pure a
    | liftBind q cont ih =>
      exact fuelStable_bind _ _ (runQueryWithFuel_stable q) ih
  exact stable p s fuel extra result final h

end FuelledExecution

end WordRAM


end Algolean.Algorithms
