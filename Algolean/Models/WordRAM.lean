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
or resource cost. `execute_ret` proves that Lean return values cannot depend on
machine data.
Literals are introduced by the charged `set` instruction; input values can also be supplied in
`RAMState`. The program observes computed words only through register-based instructions.

Words and addresses have the same fixed width. Arithmetic wraps modulo `2 ^ w`;
- comparisons are unsigned;
- shifts are logical and return zero when the shift amount is at least `w`;
- all `2 ^ w` memory cells are available;
- allocation and input encoding specify the initial state.

`timeAndSpaceCost` interprets each query jointly in
`AddWriterT (RAMCost w k) (ExecutionM w k)`.
Time adds and probe sets union across queries.
`runStateM` retains the result, cost, and final state;
`evalStateM` and `costStateM` project evaluation and resource usage from this semantics.

`RAMCost.space`, `auxiliarySpace`, and `totalSpace` count memory words only.
The fixed register file and comparison flags are excluded from space accounting.
Space counts distinct accessed cells. Auxiliary space excludes input memory; total space
includes input memory even if some cells were never read. Program size and host-language
construction costs are excluded.

## Fuelled execution

`execute fuel program state` runs through `timeAndSpaceCost`, an instance of `ModelStateM`.
Each executed instruction consumes one unit of interpreter fuel, including branch selection.
Branch bodies and continuations share the remaining budget; unselected bodies consume none.
Fuel is not RAM time. Exhaustion returns `none`; success returns the result, `RAMCost`, final
RAM state, and remaining fuel. Pure programs require no fuel. Additional fuel preserves any
successful execution, changing only the unused budget.

Branches and loops are constructors of `WordRAM` itself. Loop tests inspect existing flags
without charging RAM time. Comparisons in loop bodies are ordinary charged instructions.
Empty true loops exhaust fuel. The pending-code list is interpreter bookkeeping, inaccessible
to the machine. All execution uses the same fuelled model.

## Control-flow sugar

`open scoped Prog` enables `ifₚ condition then ... else ...` and `repeat [fuel]`
with an indented body. Repetition executes the body exactly `fuel` times.
Use `flag op` to inspect an existing flag, or `test op x y` to compare registers afresh.
Both bodies return `Unit`. These definitions expand into the existing programs and do not
change instruction costs. `open scoped WordRAM` enables `whileₚ op do` with an indented
body, checking the flag selected by `op`. The form `whileₚ op x y do` also performs a charged
comparison of registers `x` and `y` before each iteration and on exit. Neither form has a
program-level fuel argument.

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

@[simp, grind =] theorem RAMState.writeRegister_self (s : RAMState w k) (r : Register k) :
    s.writeRegister r (s.Registers r) = s := by
  simp [RAMState.writeRegister, Function.update_eq_self]

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
  | whileCode (op : WordRAM.CmpOp) (body : List (WordRAM w k Unit)) : WordRAM w k Unit

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

/-- Interpreter fuel is separate from the machine state and its resource cost. -/
@[ext]
structure ExecutionState (w k : Nat) where
  /-- The physical memory, registers, and comparison flags. -/
  ram : RAMState w k
  /-- Remaining interpreter steps, excluded from RAM resource costs. -/
  fuel : Nat

/-- Exhaustion returns `none`, never a successful partial execution. -/
abbrev ExecutionM (w k : Nat) := StateT (ExecutionState w k) Option

/-- Sequence fuelled actions, threading both the RAM state and the remaining budget. -/
@[simp] theorem run_bind_execution
    (action : AddWriterT (RAMCost w k) (ExecutionM w k) α)
    (next : α → AddWriterT (RAMCost w k) (ExecutionM w k) β) (s : ExecutionState w k) :
    (action >>= next).run s = (do
      let (a, t) ← action.run s
      let (b, u) ← (next a.ret).run t
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := rfl

/-- Repeat while the designated machine flag is true. Only instructions in the body can
update the flag. The test is free control flow, and each test consumes interpreter fuel. -/
def whileLoop (op : CmpOp) (body : Prog (WordRAM w k) Unit) : Prog (WordRAM w k) Unit :=
  Cslib.FreeM.lift (.whileCode op (instructions body))

/-- Recompute a charged register comparison before each iteration and on exit. -/
def whileCompare (op : CmpOp) (x y : Register k) (body : Prog (WordRAM w k) Unit) :
    Prog (WordRAM w k) Unit := do
  cmp (w := w) op x y
  whileLoop op (do body; cmp (w := w) op x y)

/-- Indented looping syntax over an existing machine comparison flag. -/
scoped macro "whileₚ " op:term:max " do " body:doSeq : doElem =>
  `(doElem| WordRAM.whileLoop $op (do $body))

/-- Indented looping syntax that performs a fresh register comparison each time. -/
scoped macro "whileₚ " op:term:max x:term:max y:term:max " do " body:doSeq : doElem =>
  `(doElem| WordRAM.whileCompare $op $x $y (do $body))

/-- One interpreter step, including pending code. -/
structure Step (w k : Nat) where
  /-- Charged primitive cost; branch and loop selection have zero cost. -/
  cost : RAMCost w k
  /-- Physical machine state. -/
  ram : RAMState w k
  /-- Remaining code, inaccessible to the machine. -/
  code : List (WordRAM w k Unit)

/-- Primitive instructions execute directly; structured control schedules its selected code. -/
def step (q : WordRAM w k Unit) (rest : List (WordRAM w k Unit))
    (s : RAMState w k) : Step w k :=
  match q with
  | .set dst value => ⟨⟨1, ∅⟩, s.writeRegister dst value, rest⟩
  | .copy dst src => ⟨⟨1, ∅⟩, s.writeRegister dst (s.Registers src), rest⟩
  | .load dst addr =>
    ⟨⟨1, {s.Registers addr}⟩, s.writeRegister dst (s.Memory (s.Registers addr)), rest⟩
  | .store addr src =>
    ⟨⟨1, {s.Registers addr}⟩,
      {s with Memory := Function.update s.Memory (s.Registers addr) (s.Registers src)}, rest⟩
  | .binop op dst x y =>
    ⟨⟨1, ∅⟩, s.writeRegister dst (op.eval (s.Registers x) (s.Registers y)), rest⟩
  | .bnot dst src => ⟨⟨1, ∅⟩, s.writeRegister dst (~~~s.Registers src), rest⟩
  | .cmp op x y => ⟨⟨1, ∅⟩, s.writeFlag op (op.eval (s.Registers x) (s.Registers y)), rest⟩
  | .clearFlag op => ⟨⟨1, ∅⟩, s.writeFlag op false, rest⟩
  | .branchCode op yes no => ⟨0, s, (if s.Flags op then yes else no) ++ rest⟩
  | .whileCode op body => ⟨0, s, if s.Flags op then body ++ q :: rest else rest⟩

/-- Execute pending code with one shared budget. Even an empty body consumes fuel on each test. -/
def runCode : Nat → List (WordRAM w k Unit) → RAMState w k →
    Option (AddWriter (RAMCost w k) Unit × ExecutionState w k)
  | fuel, [], s => some (⟨(), 0⟩, ⟨s, fuel⟩)
  | 0, _ :: _, _ => none
  | fuel + 1, q :: rest, s => do
    let next := step q rest s
    let (result, final) ← runCode fuel next.code next.ram
    pure (⟨(), next.cost + result.tell⟩, final)

/-- Interpret a block with shared fuel and exact joint resource costs. -/
def runBlock (code : List (WordRAM w k Unit)) :
    AddWriterT (RAMCost w k) (ExecutionM w k) Unit :=
  AddWriterT.mk fun s => runCode s.fuel code s.ram

/-- Interpret all WordRAM instructions through the existing joint model interface. -/
def timeAndSpaceCost : ModelStateM (WordRAM w k) (ExecutionM w k) (RAMCost w k) where
  runQuery q := (result_type q).symm ▸ runBlock [result_type q ▸ q]

theorem timeAndSpaceCost_runQuery (q : WordRAM w k Unit) :
    timeAndSpaceCost.runQuery q = runBlock [q] := rfl

/-- Execute a program containing machine-controlled loops. -/
def execute (fuel : Nat) (p : Prog (WordRAM w k) α) (s : RAMState w k) :
    Option (AddWriter (RAMCost w k) α × ExecutionState w k) :=
  (p.runStateM timeAndSpaceCost).run ⟨s, fuel⟩

@[simp, grind =] theorem runCode_nil (fuel : Nat) (s : RAMState w k) :
    runCode fuel [] s = some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  cases fuel <;> rfl

@[simp, grind =] theorem runCode_zero_cons (q : WordRAM w k Unit)
    (rest : List (WordRAM w k Unit)) (s : RAMState w k) : runCode 0 (q :: rest) s = none := rfl

@[simp, grind =] theorem execute_pure (fuel : Nat) (a : α) (s : RAMState w k) :
    execute fuel (pure a) s = some (⟨a, 0⟩, ⟨s, fuel⟩) := rfl

/-- Appending code preserves the next physical step. -/
@[simp] theorem step_append (q : WordRAM w k Unit) (rest tail : List (WordRAM w k Unit))
    (s : RAMState w k) :
    step q (rest ++ tail) s = {step q rest s with code := (step q rest s).code ++ tail} := by
  cases q with
  | whileCode => simp only [step]; split <;> simp [List.append_assoc]
  | _ => simp [step, List.append_assoc]

private theorem unit_ret (a : AddWriter (RAMCost w k) Unit) : a.ret = () :=
  Subsingleton.elim _ _

@[simp] private theorem unit_result (a : AddWriter (RAMCost w k) Unit) :
    (⟨(), a.tell⟩ : AddWriter (RAMCost w k) Unit) = a := by
  cases a with | mk ret tell => cases ret; rfl

/-- Executing concatenated code shares the budget and adds exactly the two execution costs. -/
theorem runCode_append (fuel : Nat) (code tail : List (WordRAM w k Unit)) (s : RAMState w k) :
    runCode fuel (code ++ tail) s = (do
      let (a, t) ← runCode fuel code s
      let (b, u) ← runCode t.fuel tail t.ram
      pure (⟨(), a.tell + b.tell⟩, u)) := by
  induction fuel generalizing code s with
  | zero =>
    cases code <;> simp [runCode]
  | succ fuel ih =>
    cases code with
    | nil => simp
    | cons q code =>
      simp only [List.cons_append, runCode, step_append, ih, bind_assoc]
      congr 1
      funext result
      obtain ⟨a, t⟩ := result
      simp [add_assoc]

@[simp] theorem runBlock_nil : runBlock ([] : List (WordRAM w k Unit)) = pure () := by
  funext s
  exact runCode_nil s.fuel s.ram

@[simp] theorem runBlock_cons (q : WordRAM w k Unit) (rest : List (WordRAM w k Unit)) :
    runBlock (q :: rest) = (timeAndSpaceCost.runQuery q >>= fun _ => runBlock rest) := by
  apply AddWriterT.ext
  funext s
  simpa only [timeAndSpaceCost_runQuery, run_bind_execution, runBlock, AddWriterT.run_mk,
    unit_ret, List.singleton_append] using
    runCode_append s.fuel [q] rest s.ram

@[simp] theorem runBlock_instructions (p : Prog (WordRAM w k) Unit) :
    runBlock (instructions p) = p.runStateM timeAndSpaceCost := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih =>
    cases q <;> simp [instructions, Prog.runStateM, Cslib.FreeM.liftM, ih]

/-- Additional fuel preserves a completed code execution, including its exact RAM cost. -/
theorem runCode_add_fuel (fuel extra : Nat) (code : List (WordRAM w k Unit)) (s : RAMState w k)
    (result : AddWriter (RAMCost w k) Unit) (final : ExecutionState w k)
    (h : runCode fuel code s = some (result, final)) :
    runCode (fuel + extra) code s = some (result, { final with fuel := final.fuel + extra }) := by
  induction fuel generalizing code s result final with
  | zero =>
    cases code with
    | nil => cases h; simp
    | cons => simp at h
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [runCode_nil, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp
    | cons q code =>
      simp only [Nat.succ_add, runCode] at h ⊢
      cases hr : runCode fuel (step q code s).code (step q code s).ram with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨a, t⟩ := pair
        simp only [hr, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih _ _ _ _ hr]
        rfl

/-- Once a loop-containing program completes, extra fuel cannot change its outcome or cost. -/
theorem execute_add_fuel (fuel extra : Nat) (p : Prog (WordRAM w k) Unit) (s : RAMState w k)
    (result : AddWriter (RAMCost w k) Unit) (final : ExecutionState w k)
    (h : execute fuel p s = some (result, final)) :
    execute (fuel + extra) p s = some (result, { final with fuel := final.fuel + extra }) := by
  simp only [execute, ← runBlock_instructions, runBlock, AddWriterT.run_mk] at h ⊢
  exact runCode_add_fuel fuel extra _ s result final h

/-- A completed block execution, with its exact cost and final RAM state. The witness is
interpreter fuel, not data available to the program. -/
def Completes (code : List (WordRAM w k Unit)) (s : RAMState w k)
    (cost : RAMCost w k) (final : RAMState w k) : Prop :=
  ∃ fuel, runCode fuel code s = some (⟨(), cost⟩, ⟨final, 0⟩)

@[simp] theorem completes_nil (s : RAMState w k) : Completes [] s 0 s := ⟨0, rfl⟩

theorem Completes.step {q : WordRAM w k Unit} {rest : List (WordRAM w k Unit)}
    {s t : RAMState w k} {cost : RAMCost w k}
    (h : Completes (step q rest s).code (step q rest s).ram cost t) :
    Completes (q :: rest) s ((step q rest s).cost + cost) t := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel + 1, by simp only [runCode, h]; rfl⟩

theorem Completes.append {code tail : List (WordRAM w k Unit)} {s t u : RAMState w k}
    {a b : RAMCost w k} (h : Completes code s a t) (ht : Completes tail t b u) :
    Completes (code ++ tail) s (a + b) u := by
  obtain ⟨fuel, h⟩ := h
  obtain ⟨extra, ht⟩ := ht
  refine ⟨fuel + extra, ?_⟩
  rw [runCode_append, runCode_add_fuel fuel extra _ _ _ _ h]
  simp [ht]
/-- Any completed execution agrees with the cost and RAM state of a completion witness. -/
theorem Completes.unique {code : List (WordRAM w k Unit)} {s t : RAMState w k}
    {cost : RAMCost w k} (h : Completes code s cost t) {fuel : Nat}
    {result : AddWriter (RAMCost w k) Unit} {final : ExecutionState w k}
    (hr : runCode fuel code s = some (result, final)) : result.tell = cost ∧ final.ram = t := by
  obtain ⟨used, h⟩ := h
  have h₁ := runCode_add_fuel used fuel code s _ _ h
  have h₂ := runCode_add_fuel fuel used code s _ _ hr
  rw [Nat.add_comm fuel used, h₁] at h₂
  simpa using congrArg (fun pair => (pair.fst.tell, pair.snd.ram)) (Option.some.inj h₂).symm

@[simp] theorem instructions_bind (p : Prog (WordRAM w k) Unit)
    (next : Unit → Prog (WordRAM w k) Unit) :
    instructions (p >>= next) = instructions p ++ instructions (next ()) := by
  induction p with
  | pure a => cases a; rfl
  | liftBind q cont ih => cases q <;> simp [instructions, ih]

/-- At the execution boundary, compilation and `ModelStateM.runStateM` coincide. -/
theorem execute_eq_runCode (fuel : Nat) (p : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    execute fuel p s = runCode fuel (instructions p) s := by
  simp [execute, ← runBlock_instructions, runBlock]

@[simp] theorem instructions_lift (q : WordRAM w k Unit) :
    instructions (Cslib.FreeM.lift q) = [q] := rfl

theorem completes_branch {op : CmpOp} {yes no : Prog (WordRAM w k) Unit}
    {s t : RAMState w k} {cost : RAMCost w k}
    (h : Completes (instructions (if s.Flags op then yes else no)) s cost t) :
    Completes (instructions (branch op yes no)) s cost t := by
  have hs : Completes (step (.branchCode op (instructions yes) (instructions no)) [] s).code
      (step (.branchCode op (instructions yes) (instructions no)) [] s).ram cost t := by
    simpa [step, apply_ite] using h
  simpa [branch, instructions, step] using hs.step

@[simp] theorem completes_while_false (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) (h : s.Flags op = false) :
    Completes (instructions (whileLoop op body)) s 0 s :=
  ⟨1, by simp [whileLoop, runCode, step, h]⟩

/-- A loop iteration composes the body's exact execution with the remaining iterations. -/
theorem completes_while_true (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    {s t u : RAMState w k} {a b : RAMCost w k} (h : s.Flags op = true)
    (hb : Completes (instructions body) s a t)
    (hr : Completes (instructions (whileLoop op body)) t b u) :
    Completes (instructions (whileLoop op body)) s (a + b) u := by
  have joined := hb.append hr
  have hs : Completes (step (.whileCode op (instructions body)) [] s).code
      (step (.whileCode op (instructions body)) [] s).ram (a + b) u := by
    simpa [step, whileLoop, h] using joined
  simpa [step, whileLoop] using hs.step

/-- Completion supplies sufficient interpreter fuel. -/
theorem Completes.execute {p : Prog (WordRAM w k) Unit} {s t : RAMState w k}
    {cost : RAMCost w k} (h : Completes (instructions p) s cost t) :
    ∃ fuel, execute fuel p s = some (⟨(), cost⟩, ⟨t, 0⟩) := by
  simpa only [execute_eq_runCode, Completes] using h

/-- Branch selection consumes fuel, but no primitive-operation time. -/
@[simp, grind =] theorem execute_branch_succ (fuel : Nat) (op : CmpOp)
    (yes no : Prog (WordRAM w k) Unit) (s : RAMState w k) :
    execute (fuel + 1) (branch op yes no) s =
      if s.Flags op then execute fuel yes s else execute fuel no s := by
  simp only [execute_eq_runCode, branch, instructions, runCode, step]
  split <;> simp

@[simp, grind =] theorem execute_while_zero (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) : execute 0 (whileLoop op body) s = none := by
  simp [execute_eq_runCode, whileLoop]

/-- A loop test reads its flag without modifying registers, memory, or RAM cost. -/
theorem execute_while_succ (fuel : Nat) (op : CmpOp) (body : Prog (WordRAM w k) Unit)
    (s : RAMState w k) :
    execute (fuel + 1) (whileLoop op body) s =
      if s.Flags op then execute fuel (do body; whileLoop op body) s
      else some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  simp only [execute_eq_runCode, whileLoop, instructions_lift, instructions_bind, runCode, step]
  split <;> simp

@[simp] theorem execute_while_false (fuel : Nat) (op : CmpOp)
    (body : Prog (WordRAM w k) Unit) (s : RAMState w k) (h : s.Flags op = false) :
    execute (fuel + 1) (whileLoop op body) s = some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  simp [execute_while_succ, h]

@[simp] theorem execute_while_true (fuel : Nat) (op : CmpOp)
    (body : Prog (WordRAM w k) Unit) (s : RAMState w k) (h : s.Flags op = true) :
    execute (fuel + 1) (whileLoop op body) s =
      execute fuel (do body; whileLoop op body) s := by
  simp [execute_while_succ, h]

/-- Host-language return values are fixed by syntax; queries return only `Unit`. -/
def returnValue : Prog (WordRAM w k) α → α
  | .pure a => a
  | .liftBind q next => returnValue (next ((result_type q).symm ▸ ()))

@[simp] theorem returnValue_unit (p : Prog (WordRAM w k) Unit) : returnValue p = () :=
  Subsingleton.elim _ _

/-- Replacing the return value by its syntactically fixed value preserves the program. -/
theorem eq_bind_return (p : Prog (WordRAM w k) α) :
    p = (p >>= fun _ => pure (returnValue p)) := by
  induction p with
  | pure a => rfl
  | liftBind q next ih =>
    cases q <;> apply congrArg (Cslib.FreeM.liftBind _)
    all_goals
      funext u
      cases u
      exact ih ()

/-- Completed execution cannot reveal a register, flag, or memory word through a Lean result. -/
theorem execute_ret (p : Prog (WordRAM w k) α) (s : RAMState w k) (fuel : Nat)
    (result : AddWriter (RAMCost w k) α) (final : ExecutionState w k)
    (h : execute fuel p s = some (result, final)) : result.ret = returnValue p := by
  have hr := h
  rw [eq_bind_return p] at hr
  simp only [execute] at h hr
  simp only [Prog.runStateM_bind, run_bind_execution, h, Option.bind_eq_bind,
    Option.bind_some, Prog.runStateM_pure, AddWriterT.run_pure] at hr
  have hout := congrArg (fun r => r.map (fun pair => pair.fst.ret)) hr
  simpa [StateT.pure, Pure.pure, AddWriter.pure] using hout.symm

/-- Two successful runs have the same Lean return value, regardless of their machine inputs. -/
theorem execute_ret_independent (p : Prog (WordRAM w k) α) (s t : RAMState w k)
    {fuel fuel' : Nat} {result result' : AddWriter (RAMCost w k) α}
    {final final' : ExecutionState w k}
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret :=
  (execute_ret p s fuel result final h).trans (execute_ret p t fuel' result' final' h').symm

end WordRAM

end Algolean.Algorithms
