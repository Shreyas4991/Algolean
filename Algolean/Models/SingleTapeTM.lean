/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.ModelStateM
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Data.Int.Interval

/-!
# Deeply embedded single-tape TM programs

`TMQuery tm` describes tape writes, control-state updates, head moves, branches, and loops.
Every query returns `Unit`: tape symbols and control states remain inside `TMState`.
`TMCondition` is a finite syntax for testing those values inside the interpreter.
`TMQuery.branch` and `TMQuery.whileLoop` accept `Prog` bodies and compile them to finite code.

An algorithm is a fixed program, independent of its input and input length. Supply input only
through the initial machine state, and observe output through the final configuration.
`TMQuery.execute fuel program state` runs it through `TMModel`, which uses
`StateT (TMQuery.ExecutionState tm) Option`. Each instruction, branch selection, and loop test
consumes interpreter fuel. Exhaustion returns `none`, including for an empty infinite loop.
Fuel is external to the program and separate from the machine's time and space costs.
`TMQuery.execute_ret_independent` proves that successful runs of a fixed program cannot
reveal machine data through their Lean return values.

Space counts the length of the allocated tape, following the ordinary-machine case of
Papadimitriou [§2.5, Definition 2.6, p. 35][papadimitriou1994]. The whole input counts from
the start, including cells the head has not visited. Moving outside the allocated tape adds
a blank cell. Erasing symbols and returning the head do not shorten the allocated tape.
There are no separate read-only input and write-only output tapes to exclude from this count.

Our tape representation is bidirectional and has no left-end marker. Its initial allocated
length is `max 1 input.length`, including the head cell for an empty input. The textbook uses
a one-sided string with a left-end marker, initially of length `input.length + 1`.
We use its storage-counting rule with this explicit difference in tape representation.

`TMState.cellsAllocated` retains every initially stored or subsequently reached cell;
its cardinality gives total space. `TMCost.cellsAllocated` measures additional allocated cells.
`TMState.cellsVisited` separately records cells actually visited by the head and is not the
space measure. Both records are retained when procedures are composed.
Time continues to count `move` queries, including `Dir.Stop`.
Writing, control-state updates, and condition tests carry no additional time cost.

## References

* [Christos H. Papadimitriou, *Computational Complexity*, Addison-Wesley, Reading, MA,
  1994, §2.5, Definition 2.6, p. 35. ISBN 0-201-53082-1.][papadimitriou1994]

[papadimitriou1994]: https://www2.eecs.berkeley.edu/Pubs/Faculty/papadimitriou.html
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog Turing

variable {Symbol : Type}

/-- Add a separator to an alphabet. Original symbols remain distinguishable from the separator;
the tape's blank is still represented separately by `none`. -/
inductive Augmented (Symbol : Type) where
  | symbol : Symbol → Augmented Symbol
  | separator : Augmented Symbol
deriving DecidableEq

namespace Augmented

theorem symbol_injective : Function.Injective (@symbol Symbol) := fun _ _ h => symbol.inj h

/-- Tagging every symbol preserves equality of words. -/
@[simp, grind =] theorem map_symbol_inj {x y : List Symbol} :
    x.map symbol = y.map symbol ↔ x = y :=
  List.map_inj_right (fun _ _ h => symbol.inj h)

instance : Inhabited (Augmented Symbol) := ⟨.separator⟩

/-- Identify the augmented alphabet with an optional original symbol. -/
def equivOption : Augmented Symbol ≃ Option Symbol where
  toFun
    | .symbol a => some a
    | .separator => none
  invFun
    | some a => .symbol a
    | none => .separator
  left_inv a := by cases a <;> rfl
  right_inv a := by cases a <;> rfl

instance [Fintype Symbol] : Fintype (Augmented Symbol) :=
  Fintype.ofEquiv (Option Symbol) equivOption.symm

/-- Put two words on one tape with an explicit boundary between them. -/
def encodePair (input certificate : List Symbol) : List (Augmented Symbol) :=
  input.map .symbol ++ .separator :: certificate.map .symbol

/-- Read the original symbols before the first separator, or the whole word if none occurs. -/
def firstWord : List (Augmented Symbol) → List Symbol
  | [] => []
  | .symbol a :: rest => a :: firstWord rest
  | .separator :: _ => []

/-- The part after the first separator; empty when the separator is missing. -/
def afterSeparator : List (Augmented Symbol) → List (Augmented Symbol)
  | [] => []
  | .symbol _ :: rest => afterSeparator rest
  | .separator :: rest => rest

@[simp] theorem firstWord_encodePair (input certificate : List Symbol) :
    firstWord (encodePair input certificate) = input := by
  induction input <;> simp_all [encodePair, firstWord]

@[simp] theorem length_encodePair (input certificate : List Symbol) :
    (encodePair input certificate).length = input.length + certificate.length + 1 := by
  simp [encodePair]
  lia

theorem encodePair_injective :
    Function.Injective (fun p : List Symbol × List Symbol => encodePair p.1 p.2) := by
  rintro ⟨x, c⟩ ⟨y, d⟩ h
  have hx : x = y := by simpa using congrArg firstWord h
  subst y
  have hc : c = d := by
    have hm : c.map symbol = d.map symbol := by simpa [encodePair] using h
    exact (List.map_inj_right (fun _ _ h => symbol.inj h)).mp hm
  subst d
  rfl

/-- The two portions retained by the parser occupy at most the original word's length. -/
theorem lengths_le (word : List (Augmented Symbol)) :
    (firstWord word).length + (afterSeparator word).length ≤ word.length := by
  induction word with
  | nil => simp [firstWord, afterSeparator]
  | cons a rest ih =>
    cases a <;> simp_all [firstWord, afterSeparator]
    lia

/-- Removing the separator and certificate cannot lengthen the input word. -/
@[grind! .] theorem length_firstWord_le (input : List (Augmented Symbol)) :
    (firstWord input).length ≤ input.length := by
  have := lengths_le input
  lia

end Augmented

variable [Inhabited Symbol] [Fintype Symbol]

/--
The directions in which one can take move on the Turing Machine's tape.
-/
inductive Dir where
  | Left
  | Right
  | Stop

/-- Conditions are syntax, evaluated only inside the machine model. -/
inductive TMCondition (tm : SingleTapeTM Symbol) where
  /-- Test the symbol under the head against a fixed symbol or blank. -/
  | tapeIs (symbol : Option Symbol)
  /-- Test the control state against a fixed state or the halting label. -/
  | stateIs (state : Option tm.State)
  /-- Negate a machine condition without revealing its result. -/
  | not (condition : TMCondition tm)

/-- Primitive instructions and structured control; every query returns `Unit`. -/
inductive TMQuery (tm : SingleTapeTM Symbol) : Type → Type where
  /-- Write a symbol under the TM head on the tape -/
  | write (s : Option Symbol) : TMQuery tm Unit
  /-- Update the TM's state -/
  | update (st : tm.State) : TMQuery tm Unit
  /-- Move the TM one step in the specified direction or stay in place -/
  | move (dir : Dir) : TMQuery tm Unit
  /-- Select a code block using a condition evaluated inside the machine. -/
  | branchCode (condition : TMCondition tm) (yes no : List (TMQuery tm Unit)) : TMQuery tm Unit
  /-- Repeat a code block while a machine condition holds. -/
  | whileCode (condition : TMCondition tm) (body : List (TMQuery tm Unit)) : TMQuery tm Unit

/-- The configuration, allocated tape, and head visits of a single-tape query execution. -/
@[ext, grind]
structure TMState (tm : SingleTapeTM Symbol) where
  /-- The current machine configuration. -/
  config : tm.Cfg
  /-- Head position relative to its initial cell, with negative positions to the left. -/
  headPos : ℤ := 0
  /-- Allocated positions. Initially these cover the stored tape and the head cell. -/
  cellsAllocated : Finset ℤ := Finset.Icc
    (headPos - config.BiTape.left.length) (headPos + config.BiTape.right.length)
  /-- Distinct positions actually visited by the head, independent of allocated input cells. -/
  cellsVisited : Finset ℤ := {headPos}

/-- Initialize the machine on an input, with its head at position zero. -/
@[simps]
def TMState.init (tm : SingleTapeTM Symbol) (input : List Symbol) : TMState tm where
  config := tm.initCfg input

/-- Total storage includes allocated blank cells and unvisited input cells. -/
def TMState.spaceUsed {tm : SingleTapeTM Symbol} (s : TMState tm) : ℕ :=
  s.cellsAllocated.card

/-- Input storage is charged before the program executes any instruction. -/
@[simp] theorem TMState.spaceUsed_init (tm : SingleTapeTM Symbol) (input : List Symbol) :
    (TMState.init tm input).spaceUsed = max 1 input.length := by
  cases input <;> simp [TMState.init, SingleTapeTM.initCfg, BiTape.mk₁, BiTape.nil,
    TMState.spaceUsed, StackTape.length_nil, StackTape.length_mapSome, Int.card_Icc]

/-- Allocated cells form one finite tape segment containing the head. -/
def TMState.AllocatedInterval {tm : SingleTapeTM Symbol} (s : TMState tm) : Prop :=
  ∃ lo hi, s.cellsAllocated = Finset.Icc lo hi ∧ lo ≤ s.headPos ∧ s.headPos ≤ hi

/-- The initially stored input and head cell form a tape segment. -/
@[simp] theorem TMState.allocatedInterval_init (tm : SingleTapeTM Symbol) (input : List Symbol) :
    (TMState.init tm input).AllocatedInterval := by
  refine ⟨_, _, rfl, ?_, ?_⟩ <;> simp [TMState.init]

/-- Interpret condition syntax against a configuration, solely inside the model. -/
@[simp, grind]
def TMCondition.eval {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State] :
    TMCondition tm → tm.Cfg → Bool
  | .tapeIs symbol, cfg => decide (cfg.BiTape.head = symbol)
  | .stateIs state, cfg => decide (cfg.state = state)
  | .not condition, cfg => !(condition.eval cfg)

/--
The Turing machine cost structure.
-/
@[ext, grind]
structure TMCost where
  /-- `steps` counts the number of moves in the TM -/
  steps : ℕ
  /-- Number of additional allocated cells, beyond the initial state's stored tape. -/
  cellsAllocated : ℕ


/-- Equivalence between `TMCost` and a product type. -/
@[simps]
def TMCost.equivProd : TMCost ≃ (ℕ × ℕ) where
  toFun tmOps := (tmOps.steps, tmOps.cellsAllocated)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace TMCost

@[simps, grind]
instance : Zero TMCost := ⟨0, 0⟩

@[simps]
instance : LE TMCost where
  le soc₁ soc₂ := soc₁.steps ≤ soc₂.steps ∧ soc₁.cellsAllocated ≤ soc₂.cellsAllocated

instance : LT TMCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder TMCost :=
  fast_instance% TMCost.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add TMCost where
  add soc₁ soc₂ := ⟨soc₁.steps + soc₂.steps, soc₁.cellsAllocated + soc₂.cellsAllocated⟩

@[simps]
instance : SMul ℕ TMCost where
  smul n soc := ⟨n • soc.steps, n • soc.cellsAllocated⟩

instance : AddCommMonoid TMCost :=
  fast_instance%
    TMCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

attribute [grind =] le_def zero_steps zero_cellsAllocated add_steps add_cellsAllocated

instance : CovariantClass TMCost TMCost (· + ·) (· ≤ ·) where
  elim a b c h := by grind

end TMCost

namespace TMQuery

variable {tm : SingleTapeTM Symbol}

/-- No instruction can pass a tape symbol or control state to a Lean continuation. -/
theorem result_type (q : TMQuery tm α) : α = Unit := by
  cases q <;> rfl

/-- Compile a program body to finite code without consulting any machine data. -/
def instructions : Prog (TMQuery tm) Unit → List (TMQuery tm Unit)
  | .pure _ => []
  | .liftBind q next =>
    (result_type q ▸ q) :: instructions (next ((result_type q).symm ▸ ()))

@[simp, grind =] theorem instructions_pure :
    instructions (pure () : Prog (TMQuery tm) Unit) = [] := rfl

@[simp, grind =] theorem instructions_lift_bind (q : TMQuery tm Unit)
    (next : Unit → Prog (TMQuery tm) Unit) :
    instructions (FreeM.lift q >>= next) = q :: instructions (next ()) := rfl

@[simp, grind =] theorem instructions_bind (p : Prog (TMQuery tm) Unit)
    (next : Unit → Prog (TMQuery tm) Unit) :
    instructions (p >>= next) = instructions p ++ instructions (next ()) := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih => cases q <;> simp_all [instructions]

@[simp, grind =] theorem instructions_lift (q : TMQuery tm Unit) :
    instructions (Cslib.FreeM.lift q) = [q] := rfl

/-- Host-language return values are fixed by syntax; queries return only `Unit`. -/
def returnValue : Prog (TMQuery tm) α → α
  | .pure a => a
  | .liftBind q next => returnValue (next ((result_type q).symm ▸ ()))

@[simp] theorem returnValue_unit (p : Prog (TMQuery tm) Unit) : returnValue p = () :=
  Subsingleton.elim _ _

/-- Replacing the return value by its syntactically fixed value preserves the program. -/
theorem eq_bind_return (p : Prog (TMQuery tm) α) :
    p = (p >>= fun _ => pure (returnValue p)) := by
  induction p with
  | pure a => rfl
  | liftBind q next ih =>
    cases q <;> simp only [← FreeM.bind_eq_bind, FreeM.bind, returnValue]
    all_goals congr 1; funext u; cases u; simpa only [FreeM.bind_eq_bind] using ih ()

/-- Branch inside the model without returning a decision to Lean. -/
def branch (condition : TMCondition tm) (yes no : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit :=
  FreeM.lift (.branchCode condition (instructions yes) (instructions no))

/-- Repeat a fixed body, testing its condition inside the model on every iteration. -/
def whileLoop (condition : TMCondition tm) (body : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit :=
  FreeM.lift (.whileCode condition (instructions body))

/-- Interpreter fuel is kept separately from the physical machine state. -/
@[ext, grind]
structure ExecutionState (tm : SingleTapeTM Symbol) where
  /-- Current configuration, head position, allocated tape, and visited-cell history. -/
  machine : TMState tm
  /-- Remaining interpreter steps; inaccessible to programs. -/
  fuel : ℕ

/-- Fuel exhaustion fails the whole execution rather than returning a partial result. -/
abbrev ExecutionM (tm : SingleTapeTM Symbol) := StateT (ExecutionState tm) Option

/-- Sequence fuelled actions, threading both the machine state and the remaining budget. -/
@[simp, grind =] theorem run_bind_execution
    (action : AddWriterT TMCost (ExecutionM tm) α)
    (next : α → AddWriterT TMCost (ExecutionM tm) β) (s : ExecutionState tm) :
    (action >>= next).run s = (do
      let (a, t) ← action.run s
      let (b, u) ← (next a.ret).run t
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := rfl

/-- One small step, with pending code kept outside the physical machine state. -/
@[ext, grind]
structure Step (tm : SingleTapeTM Symbol) where
  /-- Resource cost of this step. -/
  cost : TMCost
  /-- Updated physical machine state. -/
  machine : TMState tm
  /-- Code still to execute. -/
  code : List (TMQuery tm Unit)

variable [DecidableEq Symbol] [DecidableEq tm.State]

/-- Execute a primitive instruction or schedule the selected control-flow block. -/
def step (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) (s : TMState tm) : Step tm :=
  match q with
  | .write symbol => ⟨0, {s with config.BiTape := s.config.BiTape.write symbol}, rest⟩
  | .update st => ⟨0, {s with config.state := some st}, rest⟩
  | .move dir =>
    let (tape, pos) := match dir with
      | .Left => (s.config.BiTape.moveLeft, s.headPos - 1)
      | .Right => (s.config.BiTape.moveRight, s.headPos + 1)
      | .Stop => (s.config.BiTape, s.headPos)
    ⟨⟨1, if pos ∈ s.cellsAllocated then 0 else 1⟩,
      {s with
        config := {s.config with BiTape := tape}
        headPos := pos
        cellsAllocated := insert pos s.cellsAllocated
        cellsVisited := insert pos s.cellsVisited}, rest⟩
  | .branchCode condition yes no =>
    ⟨0, s, (if condition.eval s.config then yes else no) ++ rest⟩
  | .whileCode condition body =>
    ⟨0, s, if condition.eval s.config then body ++ q :: rest else rest⟩

private theorem insert_Icc_adjacent {lo hi pos : ℤ}
    (hlo : lo - 1 ≤ pos) (hhi : pos ≤ hi + 1) :
    insert pos (Finset.Icc lo hi) = Finset.Icc (min lo pos) (max hi pos) := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_Icc, min_le_iff, le_max_iff]
  lia

/-- A head move can extend either end of the stored tape but cannot create a gap. -/
theorem step_allocatedInterval (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (s : TMState tm) (h : s.AllocatedInterval) : (step q rest s).machine.AllocatedInterval := by
  obtain ⟨lo, hi, hs, hlo, hhi⟩ := h
  cases q with
  | move dir =>
    cases dir <;>
      refine ⟨min lo _, max hi _, ?_, min_le_right _ _, le_max_right _ _⟩ <;>
      simpa [step, hs] using insert_Icc_adjacent (lo := lo) (hi := hi) (by lia) (by lia)
  | _ => exact ⟨lo, hi, hs, hlo, hhi⟩

/-- Shared structured-code runner, parameterized only by its model's small-step semantics. -/
@[simp] def runCodeWith
    (nextStep : TMQuery tm Unit → List (TMQuery tm Unit) → TMState tm → Step tm) :
    ℕ → List (TMQuery tm Unit) → TMState tm →
    Option (AddWriter TMCost Unit × ExecutionState tm)
  | fuel, [], s => some (⟨(), 0⟩, ⟨s, fuel⟩)
  | 0, _ :: _, _ => none
  | fuel + 1, q :: rest, s => do
    let next := nextStep q rest s
    let (result, final) ← runCodeWith nextStep fuel next.code next.machine
    pure (⟨(), next.cost + result.tell⟩, final)

/-- Run pending code with shared fuel; every instruction and control test consumes one unit. -/
def runCode := runCodeWith (step (tm := tm))

/-- Interpret a finite block through the joint state-and-cost interface. -/
def runBlock (code : List (TMQuery tm Unit)) : AddWriterT TMCost (ExecutionM tm) Unit :=
  AddWriterT.mk fun s => runCode s.fuel code s.machine

end TMQuery

/-- Stateful execution and costs for deeply embedded single-tape programs. -/
def TMModel (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State] :
    ModelStateM (TMQuery tm) (TMQuery.ExecutionM tm) TMCost where
  runQuery q := (TMQuery.result_type q).symm ▸ TMQuery.runBlock [TMQuery.result_type q ▸ q]

namespace TMQuery

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Execute a fixed program on a separately supplied input state. -/
def execute (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm) :
    Option (AddWriter TMCost α × ExecutionState tm) :=
  (p.runStateM (TMModel tm)).run ⟨s, fuel⟩

theorem model_runQuery (q : TMQuery tm Unit) :
    (TMModel tm).runQuery q = runBlock [q] := rfl

@[simp, grind =] theorem runCode_nil (fuel : Nat) (s : TMState tm) :
    runCode fuel [] s = some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  cases fuel <;> rfl

@[simp, grind =] theorem runCode_zero_cons (q : TMQuery tm Unit)
    (rest : List (TMQuery tm Unit)) (s : TMState tm) : runCode 0 (q :: rest) s = none := rfl

@[simp, grind =] theorem execute_pure (fuel : Nat) (a : α) (s : TMState tm) :
    execute fuel (pure a) s = some (⟨a, 0⟩, ⟨s, fuel⟩) := rfl

/-- Sequencing shares the remaining fuel and accumulates the joint execution costs. -/
@[simp, grind =] theorem execute_bind (fuel : ℕ) (p : Prog (TMQuery tm) α)
    (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    execute fuel (p >>= next) s = (do
      let (a, t) ← execute fuel p s
      let (b, u) ← execute t.fuel (next a.ret) t.machine
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := by
  simp [execute, Prog.runStateM_bind]

/-- Appending code preserves the next physical step. -/
@[simp, grind =] theorem step_append (q : TMQuery tm Unit) (rest tail : List (TMQuery tm Unit))
    (s : TMState tm) :
    step q (rest ++ tail) s = {step q rest s with code := (step q rest s).code ++ tail} := by
  cases q <;> simp [step, List.append_assoc]
  split <;> simp [List.append_assoc]

private theorem unit_ret (a : AddWriter TMCost Unit) : a.ret = () :=
  Subsingleton.elim _ _

@[simp] private theorem unit_result (a : AddWriter TMCost Unit) :
    (⟨(), a.tell⟩ : AddWriter TMCost Unit) = a := by
  cases a with | mk ret tell => cases ret; rfl

omit [DecidableEq Symbol] [DecidableEq tm.State] in
/-- Executing concatenated code shares the budget and adds exactly the two execution costs. -/
theorem runCodeWith_append
    (nextStep : TMQuery tm Unit → List (TMQuery tm Unit) → TMState tm → Step tm)
    (append : ∀ q rest tail s, nextStep q (rest ++ tail) s =
      { nextStep q rest s with code := (nextStep q rest s).code ++ tail })
    (fuel : ℕ) (code tail : List (TMQuery tm Unit)) (s : TMState tm) :
    runCodeWith nextStep fuel (code ++ tail) s = (do
      let (a, t) ← runCodeWith nextStep fuel code s
      let (b, u) ← runCodeWith nextStep t.fuel tail t.machine
      pure (⟨(), a.tell + b.tell⟩, u)) := by
  induction fuel generalizing code s with
  | zero => cases code <;> simp
  | succ fuel ih => cases code <;> simp [append, ih, Option.bind_assoc, add_assoc]

/-- Executing concatenated ordinary code adds costs and shares the remaining budget. -/
theorem runCode_append (fuel : Nat) (code tail : List (TMQuery tm Unit)) (s : TMState tm) :
    runCode fuel (code ++ tail) s = (do
      let (a, t) ← runCode fuel code s
      let (b, u) ← runCode t.fuel tail t.machine
      pure (⟨(), a.tell + b.tell⟩, u)) := by
  exact runCodeWith_append step step_append fuel code tail s

@[simp] theorem runBlock_nil : runBlock ([] : List (TMQuery tm Unit)) = pure () := by
  funext s
  exact runCode_nil s.fuel s.machine

@[simp] theorem runBlock_cons (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) :
    runBlock (q :: rest) = ((TMModel tm).runQuery q >>= fun _ => runBlock rest) := by
  apply AddWriterT.ext
  funext s
  simpa only [model_runQuery, run_bind_execution, runBlock, AddWriterT.run_mk,
    unit_ret, List.singleton_append] using
    runCode_append s.fuel [q] rest s.machine

@[simp, grind =] theorem runBlock_instructions (p : Prog (TMQuery tm) Unit) :
    runBlock (instructions p) = p.runStateM (TMModel tm) := by
  induction p with
  | pure a => cases a; simp
  | liftBind q cont ih => cases q <;> simp_all [Prog.runStateM, FreeM.liftM]

/-- Additional fuel preserves a completed code execution, including its exact TM cost. -/
theorem runCode_add_fuel (fuel extra : Nat) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    runCode (fuel + extra) code s = some (result, { final with fuel := final.fuel + extra }) := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q code =>
      cases hr : runCode fuel (step q code s).code (step q code s).machine <;>
        simp_all [runCode, Nat.succ_add]
      grind [Option.bind_eq_some_iff]

/-- Once a loop-containing program completes, extra fuel cannot change its outcome or cost. -/
theorem execute_add_fuel (fuel extra : Nat) (p : Prog (TMQuery tm) Unit) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) :
    execute (fuel + extra) p s = some (result, { final with fuel := final.fuel + extra }) := by
  simp only [execute, ← runBlock_instructions, runBlock, AddWriterT.run_mk] at h ⊢
  exact runCode_add_fuel fuel extra _ s result final h

/-- At the execution boundary, compilation and `ModelStateM.runStateM` coincide. -/
@[grind =] theorem execute_eq_runCode (fuel : Nat) (p : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute fuel p s = runCode fuel (instructions p) s := by
  simp [execute, ← runBlock_instructions, runBlock]

/-- Branch selection consumes one unit of fuel and executes only the selected body. -/
@[simp, grind =] theorem execute_branch_succ (fuel : ℕ) (condition : TMCondition tm)
    (yes no : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute (fuel + 1) (branch condition yes no) s =
      if condition.eval s.config then execute fuel yes s else execute fuel no s := by
  simp only [execute_eq_runCode, branch, instructions_lift, runCode, runCodeWith, step]
  split <;> simp

@[simp, grind =] theorem execute_while_zero (condition : TMCondition tm)
    (body : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute 0 (whileLoop condition body) s = none := by
  simp [execute_eq_runCode, whileLoop]

/-- Loop tests consume fuel, while the selected body determines the machine cost and state. -/
@[grind =] theorem execute_while_succ (fuel : ℕ) (condition : TMCondition tm)
    (body : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute (fuel + 1) (whileLoop condition body) s =
      if condition.eval s.config then execute fuel (do body; whileLoop condition body) s
      else some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  simp only [execute_eq_runCode, whileLoop, instructions_lift, instructions_bind,
    runCode, runCodeWith, step]
  split <;> simp

/-- A step's space charge is exactly the number of additional allocated cells. -/
@[grind ←] theorem step_cellsAllocated (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (s : TMState tm) :
    s.cellsAllocated.card + (step q rest s).cost.cellsAllocated =
      (step q rest s).machine.cellsAllocated.card := by
  cases q with
  | move dir => cases dir <;> grind [step]
  | _ => simp [step]

/-- Completed code charges each additional allocated cell once, through branches and loops. -/
@[grind →] theorem runCode_cellsAllocated (fuel : ℕ) (code : List (TMQuery tm Unit))
    (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    s.cellsAllocated.card + result.tell.cellsAllocated = final.machine.cellsAllocated.card := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q code =>
      cases hr : runCode fuel (step q code s).code (step q code s).machine <;>
        simp_all [runCode]
      grind

/-- Total storage is the initially allocated tape plus the accumulated space cost. -/
@[grind →] theorem execute_cellsAllocated (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) :
    s.cellsAllocated.card + result.tell.cellsAllocated = final.machine.cellsAllocated.card := by
  grind

/-- A completed program retains a single allocated tape segment, even after erasure. -/
theorem runCode_allocatedInterval (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) (hs : s.AllocatedInterval) :
    final.machine.AllocatedInterval := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q rest =>
      cases hr : runCodeWith step fuel (step q rest s).code (step q rest s).machine with
      | none => simp [runCode, hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        have hu := ih _ _ _ _ hr (step_allocatedInterval q rest s hs)
        simp_all [runCode]

/-- Storage after an initialized run includes the entire input and every tape extension. -/
theorem execute_spaceUsed (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (input : List Symbol)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : execute fuel p (TMState.init tm input) = some (result, final)) :
    final.machine.spaceUsed = max 1 input.length + result.tell.cellsAllocated := by
  have := execute_cellsAllocated fuel p (TMState.init tm input) result final h
  change (TMState.init tm input).spaceUsed + _ = final.machine.spaceUsed at this
  simpa using this.symm

/-- The space of an initialized run is the length of one retained tape segment. -/
theorem execute_allocatedInterval (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (input : List Symbol)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : execute fuel p (TMState.init tm input) = some (result, final)) :
    final.machine.AllocatedInterval := by
  rw [execute_eq_runCode] at h
  exact runCode_allocatedInterval _ _ _ _ _ h (TMState.allocatedInterval_init tm input)

/-- Completed execution cannot reveal a tape symbol or control state through a Lean result. -/
@[grind →] theorem execute_ret (p : Prog (TMQuery tm) α) (s : TMState tm) (fuel : Nat)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) : result.ret = returnValue p := by
  have hr := h
  rw [eq_bind_return p] at hr
  simp only [execute_bind, h, execute_pure, Option.pure_def] at hr
  grind

/-- Two successful runs have the same Lean return value, regardless of their machine inputs. -/
theorem execute_ret_independent (p : Prog (TMQuery tm) α) (s t : TMState tm)
    {fuel fuel' : Nat} {result result' : AddWriter TMCost α}
    {final final' : ExecutionState tm}
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret := by
  grind

end TMQuery


end Algorithms

end Algolean
