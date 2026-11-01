/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.FuelExecMonad
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic
public import Mathlib.Data.Int.Interval

/-!
# Deeply embedded single-tape TM programs

A TM algorithm is a fixed program run on a single tape turing machine,
independent of its input and input length to keep the Program uniform.
The input is supplied through the initial machine state, not the Prog.
The output is observed through the final configuration.
Tape symbols and control states remain inside the model. Every query returns `Unit`.

Each instruction, branch selection, and loop test consumes interpreter fuel.
Exhaustion returns `none`, including for an empty infinite loop.
Fuel is external to the program and separate from the machine's time and space costs. Successful
runs of a fixed program cannot reveal machine data through their Lean return values.

Space complexity is counted as the range of cells visited by the tape head
together with the cells holding the initial input, following the ordinary-machine case of
Papadimitriou [§2.5, Definition 2.6, p. 35][papadimitriou1994].



## References

* [Christos H. Papadimitriou, *Computational Complexity*, Addison-Wesley, Reading, MA,
  1994, §2.5, Definition 2.6, p. 35. ISBN 0-201-53082-1.][papadimitriou1994]

[papadimitriou1994]: https://www2.eecs.berkeley.edu/Pubs/Faculty/papadimitriou.html

## Main definitions and results

* `TMQuery tm` describes tape writes, control-state updates, head moves, branches, and loops.
* `TMCondition` is syntax for testing tape symbols and control states inside the interpreter.
* `TMQuery.branch` and `TMQuery.whileLoop` accept `Prog` bodies. Their internal storage uses
  instruction lists.
* `TMState.cellsAllocated` retains every initially stored or subsequently reached cell;
  its cardinality gives total space. `TMCost.cellsAllocated` counts cells added to this range.
* `TMState.cellsVisited` records cells actually visited by the head, separately from space usage.
* `TMQuery.execute fuel program state` runs a program through `TMModel`, which uses
  `FuelExecMonad (TMState tm)`.
* `TMQuery.execute_ret_independent` proves that successful runs of a fixed program cannot
  reveal machine data through their Lean return values.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

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

/-- The configuration, tape range, and head visits of a single-tape query execution. -/
@[ext, grind]
structure TMState (tm : SingleTapeTM Symbol) where
  /-- The current machine configuration. -/
  config : tm.Cfg
  /-- Head position relative to its initial cell, with negative positions to the left. -/
  headPos : ℤ := 0
  /-- The range of cells visited by the tape head together with the initially stored tape. -/
  cellsAllocated : Finset ℤ := Finset.Icc
    (headPos - config.BiTape.left.length) (headPos + config.BiTape.right.length)
  /-- Distinct positions actually visited by the head, independent of unvisited input cells. -/
  cellsVisited : Finset ℤ := {headPos}

/-- Initialize the machine on an input, with its head at position zero. -/
@[simps]
def TMState.init (tm : SingleTapeTM Symbol) (input : List Symbol) : TMState tm where
  config := tm.initCfg input

/-- Total storage includes the range of cells visited by the tape head and the whole input. -/
def TMState.spaceUsed {tm : SingleTapeTM Symbol} (s : TMState tm) : ℕ :=
  s.cellsAllocated.card

/-- Input storage is charged before the program executes any instruction. -/
@[simp] theorem TMState.spaceUsed_init (tm : SingleTapeTM Symbol) (input : List Symbol) :
    (TMState.init tm input).spaceUsed = max 1 input.length := by
  cases input <;> simp [TMState.init, SingleTapeTM.initCfg, BiTape.mk₁, BiTape.nil,
    TMState.spaceUsed, StackTape.length_nil, StackTape.length_mapSome, Int.card_Icc]

/-- The recorded tape range is a single finite interval containing the head. -/
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
  /-- Number of cells added to the tape range beyond the initial state's stored tape. -/
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

-- Only structured control stores bodies as lists. Programs and their execution use `Prog`.
namespace Internal

/-- Store a fixed program as the body of a structured control instruction. -/
def instructions : Prog (TMQuery tm) Unit → List (TMQuery tm Unit)
  | .pure _ => []
  | .liftBind q next =>
    (result_type q ▸ q) :: instructions (next ((result_type q).symm ▸ ()))

private theorem forM_instructions (p : Prog (TMQuery tm) Unit) :
    (instructions p).forM (fun q => FreeM.lift q) = p := by
  induction p with
  | pure a => cases a; rfl
  | liftBind q next ih =>
    cases q <;> simp_all only [instructions, List.forM_eq_forM, List.forM_cons]
    all_goals rw [FreeM.liftBind_eq]; congr 1

end Internal

open Internal

/-- Host-language return values are fixed by syntax; queries return only `Unit`. -/
def returnValue : Prog (TMQuery tm) α → α
  | .pure a => a
  | .liftBind q next => returnValue (next ((result_type q).symm ▸ ()))

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

/-- TM machine state paired with its remaining interpreter fuel. -/
abbrev ExecutionState (tm : SingleTapeTM Symbol) := FuelExecState (TMState tm)

/-- Fuel exhaustion fails the whole execution rather than returning a partial result. -/
abbrev ExecutionM (tm : SingleTapeTM Symbol) := FuelExecMonad (TMState tm)

variable [DecidableEq Symbol] [DecidableEq tm.State]

/-- Execute one query and continue with its `Prog` continuation. -/
def step (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    FuelExecMonad.Step (TMQuery tm) (TMState tm) TMCost β :=
  match q with
  | .write symbol => ⟨0, {s with config.BiTape := s.config.BiTape.write symbol}, next ()⟩
  | .update st => ⟨0, {s with config.state := some st}, next ()⟩
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
        cellsVisited := insert pos s.cellsVisited}, next ()⟩
  | .branchCode condition yes no =>
    ⟨0, s, (if condition.eval s.config then yes else no).forM (fun q => FreeM.lift q) >>= next⟩
  | .whileCode condition body =>
    ⟨0, s, if condition.eval s.config then do
      body.forM (fun q => FreeM.lift q)
      FreeM.lift (.whileCode condition body) >>= next
    else next ()⟩

end TMQuery

/-- The TM's primitive instructions and structured control define its small-step semantics. -/
abbrev TMQuery.interpreter (tm : SingleTapeTM Symbol)
    [DecidableEq Symbol] [DecidableEq tm.State] :
    FuelExecMonad.Interpreter (TMQuery tm) (TMState tm) TMCost where
  step := TMQuery.step
  step_bind := by
    intro α β γ q next cont s
    cases q <;> simp [TMQuery.step, bind_assoc]
    split <;> simp

/-- Stateful execution and costs for deeply embedded single-tape programs. -/
abbrev TMModel (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State] :
    ModelStateM (TMQuery tm) (TMQuery.ExecutionM tm) TMCost :=
  (TMQuery.interpreter tm).toModel

namespace TMQuery

open Internal

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Execute a fixed program on a separately supplied input state. -/
abbrev execute (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm) :
    Option (AddWriter TMCost α × ExecutionState tm) :=
  FuelExecMonad.execute (TMModel tm) fuel p s

/-- Branch selection consumes one unit of fuel and executes only the selected body. -/
@[simp, grind =] theorem execute_branch_succ (fuel : ℕ) (condition : TMCondition tm)
    (yes no : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute (fuel + 1) (branch condition yes no) s =
      if condition.eval s.config then execute fuel yes s else execute fuel no s := by
  change FuelExecMonad.execute (interpreter tm).toModel (fuel + 1)
    (.liftBind (.branchCode condition (instructions yes)
    (instructions no)) pure) s = _
  rw [FuelExecMonad.execute_liftBind_succ (I := interpreter tm) fuel
    (.branchCode condition (instructions yes) (instructions no)) pure s]
  simp only [step]
  split
  · simp only [forM_instructions, bind_pure, zero_add]
    change (execute fuel yes s).bind some = _
    simp
  · simp only [forM_instructions, bind_pure, zero_add]
    change (execute fuel no s).bind some = _
    simp

@[simp, grind =] theorem execute_while_zero (condition : TMCondition tm)
    (body : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute 0 (whileLoop condition body) s = none := by
  simp only [whileLoop, FreeM.lift, FuelExecMonad.execute_zero_liftBind]

/-- Each loop test consumes fuel; the body determines the machine cost and state. -/
@[grind =] theorem execute_while_succ (fuel : ℕ) (condition : TMCondition tm)
    (body : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute (fuel + 1) (whileLoop condition body) s =
      if condition.eval s.config then execute fuel (do body; whileLoop condition body) s
      else some (⟨(), 0⟩, ⟨s, fuel⟩) := by
  change FuelExecMonad.execute (interpreter tm).toModel (fuel + 1)
    (.liftBind (.whileCode condition (instructions body)) pure) s = _
  rw [FuelExecMonad.execute_liftBind_succ (I := interpreter tm) fuel
    (.whileCode condition (instructions body)) pure s]
  simp only [step, forM_instructions]
  split
  · simp only [bind_pure, zero_add]
    change (execute fuel (do body; whileLoop condition body) s).bind some = _
    simp
  · simp

private theorem insert_Icc_adjacent {lo hi pos : ℤ}
    (hlo : lo - 1 ≤ pos) (hhi : pos ≤ hi + 1) :
    insert pos (Finset.Icc lo hi) = Finset.Icc (min lo pos) (max hi pos) := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_Icc, min_le_iff, le_max_iff]
  lia

/-- A head move can extend either end of the stored tape but cannot create a gap. -/
theorem step_allocatedInterval (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β)
    (s : TMState tm) (h : s.AllocatedInterval) : (step q next s).machine.AllocatedInterval := by
  obtain ⟨lo, hi, hs, hlo, hhi⟩ := h
  cases q with
  | move dir =>
    cases dir <;>
      refine ⟨min lo _, max hi _, ?_, min_le_right _ _, le_max_right _ _⟩ <;>
      simpa [step, hs] using insert_Icc_adjacent (lo := lo) (hi := hi) (by lia) (by lia)
  | _ => exact ⟨lo, hi, hs, hlo, hhi⟩

/-- A step's space charge is exactly the number of cells added to the tape range. -/
@[grind ←] theorem step_cellsAllocated (q : TMQuery tm α)
    (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    s.cellsAllocated.card + (step q next s).cost.cellsAllocated =
      (step q next s).machine.cellsAllocated.card := by
  cases q with
  | move dir => cases dir <;> grind [step]
  | _ => simp [step]

/-- Total storage is the initial tape range plus the accumulated space cost. -/
@[grind →] theorem execute_cellsAllocated (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) :
    s.cellsAllocated.card + result.tell.cellsAllocated = final.machine.cellsAllocated.card := by
  induction fuel generalizing p s result final with
  | zero =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next => simp only [FuelExecMonad.execute_zero_liftBind] at h; cases h
  | succ fuel ih =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next =>
      simp only [FuelExecMonad.execute_liftBind_succ] at h
      cases hr : execute fuel (step q next s).program (step q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        have hu := ih _ _ _ _ hr
        have hs := step_cellsAllocated q next s
        simp only [TMCost.add_cellsAllocated]
        omega

/-- A completed program retains a single tape range, even after erasure. -/
theorem execute_preserves_allocatedInterval (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) (hs : s.AllocatedInterval) :
    final.machine.AllocatedInterval := by
  induction fuel generalizing p s result final with
  | zero =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs
    | liftBind q next => simp only [FuelExecMonad.execute_zero_liftBind] at h; cases h
  | succ fuel ih =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hs
    | liftBind q next =>
      simp only [FuelExecMonad.execute_liftBind_succ] at h
      cases hr : execute fuel (step q next s).program (step q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ih _ _ _ _ hr (step_allocatedInterval q next s hs)

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
    final.machine.AllocatedInterval :=
  execute_preserves_allocatedInterval fuel p _ result final h
    (TMState.allocatedInterval_init tm input)

/-- Completed execution cannot reveal a tape symbol or control state through a Lean result. -/
@[grind →] theorem execute_ret (p : Prog (TMQuery tm) α) (s : TMState tm) (fuel : ℕ)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) : result.ret = returnValue p := by
  have hr := h
  rw [eq_bind_return p] at hr
  simp only [FuelExecMonad.execute_bind, h, FuelExecMonad.execute_pure, Option.pure_def] at hr
  grind

/-- Two successful runs have the same Lean return value, regardless of their machine inputs. -/
theorem execute_ret_independent (p : Prog (TMQuery tm) α) (s t : TMState tm)
    {fuel fuel' : ℕ} {result result' : AddWriter TMCost α}
    {final final' : ExecutionState tm}
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret := by
  grind

end TMQuery
end Algorithms
end Algolean
