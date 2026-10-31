/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTMSyntax
public import Std.Tactic.Do

/-!
# Deeply embedded single-tape TM examples

Programs are fixed across inputs. Branches and loops inspect tape and control state inside the
model; all output observations below happen after execution, through the final configuration.
Space includes blank and input cells, and retains its history across erasure and revisits.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMExamples

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery

open scoped TMQuery

/-- A finite alphabet and control-state type for the examples. -/
abbrev machine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

section Notation

-- A nested block supplies its own machine and control-state type.
example : instructions (do [TMQuery machine]
    let other := do [TMQuery (SingleTapeTM.idComputer (Symbol := Bool))]
      state ←ₜ ()
    let _ := other
    moveₜ .Stop) = [.move .Stop] := rfl

-- Primitive notation has generated unexpanders; control flow has explicit ones.
/-- info: fun symbol ↦ tape ←ₜ symbol : Option Bool → TMQuery machine Unit -/
#guard_msgs in
#check fun (symbol : Option Bool) => TMQuery.write (tm := machine) symbol

/-- info: fun label ↦ state ←ₜ label : machine.State → TMQuery machine Unit -/
#guard_msgs in
#check fun (label : machine.State) => TMQuery.update label

/-- info: fun direction ↦ moveₜ direction : Dir → TMQuery machine Unit -/
#guard_msgs in
#check fun (direction : Algolean.Algorithms.Dir) => TMQuery.move (tm := machine) direction

/--
info: fun condition yes no ↦ do
  ifₜ condition then
    yes
  else
    no : TMCondition machine → Prog (TMQuery machine) Unit → Prog (TMQuery machine) Unit → Prog (TMQuery machine) Unit
-/
#guard_msgs in
#check fun (condition : TMCondition machine) (yes no : Prog (TMQuery machine) Unit) =>
  TMQuery.branch condition yes no

/--
info: fun condition body ↦ do
  whileₜ condition do
    body : TMCondition machine → Prog (TMQuery machine) Unit → Prog (TMQuery machine) Unit
-/
#guard_msgs in
#check fun (condition : TMCondition machine) (body : Prog (TMQuery machine) Unit) =>
  TMQuery.whileLoop condition body

end Notation

attribute [local simp] execute_eq_runCode runCode step branch whileLoop
  TMState.init SingleTapeTM.initCfg BiTape.mk₁ BiTape.nil
  BiTape.moveLeft BiTape.moveRight BiTape.write
  StackTape.head StackTape.tail StackTape.mapSome StackTape.nil
  StackTape.length

-- The whole input is stored even when the program does nothing and visits only its first cell.
example (input : List Bool) :
    (execute 0 (do [TMQuery machine] pure ()) (TMState.init machine input)).map
      (fun (_, final) => (final.machine.spaceUsed, final.machine.cellsVisited.card)) =
      some (max 1 input.length, 1) := by
  simp only [execute_pure, Option.map_some, TMState.spaceUsed_init,
    TMState.init_cellsVisited, Finset.card_singleton]

/-- Both updates remain in the model, and the program returns only unit. -/
@[simp] def writeAndUpdate : Prog (TMQuery machine) Unit := do [TMQuery machine]
  tape ←ₜ some true
  state ←ₜ true

example : (execute 2 writeAndUpdate (TMState.init machine [])).map
    (fun r => (r.2.machine.config.BiTape.head, r.2.machine.config.state,
      r.1.tell.steps, r.1.tell.cellsAllocated)) = some (some true, some true, 0, 0) := by simp

/-- Visit both sides of the starting cell and return, without writing. -/
@[simp] def roundTrip : Prog (TMQuery machine) Unit := do [TMQuery machine]
  moveₜ .Left
  moveₜ .Right
  moveₜ .Right
  moveₜ .Left

-- Returning to cells does not count them again; blank cells still count.
example : (execute 4 roundTrip (TMState.init machine [])).map
    (fun r => (r.1.tell.steps, r.1.tell.cellsAllocated, r.2.machine.headPos,
      r.2.machine.cellsAllocated.card)) = some (4, 2, 0, 3) := by simp

-- Blank cells remain allocated even though the tape representation trims their contents.
example : (execute 4 roundTrip (TMState.init machine [])).map
    (fun (_, final) => (final.machine.config.BiTape.spaceUsed, final.machine.spaceUsed)) =
      some (1, 3) := by simp [BiTape.spaceUsed, TMState.spaceUsed, StackTape.cons]

example : (execute 4 roundTrip (TMState.init machine [])).map
    (fun r => r.2.machine.cellsAllocated) = some {-1, 0, 1} := by
  suffices ({1, -1, 0} : Finset ℤ) = {-1, 0, 1} by simpa using this
  ext
  simp [or_comm, or_left_comm, or_assoc]

-- Moving through already allocated input cells adds no storage.
example : (execute 4 roundTrip (TMState.init machine [true, false])).map
    (fun r => (r.1.tell.cellsAllocated, r.2.machine.config.BiTape.head)) =
      some (1, some true) := by simp

/-- Erase a cell, revisit it, and write again. Its space is charged only once. -/
@[simp] def eraseAndRevisit : Prog (TMQuery machine) Unit := do [TMQuery machine]
  moveₜ .Right
  tape ←ₜ some true
  tape ←ₜ none
  moveₜ .Left
  moveₜ .Right
  tape ←ₜ some false

example : (execute 6 eraseAndRevisit (TMState.init machine [])).map
    (fun r => (r.2.machine.config.BiTape.head, r.1.tell.cellsAllocated)) =
      some (some false, 1) := by simp

-- The shared budget applies across queries, and exhaustion discards partial execution.
example : execute 5 eraseAndRevisit (TMState.init machine []) = none := rfl

-- A second execution retains the allocated tape and charges no additional cells.
example : (do
    let (_, after) ← execute 4 roundTrip (TMState.init machine [])
    let (cost, _) ← execute 4 roundTrip after.machine
    pure cost.tell.cellsAllocated) = some 0 := by simp

/-- The same closed program scans any input length; the loop tests for blank inside the model. -/
@[simp] def scanRight : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Right
  state ←ₜ true

example : (execute 6 scanRight (TMState.init machine [true, false])).map
    (fun r => (r.2.machine.headPos, r.2.machine.config.state, r.1.tell.steps,
      r.1.tell.cellsAllocated, r.2.machine.cellsAllocated.card, r.2.fuel)) =
      some (2, some true, 2, 1, 3, 0) := by simp

example : execute 5 scanRight (TMState.init machine [true, false]) = none := rfl

example : (execute 4 scanRight (TMState.init machine [false])).map
    (fun r => (r.2.machine.headPos, r.1.tell.steps)) = some (1, 1) := by simp

example : (execute 2 scanRight (TMState.init machine [])).map
    (fun r => (r.2.machine.headPos, r.1.tell.cellsAllocated)) = some (0, 0) := by simp

-- Extra interpreter fuel leaves the resource cost and final configuration unchanged.
example : (execute 9 scanRight (TMState.init machine [true, false])).map
    (fun r => (r.2.machine.headPos, r.1.tell.steps, r.1.tell.cellsAllocated, r.2.fuel)) =
      some (2, 2, 1, 3) := by simp

/-- Nested control tests tape data and control state without returning either to Lean. -/
@[simp] def nested : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ tape =ₜ some true then
    whileₜ (state =ₜ some false) do
      state ←ₜ true
  else
    roundTrip
  moveₜ .Right

example : (execute 5 nested (TMState.init machine [true])).map
    (fun r => (r.2.machine.config.state, r.2.machine.headPos, r.1.tell.steps)) =
      some (some true, 1, 1) := by simp

example : execute 4 nested (TMState.init machine [true]) = none := rfl

example : (execute 6 nested (TMState.init machine [])).map
    (fun r => (r.2.machine.config.state, r.2.machine.headPos, r.1.tell.steps,
      r.2.machine.cellsAllocated.card)) = some (some false, 1, 5, 3) := by simp

/-- An empty loop whose condition remains true must consume all interpreter fuel. -/
@[simp] def forever : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some false) do
    pure ()

example (fuel : ℕ) : execute fuel forever (TMState.init machine []) = none := by
  simp only [execute_eq_runCode, forever, whileLoop, instructions_lift, instructions_pure]
  induction fuel <;> simp_all

-- An infinite unselected branch must not execute or consume fuel.
example : (execute 1
    (do [TMQuery machine]
      ifₜ tape =ₜ some true then
        pure ()
      else
        forever) (TMState.init machine [true])).map
    (fun r => (r.1.tell.steps, r.2.fuel)) = some (0, 0) := by simp

-- Stop counts one move but no new cells. A pure program needs no fuel.
example : (execute 1 (do [TMQuery machine] moveₜ .Stop) (TMState.init machine [])).map
    (fun r => (r.1.tell.steps, r.1.tell.cellsAllocated, r.2.machine.headPos)) =
      some (1, 0, 0) := by simp

example : execute 0 (do [TMQuery machine] pure ()) (TMState.init machine []) =
    some (⟨(), 0⟩, ⟨TMState.init machine [], 0⟩) := rfl

section WeakestPreconditions

open Cslib.FreeM Std.WP

/-- Interpret verification conditions through the TM model's joint state-and-cost handler. -/
local instance tmCostHandler : HasHandler (TMQuery machine)
    (TMCost → ExecutionState machine → Prop) (Unit → Prop) :=
  (TMModel machine).hasCostHandler

-- Verify both updates, their zero cost, and the shared fuel budget through the model's handler.
set_option experimental.vcgen true in
example :
    ⦃ fun cost s => cost = 0 ∧ s = ⟨TMState.init machine [], 2⟩ ⦄ writeAndUpdate
      ⦃ fun _ cost s => cost = 0 ∧ s.machine.config.BiTape.head = some true ∧
        s.machine.config.state = some true ∧ s.fuel = 0 ⦄ := by
  vcgen [writeAndUpdate]
  simp_all [HasHandler.handler, ModelStateM.costHandler, TMModel, runBlock]

-- The loop is machine-controlled; postconditions can still observe its exact time and space.
set_option experimental.vcgen true in
example (initial : TMCost) :
    ⦃ fun cost s => cost = initial ∧ s = ⟨TMState.init machine [true, false], 6⟩ ⦄ scanRight
      ⦃ fun _ cost s => s.machine.headPos = 2 ∧ s.machine.config.state = some true ∧
        cost.steps = initial.steps + 2 ∧ cost.cellsAllocated = initial.cellsAllocated + 1 ∧
        s.machine.cellsAllocated.card = 3 ∧ s.fuel = 0 ⦄ := by
  vcgen [scanRight, whileLoop]
  simp_all [HasHandler.handler, ModelStateM.costHandler, TMModel, runBlock]

end WeakestPreconditions

-- This holds for every program and every pair of successful executions, even with different fuel.
example (p : Prog (TMQuery machine) (List Bool)) (s t : TMState machine)
    (fuel fuel' : ℕ) (result result' : AddWriter TMCost (List Bool))
    (final final' : ExecutionState machine)
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret := by
  grind

end AlgoleanTests.SingleTapeTMExamples
