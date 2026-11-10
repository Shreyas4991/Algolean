/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Asking an assumed solver questions

This file lets a tape program ask an assumed solver for answers to a yes/no problem. Such a
solver is called an oracle. The program asks about the word under the tape head, ending at the
first blank. The query word and the reduction machine use the same fixed finite alphabet;
only the oracle's answer is Boolean. Its answer is recorded in the machine state, so later
branches and loops can depend on it.

A request costs one time step and leaves the tape and head unchanged. Head moves also cost one
time step. Every instruction and loop test uses fuel. The solver's own work is outside this
count.

## Main definitions and results

* [OracleInterface](##Algolean.Algorithms.OracleInterface) chooses distinct states for requests,
  yes answers, and no answers.
* [queryWord](##Algolean.Algorithms.OracleInterface.queryWord) reads the word being asked about.
* [ask](##Algolean.Algorithms.OracleInterface.ask) issues a request.
* [interpreter](##Algolean.Algorithms.OracleInterface.interpreter) supplies the rules for
  executing requests to the [shared
  runner](##Algolean.Algorithms.FuelExecMonad.Interpreter.run).
* [execute_ask_succ](##Algolean.Algorithms.OracleInterface.execute_ask_succ) describes the
  answer and cost of a request.
* [execute_cellsAllocated](##Algolean.Algorithms.OracleInterface.execute_cellsAllocated) counts
  the cells added to the recorded tape range during execution.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
This interface chooses three distinct machine states for issuing a request and recording a yes
or no answer.
-/
structure OracleInterface (tm : SingleTapeTM Symbol) where
  /--
  Setting this state with an update instruction asks the solver about the word under the head.
  -/
  request : tm.State
  /-- The interpreter sets this state when the solver answers yes. -/
  yes : tm.State
  /-- The interpreter sets this state when the solver answers no. -/
  no : tm.State
  /-- The request state differs from the yes state. -/
  request_ne_yes : request ≠ yes
  /-- The request state differs from the no state. -/
  request_ne_no : request ≠ no
  /-- The yes and no states differ, so the program can distinguish the answers. -/
  yes_ne_no : yes ≠ no

namespace OracleInterface

/-- The question is the word starting under the head and ending before the first blank. -/
def queryWord (contents : BiTape Symbol) : List Symbol :=
  match contents.head with
  | none => []
  | some symbol => symbol :: (contents.right.toList.takeWhile Option.isSome).filterMap id

omit [Inhabited Symbol] [Fintype Symbol] in
/-- Reading a word placed on the initial tape gives back exactly that word. -/
@[simp] theorem queryWord_mk₁ (input : List Symbol) : queryWord (BiTape.mk₁ input) = input := by
  have h (word : List Symbol) :
      ((word.map some).takeWhile Option.isSome).filterMap id = word := by
    induction word <;> simp_all
  cases input with
  | nil => rfl
  | cons symbol rest => exact congrArg (List.cons symbol) (h rest)

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

open scoped TMQuery

/-- This program issues a request and leaves the answer in the machine state. -/
def ask (interface : OracleInterface tm) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ interface.request

/--
One instruction follows the [ordinary rules](##Algolean.Algorithms.TMQuery.step), except that
setting the request state obtains an answer from the solver.
-/
def step (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    FuelExecMonad.Step (TMQuery tm) (TMState tm) TMCost β :=
  match q with
  | .update label =>
    if label = interface.request then
      let answer := if oracle (queryWord s.config.BiTape) then interface.yes else interface.no
      ⟨⟨1, 0⟩, {s with config.state := some answer}, next ()⟩
    else TMQuery.step (.update label) next s
  | .write symbol => TMQuery.step (.write symbol) next s
  | .move direction => TMQuery.step (.move direction) next s
  | .branchCode condition yes no => TMQuery.step (.branchCode condition yes no) next s
  | .whileCode condition body => TMQuery.step (.whileCode condition body) next s

/--
These execution rules use the [shared
runner](##Algolean.Algorithms.FuelExecMonad.Interpreter.run) to handle fuel, program sequencing,
and costs. Requests work inside branches and loops.
-/
abbrev interpreter (interface : OracleInterface tm) (oracle : List Symbol → Bool) :
    FuelExecMonad.Interpreter (TMQuery tm) (TMState tm) TMCost where
  step := interface.step oracle
  step_bind := by
    intro α β γ q next cont s
    cases q <;> simp [step, TMQuery.step, bind_assoc]
    all_goals split <;> simp

/-- This model records the results and costs of executing programs with access to the solver. -/
abbrev model (interface : OracleInterface tm) (oracle : List Symbol → Bool) :
    ModelStateM (TMQuery tm) (ExecutionM tm) TMCost :=
  (interface.interpreter oracle).toModel

/--
The [shared execution function](##Algolean.Algorithms.FuelExecMonad.execute) runs the program
with the supplied solver, starting state, and fuel.
-/
abbrev execute (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm) :=
  FuelExecMonad.execute (interface.model oracle) fuel p s

/--
A request costs one time step and one unit of fuel. The answer is recorded in the machine state,
while the tape and head position stay unchanged.
-/
@[simp] theorem execute_ask_succ (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (fuel : ℕ) (s : TMState tm) :
    interface.execute oracle (fuel + 1) interface.ask s =
      let answer := if oracle (queryWord s.config.BiTape) then interface.yes else interface.no
      some (⟨(), ⟨1, 0⟩⟩, ⟨{s with config.state := some answer}, fuel⟩) := by
  change FuelExecMonad.execute (interface.interpreter oracle).toModel (fuel + 1)
    (.liftBind (.update interface.request) pure) s = _
  rw [FuelExecMonad.execute_liftBind_succ]
  simp [interpreter, step]

/-- One instruction counts exactly the cells it adds to the recorded tape range. -/
theorem step_cellsAllocated (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    s.cellsAllocated.card + (interface.step oracle q next s).cost.cellsAllocated =
      (interface.step oracle q next s).machine.cellsAllocated.card := by
  cases q with
  | update label => simp only [step]; split <;> simp_all [TMQuery.step]
  | _ => simpa only [step] using TMQuery.step_cellsAllocated _ next s

/--
The final number of recorded tape cells is the initial number plus the cells newly counted
during execution. Requests preserve this accounting.
-/
theorem execute_cellsAllocated (interface : OracleInterface tm) (oracle : List Symbol → Bool)
    (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : interface.execute oracle fuel p s = some (result, final)) :
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
      cases hr : interface.execute oracle fuel (interface.step oracle q next s).program
          (interface.step oracle q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        have hu := ih _ _ _ _ hr
        have hs := interface.step_cellsAllocated oracle q next s
        simp only [TMCost.add_cellsAllocated]
        lia

end OracleInterface

end Algolean.Algorithms
