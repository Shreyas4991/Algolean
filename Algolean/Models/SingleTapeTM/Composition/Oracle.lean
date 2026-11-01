/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component
public import Algolean.Models.SingleTapeTMSyntax

/-!
# How a machine asks another problem a question

A Turing reduction uses an assumed solver for another yes/no problem. The usual name for this
solver is an *oracle*. This file describes how a machine asks that solver questions.

`OracleInterface` chooses three different state names: request, yes, and no. Setting the request
state asks about the Boolean word starting at the tape head and ending at the first blank.
The interpreter records the answer by setting the machine's state to yes or no. The tape,
head position, allocated storage, and record of head visits stay unchanged.

The program can test this answer state and choose its next action. Questions can occur inside
branches and loops, so the number of questions and their contents may depend on earlier answers.
All of this uses the existing `TMQuery` instructions.

Each head-move instruction and each question costs one time step. The assumed solver's own
work is outside this count. As with ordinary execution, every instruction and loop test also
uses the separate interpreter limit called `fuel`; running out of it returns `none`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing TMQuery

/-- The three different state names used to ask a solver a question and record its answer. -/
structure OracleInterface (tm : SingleTapeTM Bool) where
  /-- Setting this state asks the solver about the word under the tape head. -/
  request : tm.State
  /-- After the solver answers yes, the interpreter uses this state. -/
  yes : tm.State
  /-- After the solver answers no, the interpreter uses this state. -/
  no : tm.State
  /-- The request and yes states must be different. -/
  request_ne_yes : request ≠ yes
  /-- The request and no states must be different. -/
  request_ne_no : request ≠ no
  /-- The yes and no states must be different so the program can tell the answers apart. -/
  yes_ne_no : yes ≠ no

namespace OracleInterface

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Read the word to ask about: start at the tape head and stop at the first blank. -/
def queryWord (contents : BiTape Bool) : List Bool :=
  match contents.head with
  | none => []
  | some bit => bit :: (contents.right.toList.takeWhile Option.isSome).filterMap id

@[simp] theorem queryWord_mk₁ (input : List Bool) : queryWord (BiTape.mk₁ input) = input := by
  have h (bits : List Bool) :
      ((bits.map some).takeWhile Option.isSome).filterMap id = bits := by
    induction bits <;> simp_all
  cases input with
  | nil => rfl
  | cons bit bits => exact congrArg (List.cons bit) (h bits)

open scoped TMQuery

/-- Ask the solver a question. Its answer is kept in the machine's state. -/
def ask (interface : OracleInterface tm) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ interface.request

/-- Run one instruction, asking the solver if it sets the request state.
All other instructions behave as they do in ordinary machine execution. -/
def step (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) (s : TMState tm) : Step tm :=
  match q with
  | .update label =>
    if label = interface.request then
      let answer := if oracle (queryWord s.config.BiTape) then interface.yes else interface.no
      ⟨⟨1, 0⟩, {s with config.state := some answer}, rest⟩
    else TMQuery.step q rest s
  | _ => TMQuery.step q rest s

@[simp] theorem step_append (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (q : TMQuery tm Unit) (rest tail : List (TMQuery tm Unit)) (s : TMState tm) :
    interface.step oracle q (rest ++ tail) s =
      { interface.step oracle q rest s with
        code := (interface.step oracle q rest s).code ++ tail } := by
  cases q <;> simp [step]
  split <;> rfl

/-- Run a list of instructions using the shared interpreter and instruction limit. -/
def runBlock (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (code : List (TMQuery tm Unit)) : AddWriterT TMCost (ExecutionM tm) Unit :=
  AddWriterT.mk fun s => runCodeWith (interface.step oracle) s.fuel code s.machine

/-- The interpreter used when a machine can ask the given solver questions. -/
def model (interface : OracleInterface tm) (oracle : List Bool → Bool) :
    ModelStateM (TMQuery tm) (ExecutionM tm) TMCost where
  runQuery q := (result_type q).symm ▸ interface.runBlock oracle [result_type q ▸ q]

theorem model_runQuery (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (q : TMQuery tm Unit) :
    (interface.model oracle).runQuery q = interface.runBlock oracle [q] := rfl

@[simp] theorem runBlock_nil (interface : OracleInterface tm) (oracle : List Bool → Bool) :
    interface.runBlock oracle [] = (pure () : AddWriterT TMCost (ExecutionM tm) Unit) := by
  apply AddWriterT.ext
  funext s
  simp only [runBlock, AddWriterT.run_mk, AddWriterT.run_pure]
  simp only [runCodeWith]
  rfl

private theorem unit_ret (a : AddWriter TMCost Unit) : a.ret = () := Subsingleton.elim _ _

@[simp] theorem runBlock_cons (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) :
    interface.runBlock oracle (q :: rest) =
      ((interface.model oracle).runQuery q >>= fun _ => interface.runBlock oracle rest) := by
  apply AddWriterT.ext
  funext s
  simpa only [model_runQuery, run_bind_execution, runBlock, AddWriterT.run_mk,
    unit_ret, List.singleton_append] using
    runCodeWith_append (interface.step oracle) (interface.step_append oracle)
      s.fuel [q] rest s.machine

@[simp] theorem runBlock_instructions (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (p : Prog (TMQuery tm) Unit) :
    interface.runBlock oracle (instructions p) = p.runStateM (interface.model oracle) := by
  induction p with
  | pure a => cases a; simp
  | liftBind q next ih => cases q <;> simp_all [Prog.runStateM, FreeM.liftM]

/-- Run a fixed program with the given solver, starting state, and instruction limit. -/
def execute (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (s : TMState tm) :=
  (p.runStateM (interface.model oracle)).run ⟨s, fuel⟩

theorem execute_eq_runCode (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (s : TMState tm) :
    interface.execute oracle fuel p s =
      runCodeWith (interface.step oracle) fuel (instructions p) s := by
  simp [execute, ← runBlock_instructions, runBlock]

/-- Asking a question costs one time step and one unit of the instruction limit.
The tape and head position stay unchanged. -/
@[simp] theorem execute_ask_succ (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (fuel : ℕ) (s : TMState tm) :
    interface.execute oracle (fuel + 1) interface.ask s =
      let answer := if oracle (queryWord s.config.BiTape) then interface.yes else interface.no
      some (⟨(), ⟨1, 0⟩⟩, ⟨{s with config.state := some answer}, fuel⟩) := by
  simp [execute_eq_runCode, ask, step]

theorem step_cellsAllocated (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) (s : TMState tm) :
    s.cellsAllocated.card + (interface.step oracle q rest s).cost.cellsAllocated =
      (interface.step oracle q rest s).machine.cellsAllocated.card := by
  cases q with
  | update label => simp only [step]; split <;> simp_all [TMQuery.step]
  | _ => simpa only [step] using TMQuery.step_cellsAllocated _ rest s

/-- Previously allocated cells still count. The total after the run equals the previous total
plus the number of new cells allocated during this run. -/
theorem execute_cellsAllocated (interface : OracleInterface tm) (oracle : List Bool → Bool)
    (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : interface.execute oracle fuel p s = some (result, final)) :
    s.cellsAllocated.card + result.tell.cellsAllocated = final.machine.cellsAllocated.card := by
  rw [execute_eq_runCode] at h
  generalize instructions p = code at h
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCodeWith]
  | succ fuel ih =>
    cases code with
    | nil => grind [runCodeWith]
    | cons q rest =>
      cases hr : runCodeWith (interface.step oracle) fuel
          (interface.step oracle q rest s).code (interface.step oracle q rest s).machine <;>
        simp_all
      have := interface.step_cellsAllocated oracle q rest s
      grind

end OracleInterface

end Algolean.Algorithms
