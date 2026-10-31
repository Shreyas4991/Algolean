/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component

/-!
# Relabeling finite control states

An injective relabeling embeds a component's finite control alphabet into another one.
It changes no tape operation, interpreter budget, head position, or storage cost.
In particular, disjoint injections can give independently defined components fresh labels.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {source target : SingleTapeTM Symbol}

/-- Relabel only finite control; retain the tape, allocated storage, and all head visits. -/
@[simps]
def TMState.relabel (f : source.State → target.State) (s : TMState source) : TMState target where
  config := ⟨s.config.state.map f, s.config.BiTape⟩
  headPos := s.headPos
  cellsAllocated := s.cellsAllocated
  cellsVisited := s.cellsVisited

/-- Relabel the fixed state labels appearing in a condition. -/
@[simp] def TMCondition.relabel (f : source.State → target.State) :
    TMCondition source → TMCondition target
  | .tapeIs symbol => .tapeIs symbol
  | .stateIs label => .stateIs (label.map f)
  | .not condition => .not (condition.relabel f)

/-- Relabel every state constant, including constants inside branch and loop bodies. -/
def TMQuery.relabel (f : source.State → target.State) : TMQuery source α → TMQuery target α
  | .write symbol => .write symbol
  | .move direction => .move direction
  | .update label => .update (f label)
  | .branchCode condition yes no =>
    .branchCode (condition.relabel f) (yes.map (relabel f)) (no.map (relabel f))
  | .whileCode condition body => .whileCode (condition.relabel f) (body.map (relabel f))

namespace TMQuery

/-- Relabel an existing program without consulting its input. -/
def relabelProg (f : source.State → target.State) (p : Prog (TMQuery source) Unit) :
    Prog (TMQuery target) Unit := p.liftM (fun q => FreeM.lift (q.relabel f))

@[simp] theorem instructions_relabelProg (f : source.State → target.State)
    (p : Prog (TMQuery source) Unit) :
    instructions (relabelProg f p) = (instructions p).map (relabel f) := by
  induction p with
  | pure a => cases a; rfl
  | liftBind q next ih => cases q <;> simp_all [relabelProg, FreeM.liftM, instructions, relabel]

variable [DecidableEq Symbol] [DecidableEq source.State] [DecidableEq target.State]

@[simp] theorem eval_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (condition : TMCondition source) (s : TMState source) :
    (condition.relabel f).eval (s.relabel f).config = condition.eval s.config := by
  induction condition with
  | tapeIs symbol => rfl
  | stateIs label => simp [TMState.relabel, (Option.map_injective hf).eq_iff]
  | not condition ih => simpa using congrArg Bool.not ih

/-- Relabel a pending interpreter step, retaining its exact cost. -/
@[simps] def Step.relabel (f : source.State → target.State) (next : Step source) : Step target :=
  ⟨next.cost, next.machine.relabel f, next.code.map (TMQuery.relabel f)⟩

theorem step_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (q : TMQuery source Unit) (rest : List (TMQuery source Unit)) (s : TMState source) :
    step (q.relabel f) (rest.map (relabel f)) (s.relabel f) = (step q rest s).relabel f := by
  cases q with
  | move direction =>
    cases direction <;> simp [relabel, step, Step.relabel, TMState.relabel] <;>
      split <;> simp_all
  | branchCode condition yes no =>
    cases h : condition.eval s.config <;>
      simp [relabel, step, Step.relabel, eval_relabel f hf, h]
  | whileCode condition body =>
    cases h : condition.eval s.config <;>
      simp [relabel, step, Step.relabel, eval_relabel f hf, h]
  | _ => simp [relabel, step, Step.relabel, TMState.relabel]

theorem runCode_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (fuel : ℕ) (code : List (TMQuery source Unit)) (s : TMState source) :
    runCode fuel (code.map (relabel f)) (s.relabel f) =
      (runCode fuel code s).map (fun (result, final) =>
        (result, ⟨final.machine.relabel f, final.fuel⟩)) := by
  induction fuel generalizing code s with
  | zero => cases code <;> rfl
  | succ fuel ih =>
    simp only [runCode] at ih
    cases code with
    | nil => rfl
    | cons q rest =>
      simp only [List.map_cons, runCode, runCodeWith, step_relabel f hf, Step.relabel_machine,
        Step.relabel_code, Step.relabel_cost, ih]
      cases runCodeWith step fuel (step q rest s).code (step q rest s).machine <;> rfl

/-- State relabeling preserves complete execution, including exact time and additional space. -/
theorem Completes.relabel {p : Prog (TMQuery source) Unit} {s t : TMState source} {cost : TMCost}
    (h : Completes p s cost t) (f : source.State → target.State) (hf : Function.Injective f) :
    Completes (relabelProg f p) (s.relabel f) cost (t.relabel f) := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel, ?_⟩
  rw [execute_eq_runCode, instructions_relabelProg, runCode_relabel f hf]
  rw [execute_eq_runCode] at h
  simp [h]

end TMQuery

namespace Component

variable [DecidableEq Symbol] [DecidableEq source.State] [DecidableEq target.State]

/-- Transport a component contract into an injectively relabeled control alphabet. -/
@[simps program]
def relabel {ι : Type} {pre : ι → TMState source → Prop}
    {post : ι → TMState source → TMCost → TMState source → Prop}
    (machine : Component source pre post) (f : source.State → target.State)
    (hf : Function.Injective f) :
    Component target (fun i s => ∃ original, pre i original ∧ s = original.relabel f)
      (fun i s cost final => ∃ original result,
        s = original.relabel f ∧ final = result.relabel f ∧ post i original cost result) where
  program := TMQuery.relabelProg f machine.program
  correct i s hs := by
    obtain ⟨original, hp, rfl⟩ := hs
    obtain ⟨cost, result, hc, hpost⟩ := machine.correct i original hp
    exact ⟨cost, result.relabel f, hc.relabel f hf, original, result, rfl, rfl, hpost⟩

end Component

end Algolean.Algorithms
