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

## Main definitions and results

* `TMState.relabel`, `TMCondition.relabel`, and `TMQuery.relabel` map finite control labels.
* `TMQuery.relabelReduction` supplies the query translation used by `Prog.reduceProg`.
* `TMQuery.Completes.relabel` preserves exact completion and execution costs.
* `Component.relabel` relabels a component and proves that its correctness specification
  still holds.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {source target : SingleTapeTM Symbol}

/-- Relabel only finite control; retain the tape, its range, and all head visits. -/
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

/-- Implement each source query with the corresponding relabeled target query.
Use `Prog.reduceProg` to apply this translation to an entire program. -/
def relabelReduction (f : source.State → target.State) :
    Reduction (TMQuery source) (TMQuery target) where
  reduce q := FreeM.lift (q.relabel f)

private theorem relabel_forM (f : source.State → target.State)
    (body : List (TMQuery source Unit)) :
    FreeM.liftM (m := Prog (TMQuery target))
      (fun {α} (q : TMQuery source α) => FreeM.lift (q.relabel f))
      (forM body (fun q => FreeM.lift q)) =
      forM body (fun q => FreeM.lift (q.relabel f)) := by
  induction body with
  | nil => rfl
  | cons q rest ih => simp only [List.forM_cons, FreeM.liftM_bind, FreeM.liftM_lift, ih]

variable [DecidableEq Symbol] [DecidableEq source.State] [DecidableEq target.State]

@[simp] theorem eval_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (condition : TMCondition source) (s : TMState source) :
    (condition.relabel f).eval (s.relabel f).config = condition.eval s.config := by
  induction condition with
  | tapeIs symbol => rfl
  | stateIs label => simp [TMState.relabel, (Option.map_injective hf).eq_iff]
  | not condition ih => simpa using congrArg Bool.not ih

/-- Relabel the remaining program and machine state without changing the step's cost. -/
@[simps] def relabelStep (f : source.State → target.State)
    (next : FuelExecMonad.Step (TMQuery source) (TMState source) TMCost α) :
    FuelExecMonad.Step (TMQuery target) (TMState target) TMCost α :=
  ⟨next.cost, next.machine.relabel f, next.program.reduceProg (relabelReduction f)⟩

theorem step_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (q : TMQuery source α) (next : α → Prog (TMQuery source) β) (s : TMState source) :
    step (q.relabel f) (fun a => Prog.reduceProg (next a) (relabelReduction f)) (s.relabel f) =
      relabelStep f (step q next s) := by
  cases q with
  | move direction =>
    cases direction <;> simp [relabel, step, relabelStep, TMState.relabel] <;>
      split <;> simp_all
  | branchCode condition yes no =>
    cases h : condition.eval s.config <;>
      simp [relabel, step, relabelStep, eval_relabel f hf, h,
        Prog.reduceProg, relabelReduction, FreeM.liftM_bind, relabel_forM]
  | whileCode condition body =>
    cases h : condition.eval s.config <;>
      simp [relabel, step, relabelStep, eval_relabel f hf, h,
        Prog.reduceProg, relabelReduction, FreeM.liftM_bind, relabel_forM]
  | _ => simp [relabel, step, relabelStep, TMState.relabel]

/-- Relabeling preserves program execution, including the exact cost and remaining fuel. -/
theorem execute_relabel (f : source.State → target.State) (hf : Function.Injective f)
    (fuel : ℕ) (p : Prog (TMQuery source) α) (s : TMState source) :
    execute fuel (p.reduceProg (relabelReduction f)) (s.relabel f) =
      (execute fuel p s).map (fun (result, final) =>
        (result, ⟨final.machine.relabel f, final.fuel⟩)) := by
  induction fuel generalizing p s with
  | zero =>
    cases p with
    | pure a => simp [Prog.reduceProg, relabelReduction]
    | liftBind q next =>
      change execute 0 (.liftBind (q.relabel f)
        (fun a => Prog.reduceProg (next a) (relabelReduction f))) _ = _
      simp only [FuelExecMonad.execute_zero_liftBind, Option.map_none]
  | succ fuel ih =>
    cases p with
    | pure a => simp [Prog.reduceProg, relabelReduction]
    | liftBind q next =>
      change execute (fuel + 1) (.liftBind (q.relabel f)
        (fun a => Prog.reduceProg (next a) (relabelReduction f))) _ = _
      simp only [FuelExecMonad.execute_liftBind_succ, step_relabel f hf, relabelStep_machine,
        relabelStep_program, relabelStep_cost, ih]
      simp only [execute, TMModel]
      cases FuelExecMonad.execute (interpreter source).toModel fuel
        (step q next s).program (step q next s).machine <;> rfl

/-- State relabeling preserves complete execution, including exact time and additional space. -/
theorem Completes.relabel {p : Prog (TMQuery source) Unit} {s t : TMState source} {cost : TMCost}
    (h : Completes p s cost t) (f : source.State → target.State) (hf : Function.Injective f) :
    Completes (p.reduceProg (relabelReduction f)) (s.relabel f) cost (t.relabel f) := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel, ?_⟩
  rw [execute_relabel f hf]
  simp [h]

end TMQuery

namespace Component

variable [DecidableEq Symbol] [DecidableEq source.State] [DecidableEq target.State]

/-- Relabel a component's control states using an injective map and prove that it still satisfies
its specification. -/
@[simps program]
def relabel {ι : Type} {pre : ι → TMState source → Prop}
    {post : ι → TMState source → TMCost → TMState source → Prop}
    (machine : Component source pre post) (f : source.State → target.State)
    (hf : Function.Injective f) :
    Component target (fun i s => ∃ original, pre i original ∧ s = original.relabel f)
      (fun i s cost final => ∃ original result,
        s = original.relabel f ∧ final = result.relabel f ∧ post i original cost result) where
  program := machine.program.reduceProg (TMQuery.relabelReduction f)
  correct i s hs := by
    obtain ⟨original, hp, rfl⟩ := hs
    obtain ⟨cost, result, hc, hpost⟩ := machine.correct i original hp
    exact ⟨cost, result.relabel f, hc.relabel f hf, original, result, rfl, rfl, hpost⟩

end Component

end Algolean.Algorithms
