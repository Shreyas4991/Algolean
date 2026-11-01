/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.ModelStateM

/-!
# Fuelled execution with state and costs

An interpreter can keep its machine state and remaining fuel in a shared state monad.
Failure returns `none`, discarding the result, final state, and accumulated cost.
Each model determines which operations consume fuel; the monad does not decrement it
automatically. Interpreter fuel remains separate from the model's resource costs.

The state type, query language, and cost type are independent parameters. In particular,
the shared execution rules do not require queries to return `Unit`.

To construct an interpreter, describe the state, cost, and remaining program after one query.
Appending a continuation must leave that step's state and cost unchanged. The shared runner
then manages the fuel and supplies the proofs relating these steps to `ModelStateM` execution.

## Main definitions and results

* `FuelExecState σ` pairs a machine state with its remaining interpreter fuel.
* `FuelExecMonad σ` provides stateful execution with failure through `Option`.
* `FuelExecMonad.execute` runs a query program using a supplied `ModelStateM` interpreter.
* `FuelExecMonad.execute_pure` and `FuelExecMonad.execute_bind` describe program execution.
* `FuelExecMonad.Interpreter` supplies a machine's small-step semantics and constructs its model.
* `FuelExecMonad.execute_eq_run` relates the monadic interpreter to those semantics.
* `FuelExecMonad.execute_add_fuel` and `FuelExecMonad.execute_trim_fuel` change the supplied fuel
  without changing a completed computation.
-/

@[expose] public section

namespace Algolean.Algorithms

/-- Machine state paired with an external interpreter budget. -/
@[ext, grind]
structure FuelExecState (σ : Type u) where
  /-- The state interpreted by the model. -/
  machine : σ
  /-- Remaining interpreter steps. -/
  fuel : ℕ

/-- Stateful execution whose failure discards the whole result, including the final state. -/
abbrev FuelExecMonad (σ : Type u) := StateT (FuelExecState σ) Option

namespace FuelExecMonad

variable {σ α β Cost : Type u} {Q : Type u → Type v}

/-- Execute a program with the supplied model, initial machine state, and fuel budget. -/
def execute [AddZero Cost] (model : ModelStateM Q (FuelExecMonad σ) Cost)
    (fuel : ℕ) (program : Prog Q α) (machine : σ) :
    Option (AddWriter Cost α × FuelExecState σ) :=
  (program.runStateM model).run ⟨machine, fuel⟩

/-- A pure program consumes neither fuel nor resources. -/
@[simp, grind =] theorem execute_pure [AddZero Cost]
    (model : ModelStateM Q (FuelExecMonad σ) Cost) (fuel : ℕ) (a : α) (machine : σ) :
    execute model fuel (pure a) machine = some (⟨a, 0⟩, ⟨machine, fuel⟩) := rfl

/-- Program sequencing shares the remaining fuel and accumulates the execution costs. -/
@[simp, grind =] theorem execute_bind [AddMonoid Cost]
    (model : ModelStateM Q (FuelExecMonad σ) Cost) (fuel : ℕ)
    (program : Prog Q α) (next : α → Prog Q β) (machine : σ) :
    execute model fuel (program >>= next) machine = (do
      let (a, t) ← execute model fuel program machine
      let (b, u) ← execute model t.fuel (next a.ret) t.machine
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := by
  exact Prog.runStateM_bind_stateT model program next ⟨machine, fuel⟩



/-- The state, cost, and remaining program after one interpreter step. -/
@[ext, grind]
structure Step (Q : Type u → Type v) (σ Cost : Type u) (α : Type u) where
  /-- Resource cost of this step. -/
  cost : Cost
  /-- Updated machine state. -/
  machine : σ
  /-- The program that remains to be executed. -/
  program : Prog Q α

/-- Small-step semantics for a query language. Appending a continuation must not change the
current step's cost or state; it only appends that continuation to the remaining program. -/
structure Interpreter (Q : Type u → Type v) (σ Cost : Type u) where
  /-- Execute one query and determine the program to run next. -/
  step : {α β : Type u} → Q α → (α → Prog Q β) → σ → Step Q σ Cost β
  /-- A continuation starts after the current step has finished. -/
  step_bind : ∀ {α β γ : Type u} (q : Q α) (next : α → Prog Q β)
    (cont : β → Prog Q γ) (s : σ),
    step q (fun a => next a >>= cont) s =
      {step q next s with program := (step q next s).program >>= cont}

namespace Interpreter

variable (I : Interpreter Q σ Cost)

/-- Execute a program, consuming one unit of fuel for each interpreter step. -/
def run [AddZero Cost] : ℕ → Prog Q α → σ → Option (AddWriter Cost α × FuelExecState σ)
  | fuel, .pure a, s => some (⟨a, 0⟩, ⟨s, fuel⟩)
  | 0, .liftBind _ _, _ => none
  | fuel + 1, .liftBind q next, s => do
    let pending := I.step q next s
    let (result, final) ← run fuel pending.program pending.machine
    pure (⟨result.ret, pending.cost + result.tell⟩, final)

private theorem run_bind [AddMonoid Cost] (fuel : ℕ) (p : Prog Q α)
    (next : α → Prog Q β) (s : σ) :
    I.run fuel (p >>= next) s = (do
      let (a, t) ← I.run fuel p s
      let (b, u) ← I.run t.fuel (next a.ret) t.machine
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := by
  induction fuel generalizing p s with
  | zero =>
    cases p with
    | pure a => simp [run]; cases I.run 0 (next a) s <;> rfl
    | liftBind q cont => rfl
  | succ fuel ih =>
    cases p with
    | pure a => simp [run]; cases I.run (fuel + 1) (next a) s <;> rfl
    | liftBind q cont =>
      change I.run (fuel + 1) (.liftBind q (fun a => cont a >>= next)) s = _
      simp [run, I.step_bind, ih, Option.bind_assoc, add_assoc, -Cslib.FreeM.liftBind_eq]

/-- Interpret queries in the shared state-and-cost model using these small-step semantics. -/
def toModel [AddZero Cost] : ModelStateM Q (FuelExecMonad σ) Cost where
  runQuery q := AddWriterT.mk fun s => I.run s.fuel (Cslib.FreeM.lift q) s.machine

private theorem runStateM_eq_run [AddMonoid Cost] (p : Prog Q α) (s : FuelExecState σ) :
    (p.runStateM I.toModel).run s = I.run s.fuel p s.machine := by
  induction p generalizing s with
  | pure a => cases s with | mk machine fuel => cases fuel <;> rfl
  | liftBind q next ih =>
    change (Prog.runStateM (Cslib.FreeM.lift q >>= next) I.toModel).run s = _
    rw [Prog.runStateM_bind_stateT]
    simp only [Prog.runStateM_lift, ih]
    simpa only [toModel, AddWriterT.run_mk, Cslib.FreeM.liftBind_eq,
      Cslib.FreeM.bind_eq_bind] using (I.run_bind s.fuel (Cslib.FreeM.lift q) next s.machine).symm

end Interpreter

variable {I : Interpreter Q σ Cost} [AddMonoid Cost]

/-- Interpreting queries through the model agrees with executing the program one step at a time. -/
theorem execute_eq_run (fuel : ℕ) (p : Prog Q α) (s : σ) :
    execute I.toModel fuel p s = I.run fuel p s := I.runStateM_eq_run p ⟨s, fuel⟩

/-- A query's model interpretation agrees with executing its lifted program. -/
@[simp] theorem Interpreter.runQuery_eq_execute (I : Interpreter Q σ Cost) (q : Q α) :
    I.toModel.runQuery q = AddWriterT.mk (fun s => execute I.toModel s.fuel
      (Cslib.FreeM.lift q) s.machine) := by
  apply AddWriterT.ext
  funext s
  exact (execute_eq_run s.fuel (Cslib.FreeM.lift q) s.machine).symm

theorem execute_zero_liftBind (q : Q α) (next : α → Prog Q β) (s : σ) :
    execute I.toModel 0 (.liftBind q next) s = none := by rw [execute_eq_run]; rfl

/-- Execute one query, then run the remaining program with one less unit of fuel. -/
theorem execute_liftBind_succ (fuel : ℕ) (q : Q α) (next : α → Prog Q β) (s : σ) :
    execute I.toModel (fuel + 1) (.liftBind q next) s = (do
      let (result, final) ← execute I.toModel fuel
        (I.step q next s).program (I.step q next s).machine
      pure (⟨result.ret, (I.step q next s).cost + result.tell⟩, final)) := by
  simp only [execute_eq_run, Interpreter.run]

@[simp] theorem execute_zero_lift (q : Q α) (s : σ) :
    execute I.toModel 0 (Cslib.FreeM.lift q) s = none := execute_zero_liftBind q pure s

/-- Execute a lifted query using the same semantics as any other program. -/
@[simp] theorem execute_lift_succ (fuel : ℕ) (q : Q α) (s : σ) :
    execute I.toModel (fuel + 1) (Cslib.FreeM.lift q) s = (do
      let (result, final) ← execute I.toModel fuel
        (I.step q pure s).program (I.step q pure s).machine
      pure (⟨result.ret, (I.step q pure s).cost + result.tell⟩, final)) :=
  execute_liftBind_succ fuel q pure s

/-- Extra fuel preserves a completed execution and its exact resource cost. -/
theorem execute_add_fuel (fuel extra : ℕ) (p : Prog Q α) (s : σ)
    (result : AddWriter Cost α) (final : FuelExecState σ)
    (h : execute I.toModel fuel p s = some (result, final)) :
    execute I.toModel (fuel + extra) p s =
      some (result, {final with fuel := final.fuel + extra}) := by
  induction fuel generalizing p s result final with
  | zero =>
    cases p with
    | pure a =>
      simp only [Cslib.FreeM.pure_eq_pure, execute_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next => simp only [execute_zero_liftBind] at h; cases h
  | succ fuel ih =>
    cases p with
    | pure a =>
      simp only [Cslib.FreeM.pure_eq_pure, execute_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Nat.add_assoc]
    | liftBind q next =>
      simp only [execute_liftBind_succ] at h
      cases hr : execute I.toModel fuel (I.step q next s).program (I.step q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        have hu := ih _ _ _ _ hr
        rw [Nat.succ_add, execute_liftBind_succ, hu]
        rfl

/-- Remove unused fuel from a successful run without changing its result or cost. -/
theorem execute_trim_fuel (fuel : ℕ) (p : Prog Q α) (s : σ)
    (result : AddWriter Cost α) (final : FuelExecState σ)
    (h : execute I.toModel fuel p s = some (result, final)) :
    final.fuel ≤ fuel ∧
      execute I.toModel (fuel - final.fuel) p s = some (result, ⟨final.machine, 0⟩) := by
  induction fuel generalizing p s result final with
  | zero =>
    cases p with
    | pure a =>
      simp only [Cslib.FreeM.pure_eq_pure, execute_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next => simp only [execute_zero_liftBind] at h; cases h
  | succ fuel ih =>
    cases p with
    | pure a =>
      simp only [Cslib.FreeM.pure_eq_pure, execute_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next =>
      simp only [execute_liftBind_succ] at h
      cases hr : execute I.toModel fuel (I.step q next s).program (I.step q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        obtain ⟨hle, htrim⟩ := ih _ _ _ _ hr
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hle.trans (Nat.le_succ fuel), ?_⟩
        have hsub : fuel + 1 - u.fuel = (fuel - u.fuel) + 1 := by omega
        rw [hsub, execute_liftBind_succ, htrim]
        rfl

end FuelExecMonad
end Algolean.Algorithms
