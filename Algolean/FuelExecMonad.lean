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

## Main definitions and results

* `FuelExecState σ` pairs a machine state with its remaining interpreter fuel.
* `FuelExecMonad σ` provides stateful execution with failure through `Option`.
* `FuelExecMonad.run_bind_cost` threads state and fuel while adding execution costs.
* `FuelExecMonad.execute` runs a query program using a supplied `ModelStateM` interpreter.
* `FuelExecMonad.execute_pure` and `FuelExecMonad.execute_bind` describe program execution.
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

/-- A pure action preserves the machine state and remaining fuel. -/
@[simp, grind =] theorem run_pure (a : α) (s : FuelExecState σ) :
    (pure a : FuelExecMonad σ α) s = some (a, s) := rfl

/-- Sequencing passes the first action's result and execution state to the second action. -/
@[simp, grind =] theorem run_bind (action : FuelExecMonad σ α)
    (next : α → FuelExecMonad σ β) (s : FuelExecState σ) :
    (action >>= next) s = (do
      let (a, t) ← action s
      next a t) := rfl

/-- Sequence costed actions, threading the machine state and remaining budget together. -/
@[simp, grind =] theorem run_bind_cost [Add Cost]
    (action : AddWriterT Cost (FuelExecMonad σ) α)
    (next : α → AddWriterT Cost (FuelExecMonad σ) β) (s : FuelExecState σ) :
    (action >>= next).run s = (do
      let (a, t) ← action.run s
      let (b, u) ← (next a.ret).run t
      pure (⟨b.ret, a.tell + b.tell⟩, u)) := rfl

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
  simp [execute, Prog.runStateM_bind]

end FuelExecMonad
end Algolean.Algorithms
