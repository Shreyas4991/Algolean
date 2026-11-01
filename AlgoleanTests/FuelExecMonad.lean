/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.FuelExecMonad

/-!
# Fuelled execution with queries that return data

The interpreter in this example uses a natural number as its state and a pair of natural
numbers as its cost. Reading the state returns a value to the program's continuation.
These examples check that the shared runner handles such queries as well as `Unit` queries.
-/

@[expose] public section

namespace AlgoleanTests.FuelExecMonad

open Algolean Algolean.Algorithms Cslib

/-- Read the current counter or add a supplied amount to it. -/
inductive Query : Type → Type where
  | read : Query ℕ
  | add (amount : ℕ) : Query Unit

/-- Count executed queries and the total amount added to the counter. -/
def counter : FuelExecMonad.Interpreter Query ℕ (ℕ × ℕ) where
  step q next s := match q with
    | .read => ⟨(1, 0), s, next s⟩
    | .add amount => ⟨(1, amount), s + amount, next ()⟩
  step_bind q next cont s := by cases q <;> rfl

/-- Use the value returned by a query to choose the next query's argument and the final result. -/
def program : Prog Query ℕ := do
  let value ← FreeM.lift .read
  FreeM.lift (.add (value + 1))
  pure (2 * value)

example : FuelExecMonad.execute counter.toModel 2 program 3 =
    some (⟨6, (2, 4)⟩, ⟨7, 0⟩) := rfl

-- Exhaustion discards the result, costs, and intermediate state.
example : FuelExecMonad.execute counter.toModel 1 program 3 = none := rfl

-- Extra fuel leaves the result, state, and costs unchanged.
example : FuelExecMonad.execute counter.toModel 5 program 3 =
    some (⟨6, (2, 4)⟩, ⟨7, 3⟩) :=
  FuelExecMonad.execute_add_fuel (I := counter) 2 3 program 3 ⟨6, (2, 4)⟩ ⟨7, 0⟩ rfl

example : FuelExecMonad.execute counter.toModel (5 - 3) program 3 =
    some (⟨6, (2, 4)⟩, ⟨7, 0⟩) :=
  (FuelExecMonad.execute_trim_fuel (I := counter) 5 program 3 ⟨6, (2, 4)⟩ ⟨7, 3⟩ rfl).2

end AlgoleanTests.FuelExecMonad
