/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.ModelM
public import Std.Tactic.Do

/-!
# Weakest-precondition reasoning for `ModelM`

This file exercises weakest-precondition reasoning and `mvcgen` for a `StateM` query model.
-/

@[expose] public section

set_option mvcgen.warning false

namespace AlgoleanTests.ModelMWP

open Algolean Algolean.Algorithms Cslib Cslib.FreeM Std.Do

/-- Queries for incrementing and reading a counter. -/
inductive CounterQ : Type → Type where
  | tick : CounterQ Unit
  | read : CounterQ Nat

/-- Interpret counter queries in `StateM Nat`, with unit cost for each query. -/
def counterModel : ModelM CounterQ (StateM Nat) Nat :=
  ModelM.ofCost (fun | .tick => modify (· + 1) | .read => get) (fun _ => 1)

section Evaluation

local instance : HasHandler CounterQ (.arg Nat .pure) := counterModel.hasHandler

/-- Increment the counter. -/
def tick : Prog CounterQ Unit := FreeM.lift .tick

/-- Read the counter. -/
def read : Prog CounterQ Nat := FreeM.lift .read

/-- Increment the counter and return its new value. -/
def tickThenRead : Prog CounterQ Nat := do
  tick
  read

example (P : Prog CounterQ α) :
    wpH counterModel.handler P = wp (P.evalM counterModel) :=
  counterModel.wp_eq_wp_evalM P

example {Q : PostCond Nat (.arg Nat .pure)} :
    let _ : HasHandler CounterQ (.arg Nat .pure) := counterModel.hasHandler
    Triple (FreeM.lift CounterQ.read : Prog CounterQ Nat)
      (wp⟦counterModel.evalQuery .read⟧ Q) Q := by
  mvcgen [counterModel, ModelM.handler]

example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ tickThenRead
      ⦃⇓ value s => ⌜value = n + 1 ∧ s = n + 1⌝⦄ := by
  mvcgen [tickThenRead, tick, read, counterModel, ModelM.handler]
  subst_vars
  exact ⟨rfl, rfl⟩

end Evaluation

section Costs

local instance counterCostHandler : HasHandler CounterQ (.arg Nat (.arg Nat .pure)) :=
  counterModel.hasCostHandler

example (P : Prog CounterQ α) :
    wpH counterModel.costHandler P = wp (P.runM counterModel) :=
  counterModel.wp_eq_wp_runM P

-- Both queries are charged, and an existing cost is retained.
example (n c : Nat) :
    ⦃fun cost s => ⌜cost = c ∧ s = n⌝⦄ tickThenRead
      ⦃⇓ value cost s => ⌜value = n + 1 ∧ s = n + 1 ∧ cost = c + 2⌝⦄ := by
  mvcgen [tickThenRead, tick, read]
  simp_all only [HasHandler.handler, counterModel, wp_lift, ModelM.costHandler_apply_state,
    ModelM.ofCost_runQuery_state, Nat.add_assoc, Nat.reduceAdd,
    and_true, SPred.down_pure_nil]
  exact ⟨rfl, rfl⟩

/-- A query whose cost is determined by the incoming machine state. -/
def stateCostModel : ModelM CounterQ (StateM Nat) Nat where
  runQuery
    | .tick => AddWriterT.mk fun s => (⟨(), s + 1⟩, s + 1)
    | .read => AddWriterT.mk fun s => (⟨s, 1⟩, s)

end Costs

section StateCosts

local instance : HasHandler CounterQ (.arg Nat (.arg Nat .pure)) :=
  stateCostModel.hasCostHandler

example (n c : Nat) :
    ⦃fun cost s => ⌜cost = c ∧ s = n⌝⦄ tickThenRead
      ⦃⇓ value cost s => ⌜value = n + 1 ∧ s = n + 1 ∧ cost = c + n + 2⌝⦄ := by
  mvcgen [tickThenRead, tick, read]
  simp_all [HasHandler.handler, stateCostModel, Nat.add_assoc]

end StateCosts

end AlgoleanTests.ModelMWP
