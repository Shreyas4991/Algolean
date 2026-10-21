/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.ModelStateM
public import Std.Tactic.Do

/-!
# Weakest-precondition reasoning for `ModelStateM`

This file exercises weakest-precondition reasoning and `vcgen` for a `StateM` query model.
-/

@[expose] public section

set_option experimental.vcgen true

namespace AlgoleanTests.ModelStateMWP

open Algolean Algolean.Algorithms Cslib Cslib.FreeM Lean.Order Std.WP

/-- Queries for incrementing and reading a counter. -/
inductive CounterQ : Type → Type where
  | tick : CounterQ Unit
  | read : CounterQ Nat

/-- Interpret counter queries in `StateM Nat`, with unit cost for each query. -/
def counterModel : ModelStateM CounterQ (StateM Nat) Nat :=
  ModelStateM.ofCost (fun | .tick => modify (· + 1) | .read => get) (fun _ => 1)

section Evaluation

local instance : HasHandler CounterQ (Nat → Prop) EStack⟨⟩ := counterModel.hasHandler

/-- Increment the counter. -/
def tick : Prog CounterQ Unit := FreeM.lift .tick

/-- Read the counter. -/
def read : Prog CounterQ Nat := FreeM.lift .read

/-- Increment the counter and return its new value. -/
def tickThenRead : Prog CounterQ Nat := do
  tick
  read

example (P : Prog CounterQ α) (post : α → Nat → Prop) :
    (wpH counterModel.handler P).apply post () ⊑ wp (P.evalStateM counterModel) post () :=
  counterModel.wp_le_wp_evalStateM P post ()

example {Q : Nat → Nat → Prop} :
    let _ : HasHandler CounterQ (Nat → Prop) EStack⟨⟩ := counterModel.hasHandler
    Triple (FreeM.lift CounterQ.read : Prog CounterQ Nat)
      (wp (counterModel.evalQuery .read) Q ()) Q () := by
  dsimp only
  vcgen [counterModel, ModelStateM.handler]
  assumption

example (n : Nat) :
    ⦃ fun s => s = n ⦄ tickThenRead
      ⦃ fun value s => value = n + 1 ∧ s = n + 1 ⦄ := by
  vcgen [tickThenRead, tick, read, counterModel, ModelStateM.handler]
  subst_vars
  exact ⟨rfl, rfl⟩

end Evaluation

section Costs

local instance counterCostHandler : HasHandler CounterQ (Nat → Nat → Prop) EStack⟨⟩ :=
  counterModel.hasCostHandler

example (P : Prog CounterQ α) (post : α → Nat → Nat → Prop) :
    (wpH counterModel.costHandler P).apply post () ⊑ wp (P.runStateM counterModel) post () :=
  counterModel.wp_le_wp_runStateM P post ()

-- Both queries are charged, and an existing cost is retained.
example (n c : Nat) :
    ⦃ fun cost s => cost = c ∧ s = n ⦄ tickThenRead
      ⦃ fun value cost s => value = n + 1 ∧ s = n + 1 ∧ cost = c + 2 ⦄ := by
  vcgen [tickThenRead, tick, read]
  rename_i initial state h
  rcases h with ⟨hcost, hstate⟩
  subst initial
  subst state
  change n + 1 = n + 1 ∧ n + 1 = n + 1 ∧ c + 1 + 1 = c + 2
  exact ⟨rfl, rfl, by omega⟩

/-- A query whose cost is determined by the incoming machine state. -/
def stateCostModel : ModelStateM CounterQ (StateM Nat) Nat where
  runQuery
    | .tick => AddWriterT.mk fun s => (⟨(), s + 1⟩, s + 1)
    | .read => AddWriterT.mk fun s => (⟨s, 1⟩, s)

end Costs

section StateCosts

local instance : HasHandler CounterQ (Nat → Nat → Prop) EStack⟨⟩ :=
  stateCostModel.hasCostHandler

example (n c : Nat) :
    ⦃ fun cost s => cost = c ∧ s = n ⦄ tickThenRead
      ⦃ fun value cost s => value = n + 1 ∧ s = n + 1 ∧ cost = c + n + 2 ⦄ := by
  vcgen [tickThenRead, tick, read]
  rename_i initial state h
  rcases h with ⟨hcost, hstate⟩
  subst initial
  subst state
  change n + 1 = n + 1 ∧ n + 1 = n + 1 ∧ c + (n + 1) + 1 = c + n + 2
  exact ⟨rfl, rfl, by omega⟩

end StateCosts

end AlgoleanTests.ModelStateMWP
