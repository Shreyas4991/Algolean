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

This file exercises weakest-precondition reasoning and `vcgen` for a `StateM` query model.
-/

@[expose] public section

set_option experimental.vcgen true

namespace AlgoleanTests.ModelMWP

open Algolean.Algorithms Cslib Cslib.FreeM Lean.Order Std.WP

/-- Queries for incrementing and reading a counter. -/
inductive CounterQ : Type → Type where
  | tick : CounterQ Unit
  | read : CounterQ Nat

/-- Interpret counter queries in `StateM Nat`, with unit cost for each query. -/
def counterModel : ModelM CounterQ (StateM Nat) Nat where
  evalQuery
    | .tick => modify (· + 1)
    | .read => get
  cost _ := 1

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
    (wpH counterModel.handler P).apply post () ⊑ wp (P.evalM counterModel) post () :=
  counterModel.wp_le_wp_evalM P post ()

example {Q : Nat → Nat → Prop} :
    let _ : HasHandler CounterQ (Nat → Prop) EStack⟨⟩ := counterModel.hasHandler
    Triple (FreeM.lift CounterQ.read : Prog CounterQ Nat)
      (wp (counterModel.evalQuery .read) Q ()) Q () := by
  dsimp only
  vcgen [counterModel, ModelM.handler]
  assumption

example (n : Nat) :
    ⦃ fun s => s = n ⦄ tickThenRead
      ⦃ fun value s => value = n + 1 ∧ s = n + 1 ⦄ := by
  vcgen [tickThenRead, tick, read, counterModel, ModelM.handler]
  subst_vars
  exact ⟨rfl, rfl⟩

end AlgoleanTests.ModelMWP
