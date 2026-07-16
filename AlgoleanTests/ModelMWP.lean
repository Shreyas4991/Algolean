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

Regression coverage showing that an effectful query model inherits `mvcgen` support whenever its
semantic monad has a `WPMonad` instance. The chosen handler is local, so it cannot conflict with a
pure `Model` or another effectful interpretation of the same query syntax.
-/

@[expose] public section

set_option mvcgen.warning false

namespace AlgoleanTests.ModelMWP

open Algolean.Algorithms Cslib Cslib.FreeM Std.Do

inductive CounterQ : Type → Type where
  | tick : CounterQ Unit
  | read : CounterQ Nat

def counterModel : ModelM CounterQ (StateM Nat) Nat where
  evalQuery
    | .tick => modify (· + 1)
    | .read => get
  cost _ := 1

local instance : HasHandler CounterQ (.arg Nat .pure) := counterModel.hasHandler

def tick : Prog CounterQ Unit := FreeM.lift .tick

def read : Prog CounterQ Nat := FreeM.lift .read

def tickThenRead : Prog CounterQ Nat := do
  tick
  read

example (P : Prog CounterQ α) :
    wpH counterModel.handler P = wp (P.evalM counterModel) :=
  counterModel.wp_eq_wp_evalM P

example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ tickThenRead
      ⦃⇓ value s => ⌜value = n + 1 ∧ s = n + 1⌝⦄ := by
  mvcgen [tickThenRead, tick, read, counterModel, ModelM.handler]
  subst_vars
  exact ⟨rfl, rfl⟩

end AlgoleanTests.ModelMWP
