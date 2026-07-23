/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.ModelM

/-!
# Tests for monadic query models

This file tests branch-dependent cost accumulation and cost-preserving query reductions.
-/

@[expose] public section

namespace AlgoleanTests.ModelM

open Algolean Algolean.Algorithms Cslib

/-- Queries for a binary choice and a unit-cost step. -/
inductive ChoiceQ : Type → Type where
  | choose : ChoiceQ Bool
  | tick : ChoiceQ Unit

/-- Interpret `ChoiceQ` in the list monad. -/
def choiceModel : ModelM ChoiceQ List Nat where
  evalQuery
    | .choose => [false, true]
    | .tick => [()]
  cost _ := 1

/-- Perform an additional query on the `true` branch. -/
def branch : Prog ChoiceQ Unit := do
  if ← FreeM.lift .choose then
    FreeM.lift .tick

example : (branch.runM choiceModel).run = [⟨(), 1⟩, ⟨(), 2⟩] := rfl

example : branch.costM choiceModel = [1, 2] := rfl

/-- A unit-cost state increment. -/
inductive TickQ : Type → Type where
  | tick : TickQ Unit

/-- A state increment of two. -/
inductive DoubleTickQ : Type → Type where
  | tickTwice : DoubleTickQ Unit

/-- Interpret `TickQ` as a state increment. -/
def tickModel : ModelM TickQ (StateM Nat) Nat where
  evalQuery
    | .tick => modify (· + 1)
  cost _ := 1

/-- Interpret `DoubleTickQ` as a state increment of two. -/
def doubleTickModel : ModelM DoubleTickQ (StateM Nat) Nat where
  evalQuery
    | .tickTwice => modify (· + 2)
  cost _ := 2

/-- Implement one double increment using two unit increments. -/
def doubleTickReduction : Reduction DoubleTickQ TickQ where
  reduce
    | .tickTwice => do
      FreeM.lift .tick
      FreeM.lift .tick

example (P : Prog DoubleTickQ α) :
    (P.reduceProg doubleTickReduction).runM tickModel = P.runM doubleTickModel := by
  apply Prog.reduceProg_runM
  intro _ q
  cases q
  rfl

end AlgoleanTests.ModelM
