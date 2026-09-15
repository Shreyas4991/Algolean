/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.ModelStateM

/-!
# Tests for monadic query models

This file tests branch-dependent cost accumulation and cost-preserving query reductions.
-/

@[expose] public section

namespace AlgoleanTests.ModelStateM

open Algolean Algolean.Algorithms Cslib

/-- Queries for a binary choice and a unit-cost step. -/
inductive ChoiceQ : Type → Type where
  | choose : ChoiceQ Bool
  | tick : ChoiceQ Unit

/-- Interpret `ChoiceQ` in the list monad. -/
def choiceModel : ModelStateM ChoiceQ List Nat :=
  ModelStateM.ofCost (fun | .choose => [false, true] | .tick => [()]) (fun _ => 1)

/-- Perform an additional query on the `true` branch. -/
def branch : Prog ChoiceQ Unit := do
  if ← FreeM.lift .choose then
    FreeM.lift .tick

example : (branch.runStateM choiceModel).run = [⟨(), 1⟩, ⟨(), 2⟩] := rfl

example : branch.costStateM choiceModel = [1, 2] := rfl

/-- The cost of a choice can depend on that very choice's result. -/
def correlatedChoice : ModelStateM ChoiceQ List Nat where
  runQuery
    | .choose => AddWriterT.mk [⟨false, 3⟩, ⟨true, 7⟩]
    | .tick => AddWriterT.mk [⟨(), 1⟩]

example : (branch.runStateM correlatedChoice).run = [⟨(), 3⟩, ⟨(), 8⟩] := rfl

example : branch.costStateM correlatedChoice = [3, 8] := rfl

example : branch.evalStateM correlatedChoice = [(), ()] := rfl

/-- A unit-cost state increment. -/
inductive TickQ : Type → Type where
  | tick : TickQ Unit

/-- A state increment of two. -/
inductive DoubleTickQ : Type → Type where
  | tickTwice : DoubleTickQ Unit

/-- Interpret `TickQ` as a state increment. -/
def tickModel : ModelStateM TickQ (StateM Nat) Nat :=
  ModelStateM.ofCost (fun | .tick => modify (· + 1)) (fun _ => 1)

/-- Interpret `DoubleTickQ` as a state increment of two. -/
def doubleTickModel : ModelStateM DoubleTickQ (StateM Nat) Nat :=
  ModelStateM.ofCost (fun | .tickTwice => modify (· + 2)) (fun _ => 2)

/-- Implement one double increment using two unit increments. -/
def doubleTickReduction : Reduction DoubleTickQ TickQ where
  reduce
    | .tickTwice => do
      FreeM.lift .tick
      FreeM.lift .tick

example (P : Prog DoubleTickQ α) :
    (P.reduceProg doubleTickReduction).runStateM tickModel = P.runStateM doubleTickModel := by
  apply Prog.reduceProg_runStateM
  intro _ q
  cases q
  rfl

end AlgoleanTests.ModelStateM
