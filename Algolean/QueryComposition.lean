/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/

module

public import Algolean.QueryModel

/-!
## Composition of Queries and their Models

This file defines composition of queries and their models
in the query-combinator model
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib

/-- Given two queries Q₁ and Q₂, creates a new query over the sum type -/
abbrev compositeQuery (Q₁ Q₂ : Type u → Type v) : Type u → Type v :=
  fun β => Sum (Q₁ β) (Q₂ β)

/-- Given two models m₁ and m₂ with query operations Q₁ and Q₂ and
    costs c₁ and c₂, creates a new mode with query operations over
    the sume type of Q₁ and Q₂ and with the costs as a product type of
    c₁ and c₂
-/
def Model.compose [AddZero c₁] [AddZero c₂]
    (m₁ : Model Q₁ c₁) (m₂ : Model Q₂ c₂) :
    Model (compositeQuery Q₁ Q₂) (c₁ × c₂) where
  evalQuery
    | .inl q => m₁.evalQuery q
    | .inr q => m₂.evalQuery q
  cost
    | .inl q => (m₁.cost q, 0)
    | .inr q => (0, m₂.cost q)

@[simp, grind =]
theorem Model.evalQuery_compose_left [AddZero c₁] [AddZero c₂]
    {m₁ : Model Q₁ c₁} {m₂ : Model Q₂ c₂} {q : Q₁ i} :
    (m₁.compose m₂).evalQuery (Sum.inl q) = m₁.evalQuery q := by
  rfl

@[simp, grind =]
theorem Model.evalQuery_compose_right [AddZero c₁] [AddZero c₂]
    {m₁ : Model Q₁ c₁} {m₂ : Model Q₂ c₂} {q : Q₂ i} :
    (m₁.compose m₂).evalQuery (Sum.inr q) = m₂.evalQuery q := by
  rfl

@[simp, grind =]
theorem Model.cost_compose_left [AddZero c₁] [AddZero c₂]
    {m₁ : Model Q₁ c₁} {m₂ : Model Q₂ c₂} {q : Q₁ i} :
    (m₁.compose m₂).cost (Sum.inl q) = (m₁.cost q, 0) := by
  rfl

@[simp, grind =]
theorem Model.cost_compose_right [AddZero c₁] [AddZero c₂]
    {m₁ : Model Q₁ c₁} {m₂ : Model Q₂ c₂} {q : Q₂ i} :
    (m₁.compose m₂).cost (Sum.inr q) = (0, m₂.cost q) := by
  rfl

/-- Combines a reduction from Q₁ to Q₃ and a reduction from Q₂ to Q₃ into
    a reduction over the sum of Q₁ and Q₂ to Q₃
-/
def Reduction.compose {Q₁ Q₂ Q₃ : Type u → Type u} (r₁ : Reduction Q₁ Q₃) (r₂ : Reduction Q₂ Q₃) :
    Reduction (compositeQuery Q₁ Q₂) Q₃ where
  reduce := fun q =>
    match q with
    | .inl q => r₁.reduce q
    | .inr q => r₂.reduce q

@[simp, grind =]
theorem Reduction.reduce_compose_left
    {r₁ : Reduction Q₁ Q₃} {r₂ : Reduction Q₂ Q₃} {q : Q₁ i} :
    (r₁.compose r₂).reduce (Sum.inl q) = r₁.reduce q := by
  rfl

@[simp, grind =]
theorem Reduction.reduce_compose_right
    {r₁ : Reduction Q₁ Q₃} {r₂ : Reduction Q₂ Q₃} {q : Q₂ i} :
    (r₁.compose r₂).reduce (Sum.inr q) = r₂.reduce q := by
  rfl

/-- Given a program P with query operations from Q₁, we obtain a new program
    with query operations from the sum of Q₁ Q₂ that behaves exactly like P.
-/
def Prog.extend {Q₁ α} (Q₂ : Type u → Type u) (P : Prog Q₁ α) : Prog (compositeQuery Q₁ Q₂) α :=
  match P with
  | .liftBind op cont => .liftBind (Sum.inl op) (fun x => extend Q₂ (cont x))
  | .pure a => pure a

@[simp]
theorem Prog.extend_compose_reduceProg {Q₁ α Q₂ Q₃} {P : Prog Q₁ α}
    {r₁ : Reduction Q₁ Q₃} {r₂ : Reduction Q₂ Q₃} :
    (P.extend Q₂).reduceProg (r₁.compose r₂) = P.reduceProg r₁ := by
  induction P with
  | pure a => simp [extend]
  | liftBind op cond ih =>
    simp [extend, ih]

@[simp, grind =]
theorem Prog.extend_eval {Q₁ α Q₂ c₁ c₂} [AddZero c₁] [AddZero c₂] {P : Prog Q₁ α}
    {M₁ : Model Q₁ c₁} {M₂ : Model Q₂ c₂} :
    (P.extend Q₂).eval (M₁.compose M₂) = P.eval M₁ := by
  induction P with
  | pure a => simp [extend]
  | liftBind op cond ih =>
    simp [extend, ih]

@[simp, grind =]
theorem Prog.extend_time {Q₁ α Q₂ c₁ c₂} [AddCommMonoid c₁] [AddCommMonoid c₂] {P : Prog Q₁ α}
    {M₁ : Model Q₁ c₁} {M₂ : Model Q₂ c₂} :
    ((P.extend Q₂).time (M₁.compose M₂)) = (P.time M₁, 0) := by
  induction P with
  | pure a => simp [extend, Prod.zero_eq_mk]
  | liftBind op cond ih =>
    simp [extend, ih]

end Algolean.Algorithms
