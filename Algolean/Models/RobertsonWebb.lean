/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.QueryModel
public import Mathlib.MeasureTheory.Measure.FiniteMeasure

@[expose] public section


namespace Algolean

namespace Algorithms


open Cslib Prog MeasureTheory

/-- Valuation Function on a measurable cake -/
structure ValFunction (Cake : Type) [MeasurableSpace Cake] where
  /-- val is a finite measure on the cake -/
  val : FiniteMeasure Cake

/-- Allocation structure of a cake indexed by agents -/
structure Alloc (α Cake : Type) [MeasurableSpace Cake] where
  /-- `alloc` is the allocation function on a cake. It allocates
  "subsets" of the cake -/
  alloc : α → Set Cake
  /-- The allocations of `alloc` are measurable sets -/
  allocMeasurable : ∀ a : α, Measurable (alloc a)

/-- An allocation instance combines a valuation function with an allocation -/
structure AllocInstance (α Cake : Type) [MeasurableSpace Cake] where
  /-- The allocation -/
  allocInst : Alloc α Cake
  /-- Each agent's valuation -/
  valFuns : α → ValFunction Cake

/-- An allocation is complete if every element of the cake is allocated to some agent -/
abbrev Alloc.IsComplete {α Cake : Type} [MeasurableSpace Cake]
  (a : Alloc α Cake) := ∀ i : Cake, ∃ agent : α, i ∈ a.alloc agent

/-- Abbreviation for the type of real numbers in a closed interval -/
abbrev I (x y : ℝ) : Type := {a : ℝ // x ≤ a ∧ a ≤ y}

/-- The type of real numbers in the closed interval [0,1] -/
abbrev UnitI := I 0 1

/-- Envy freeness of agent `x` w.r.t agent `y` in allocation instance `a` -/
abbrev EFAgents [MeasurableSpace Cake] (a : AllocInstance α Cake) (x y : α) : Prop :=
  (a.valFuns x).val (a.allocInst.alloc x) ≥ (a.valFuns x).val (a.allocInst.alloc y)

/-- Envy freeness of the allocation instance -/
abbrev EF [MeasurableSpace Cake] (a : AllocInstance α Cake) :=
  ∀ x y : α, EFAgents a x y

/-- The Robertsion Webb query model -/
inductive RobertsonWebbQuery (α : Type) : Type → Type where
  /-- evaluates agent `i`'s value for interval `[x,y]` -/
  | eval (i : α) (x y : UnitI) : RobertsonWebbQuery α ℝ
  /-- given a starting point `x` and value `val`
      returns a `y` such that `eval i x y = val` or `y = 1` -/
  | mark (i : α) (x : UnitI) (val : ℝ) : RobertsonWebbQuery α UnitI

/-- The cost structure of the Robertson Webb query model -/
@[ext, grind]
structure RWCosts where
  /-- the number of calls to the `eval` query -/
  evals : ℕ
  /-- the number of calls to the `mark` query -/
  marks : ℕ

/-- Equivalence between SortOpsCost and a product type. -/
def RWCosts.equivProd : RWCosts ≃ (ℕ × ℕ) where
  toFun rwc := (rwc.evals, rwc.marks)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace RWCosts

@[simps, grind]
instance : Zero RWCosts := ⟨0, 0⟩

@[simps]
instance : LE RWCosts where
  le soc₁ soc₂ := soc₁.evals ≤ soc₂.evals ∧ soc₁.marks ≤ soc₂.marks

instance : LT RWCosts where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder RWCosts :=
  fast_instance% RWCosts.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add RWCosts where
  add soc₁ soc₂ := ⟨soc₁.evals + soc₂.evals, soc₁.marks + soc₂.marks⟩

@[simps]
instance : SMul ℕ RWCosts where
  smul n soc := ⟨n • soc.evals, n • soc.marks⟩

instance : AddCommMonoid RWCosts :=
  fast_instance%
    RWCosts.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

end RWCosts

open Classical in
/-- This model necessarily uses classical. Watch out for hacks -/
@[simps]
noncomputable def RobertsonWebbModel {α : Type}
    (allocInst : AllocInstance α UnitI)
    : Model (RobertsonWebbQuery α) RWCosts where
  evalQuery
    | .eval i x y => (allocInst.valFuns i).val (Set.Icc x y)
    | .mark i x val =>
        let proposition := ∃ y : UnitI, (allocInst.valFuns i).val (Set.Icc x y) = val
        if h : proposition then
          Exists.choose h
        else
          ⟨(1 : ℝ), by grind⟩
  cost
    | .eval _ _ _ => ⟨1, 0⟩
    | .mark _ _ _ => ⟨0, 1⟩


end Algorithms

end Algolean
