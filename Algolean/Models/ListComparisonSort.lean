/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric WIeser, Ethan Ermovick
-/

module

public import Algolean.QueryModel
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FastInstance
@[expose] public section

/-!
# Query Type for Comparison Search in Lists

In this file we define two query types `SortOps` which is suitable for insertion sort, and
`SortOps`for comparison based searching in Lists. We define a model `sortModel` for `SortOps`
which uses a custom cost structure `SortOpsCost`. We define a model `sortModelCmp` for `SortOpsCmp`
which defines a `ℕ` based cost structure. We also define a notion of stability for sorting
algorithms in lists.
--
## Definitions

- `SortOps`: A query type for comparison based sorting in lists which includes queries for
   comparison and head-insertion into Lists. This is a suitable query for ordered insertion
   and insertion sort.
- `SortOpsCmp`:  A query type for comparison based sorting that only includes a comparison query.
   This is more suitable for comparison based sorts for which it is only desirable to count
   comparisons
- `IsStableSort`: A definition of stability for sorting algorithms in lists.

-/
namespace Algolean

namespace Algorithms

open Prog

/--
A model for comparison sorting on lists.
-/
inductive SortOpsInsertHead (α : Type) : Type → Type  where
  /-- `cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the model provided for this typ. e-/
  | cmpLE (x : α) (y : α) : SortOpsInsertHead α Bool
  /-- `insertHead l x` is intended to return `x :: l`. -/
  | insertHead (x : α) (l : List α) : SortOpsInsertHead α (List α)

open SortOpsInsertHead

section SortOpsCostModel

/--
A cost type for counting the operations of `SortOps` with separate fields for
counting calls to `cmpLT` and `insertHead`
-/
@[ext, grind]
structure SortOpsCost where
  /-- `compares` counts the number of calls to `cmpLT` -/
  compares : ℕ
  /-- `inserts` counts the number of calls to `insertHead` -/
  inserts : ℕ

/-- Equivalence between SortOpsCost and a product type. -/
def SortOpsCost.equivProd : SortOpsCost ≃ (ℕ × ℕ) where
  toFun sortOps := (sortOps.compares, sortOps.inserts)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace SortOpsCost

@[simps, grind]
instance : Zero SortOpsCost := ⟨0, 0⟩

@[simps]
instance : LE SortOpsCost where
  le soc₁ soc₂ := soc₁.compares ≤ soc₂.compares ∧ soc₁.inserts ≤ soc₂.inserts

instance : LT SortOpsCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder SortOpsCost :=
  fast_instance% SortOpsCost.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add SortOpsCost where
  add soc₁ soc₂ := ⟨soc₁.compares + soc₂.compares, soc₁.inserts + soc₂.inserts⟩

@[simps]
instance : SMul ℕ SortOpsCost where
  smul n soc := ⟨n • soc.compares, n • soc.inserts⟩

instance : AddCommMonoid SortOpsCost :=
  fast_instance%
    SortOpsCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

end SortOpsCost

/--
A model of `SortOps` that uses `SortOpsCost` as the cost type for operations.

While this accepts any decidable relation `le`, most sorting algorithms are only well-behaved in the
presence of `[Std.Total le] [IsTrans _ le]`.
-/
@[simps, grind]
def sortModel {α : Type} (le : α → α → Bool) :
    Model (SortOpsInsertHead α) SortOpsCost where
  evalQuery
    | .cmpLE x y => le x y
    | .insertHead x l => x :: l
  cost
    | .cmpLE _ _ => ⟨1,0⟩
    | .insertHead _ _ => ⟨0,1⟩

end SortOpsCostModel

section NatModel

/--
A model for comparison sorting on lists with only the comparison operation. This
is used in mergeSort.
-/
inductive SortOps.{u} (α : Type u) : Type → Type _ where
  /-- `cmpLE x y` is intended to return `true` if `x ≤ y` and `false` otherwise.
  The specific order relation depends on the model provided for this type. -/
  | cmpLE (x : α) (y : α) : SortOps α Bool

/--
A model of `SortOps` that uses `ℕ` as the type for the cost of operations. In this model,
both comparisons and insertions are counted in a single `ℕ` parameter.

While this accepts any decidable relation `le`, most sorting algorithms are only well-behaved in the
presence of `[Std.Total le] [IsTrans _ le]`.
-/
@[simps]
def sortModelNat {α : Type*}
    (le : α → α → Bool) : Model (SortOps α) ℕ where
  evalQuery
    | .cmpLE x y => le x y
  cost _ := 1

end NatModel

section SortStability

/--
Definition of a stable list sorting algorithm.
TODO: relocate or upstream definition
-/
def IsStableSort
    (sortAlg : List α → List α)
    (xs : List α)
    (le : α → α → Bool) : Prop :=
  let ys := sortAlg xs
  ∀ k : α, ys.filter (fun x => le x k && le k x) = xs.filter (fun x => le x k && le k x)

end SortStability

end Algorithms

end Algolean
