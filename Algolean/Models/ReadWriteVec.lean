/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.QueryModel

@[expose] public section

/-!
# Query Type for Read Only Vectors

In this file we define a query type `Vec` for algorithms that
read or write into specific indices of a vector at unit cost.
We have two cost models:
1. Vec.natCost : Which does not differentiate between reads and writes
2. Vec.vecRWCost : Which counts reads and writes separately

--
## Definitions

- `ReadOnlyVec`: A query type for comparison based search in lists.
- `ReadOnlyVec.natCost`:  A model for this query with costs in `ℕ`.
- `ReadOnly
-/

namespace Algolean

namespace Algorithms

open Prog

/--
A query type which provides read only access to a vector. It lets you read from and
write to an index. The vector size is fixed.
-/
inductive Vec (α : Type) : Type → Type _ where
  | read (a : Vector α n) (i : Fin n) : Vec α α
  | write (a : Vector α n) (i : Fin n) (x : α) : Vec α (Vector α n)

/-- A model of the `Vec` query type that assigns the cost as the number of queries. -/
@[simps]
def Vec.natCost : Model (Vec α) ℕ where
  evalQuery
    | .read a i => a[i]
    | .write a i x => a.set i x
  cost _ := 1


section VecModel

/--
A cost type for counting the operations of `Vec` with separate fields for
counting calls to `read` and `write`
-/
@[ext, grind]
structure VecRW where
  /-- `read` counts the number of calls to `cmpLT` -/
  read : ℕ
  /-- `write` counts the number of calls to `insertHead` -/
  write : ℕ

/-- Equivalence between SortOpsCost and a product type. -/
def VecRW.equivProd : VecRW ≃ (ℕ × ℕ) where
  toFun rw := (rw.read, rw.write)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace VecRW

@[simps, grind]
instance : Zero VecRW := ⟨0, 0⟩

@[simps]
instance : LE VecRW where
  le soc₁ soc₂ := soc₁.read ≤ soc₂.read ∧ soc₁.write ≤ soc₂.write

instance : LT VecRW where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder VecRW :=
  fast_instance% VecRW.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add VecRW where
  add soc₁ soc₂ := ⟨soc₁.read + soc₂.read, soc₁.write + soc₂.write⟩

@[simps]
instance : SMul ℕ VecRW where
  smul n soc := ⟨n • soc.read, n • soc.write⟩

instance : AddCommMonoid VecRW :=
  fast_instance%
    VecRW.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

end VecRW

/--
A cost model for `Vec` queries that counts reads and writes separately
-/
@[simps, grind]
def vecRWModel {α : Type} :
    Model (Vec α) VecRW where
  evalQuery
    | .read a i => a[i]
    | .write a i x => a.set i x
  cost
    | .read _ _ => ⟨1,0⟩
    | .write _ _ _ => ⟨0,1⟩

end VecModel

end Algorithms

end Algolean
