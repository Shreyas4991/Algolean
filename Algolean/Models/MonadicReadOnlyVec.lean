/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.QueryModel


@[expose] public section

/-!
# Query Type for Comparison Search in Lists

In this file we define a query type `VecSearch` for comparison based searching in Lists,
whose sole query `compare` compares the head of the list with a given argument. It
further defines a model `ListSearch.natCost` for this query.

--
## Definitions

- `VecSearch`: A query type for comparison based search in lists.
- `VecSearch.natCost`:  A model for this query with costs in `ℕ`.

-/

namespace Algolean

namespace Algorithms

open Prog Cslib

/--
A query type which provides read only access to a vector. It lets you read the element at an index.
-/
inductive ReadOnlyVec (m : Type → Type) (α : Type) : Type → Type _ where
  | read (a : Vector α n) (i : Fin n) : ReadOnlyVec m α (m α)


/-- A model of the `VecSearch` query type that assigns the cost as the number of queries. -/
@[simps]
def ReadOnlyVec.natCost [Monad m] : Model (ReadOnlyVec m α) ℕ where
  evalQuery
    | .read a i => pure a[i]
  cost _ := 1



section LinearSearch

open ReadOnlyVec in
/-- Linear Search in Lists on top of the `ListSearch` query model. -/
@[simp, grind]
def vecLinearSearch [BEq α] [Monad m] (interp : m α → α) (v : Vector α n) (x : α)
  : Prog (ReadOnlyVec m α) Bool := do
  match n with
  | 0 => return false
  | _ + 1 =>
    let topElem : m α ← FreeM.lift (read v 0)
    if (interp topElem) == x then
      return true
    else
      vecLinearSearch interp (v.tail) x

end LinearSearch

end Algorithms

end Algolean
