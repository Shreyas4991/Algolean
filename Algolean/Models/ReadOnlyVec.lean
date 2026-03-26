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

open Prog

/--
A query type which provides read only access to a vector. It lets you read the element at an index.
-/
inductive ReadOnlyVec (α : Type) : Type → Type _ where
  | read (a : Vector α n) (i : Fin n) : ReadOnlyVec α α


/-- A model of the `VecSearch` query type that assigns the cost as the number of queries. -/
@[simps]
def ReadOnlyVec.natCost : Model (ReadOnlyVec α) ℕ where
  evalQuery
    | .read a i => a[i]
  cost _ := 1

end Algorithms

end Algolean
