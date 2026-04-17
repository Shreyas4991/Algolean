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

In this file we define a query type `ReadOnlyVec` for for read only algorithms
on vectors `ReadOnlyVec.natCost` for this query.

--
## Definitions

- `ReadOnlyVec`: A query type for comparison based search in lists.
- `ReadOnlyVec.natCost`:  A model for this query with costs in `ℕ`.

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
