/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.QueryModel

@[expose] public section

/-!
# Query Type for Comparisons

In this file we define a query type `Comparison` for comparison based algorithms, whose sole query
`compare` compares two arguments. It further defines a model `Comparison.natCost` for this query.
--

## Definitions

- `Comparison`: A query type for comparison based algorithms.
- `Comparison.natCost`:  A model for this query with costs in `ℕ`.
- `PatternSearchAll`: Pattern searching definition for finding all matches.

-/

namespace Algolean

namespace Algorithms

open Prog

/--
A query type for comparing elements. It supports exactly one query
`compare x y` which returns `true` if `x` is equal to `y`
and returns `false` otherwise.
-/
inductive Comparison (α : Type*) : Type → Type _ where
  | compare (x y : α) : Comparison α Bool


/-- A model of the `Comparison` query type that assigns the cost as the number of queries. -/
@[simps]
def Comparison.natCost [BEq α] : Model (Comparison α) ℕ where
  evalQuery
    | .compare x y => x == y
  cost _ := 1

/--
`PatternSearchAll pat txt` returns all starting positions in `txt` such that
`pat` is a prefix of `txt` starting there, in increasing order.

For the empty pattern, this returns every position inside the text
`0, 1, ..., txt.length - 1`.

TODO: move definition
-/
def PatternSearchAll [BEq α] (pat txt : List α) : List Nat :=
  (List.range txt.length).filter fun i => pat.isPrefixOf (txt.drop i)

end Algorithms

end Algolean
