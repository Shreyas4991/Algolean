/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sort
public import Algolean.QueryModel

/-!
# QueryType for graph algorithms

This file contains queries and models to reason about graph algorithms. We assume that the vertices
the graphs are natural numbers so that we can sort the neighbors.

## Main definitions
- `graphAccessQuery` : This query offers the operation of getting the i-th neighbor of a vertex
    assuming that this neighbor exists.
- `graphAccessModel`: This model returns the i-th neighbor based on the position in the neighbor
    list for a cost of 1.
-/

@[expose] public section

namespace Algolean.Algorithms

open Prog

inductive graphAccessQuery {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Type → Type
| getNeighbor (v : Fin n) (i : Fin (G.degree v)) : graphAccessQuery G (Fin n)

@[simps]
def graphAccessModel {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Model (graphAccessQuery G) ℕ where
  evalQuery
  | .getNeighbor v i => (G.neighborFinset v).sort[i]
  cost _ := 1

end Algolean.Algorithms
