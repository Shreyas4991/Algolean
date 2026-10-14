/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sort
public import Algolean.QueryModel

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
