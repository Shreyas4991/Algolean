module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Sort

@[expose] public section

def depthFirstSearch.helper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (stack : List (Fin n)) (visited : Finset (Fin n)) : Finset (Fin n) :=
  match stack with
  | .nil => visited
  | .cons hd tl =>
    if h : hd ∈ visited
    then visited
    else depthFirstSearch.helper G (stack ++ (G.neighborSet hd).toFinset.sort) (visited ∪ {hd})
termination_by n - visited.card
decreasing_by
  have := card_finset_fin_le (visited ∪ {hd})
  grind

def depthFirstSearch {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  depthFirstSearch.helper G [v] ∅
