module

public import Algolean.Models.ListDataStructs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
  # Depth First Search
-/

namespace Algolean.Algorithms

open Prog

inductive graphQuery (V : Type) : Type → Type
| neighbors (v : V) : graphQuery V (List V)

def graphModel {V : Type} [LinearOrder V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj] :
    Model (graphQuery V) ℕ where
  evalQuery
  | .neighbors v => (G.neighborFinset v).sort
  cost _ := 1

abbrev dfsQueries (V : Type) : Type → Type :=
    fun β => (Sum (ListADT .lifo V β) (graphQuery V β))

def dfsModel {V : Type} [Fintype V] [LinearOrder V]
  (G : SimpleGraph V) [DecidableRel G.Adj] :
    ModelM (dfsQueries V) (StateM (ListState V)) ℕ :=
  ModelM.sum (@stackModel V) (ModelM.ofModel (graphModel G))

def insertNeighborhood {V : Type} [DecidableEq V] (reached : V → Bool) (neighbors : List V) :
    Prog (ListADT .lifo V) (V → Bool) := do
  match neighbors with
  | .nil => return reached
  | .cons hd tl =>
    if reached hd
    then insertNeighborhood reached tl
    else
      let reached' := fun v => if v = hd then true else reached v
      let _ ←  ListADT.insert hd
      insertNeighborhood reached' tl

def dfsHelperProg {V : Type} [DecidableEq V] (reached : V → Bool) (neighbors : List V) (fuel : ℕ) :
    Prog (ListADT .lifo V) (V → Bool) := do
  match fuel with
  | .zero => return reached
  | .succ m =>
    ← .inl

end Algolean.Algorithms
