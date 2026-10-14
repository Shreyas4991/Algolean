/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Algolean.Models.Graphs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!

# Depth first search

This file defines depth first search on undirected graphs and proves correctness and time bounds
under the graphAccessModel. We assume that the vertices of the graph are natural numbers.

## Main definitions
- `reachableVertices` : Given a vertex v all vertices u that are connected via a path to v.
- `depthFirstSearch` : Depth first searching returning for a vertex all reachable vertices in
    the graph.

## Main results
- `depthFirstSearch_eq_reachableVertices` : Dfs finds all reachable vertices given a vertex v.
- `depthFirstSearchProg_time` : The number of steps is bounded by twice the number of edges.

-/

@[expose] public section

namespace Algolean.Algorithms

def reachableVertices {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  {(u : Fin n) | G.Reachable v u}

def depthFirstSearch.helper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (stack : List (Fin n)) (visited : Finset (Fin n)) : Finset (Fin n) :=
  match stack with
  | .nil => visited
  | .cons hd tl =>
    if h : hd ∈ visited
    then depthFirstSearch.helper G tl visited
    else depthFirstSearch.helper G ((G.neighborFinset hd).sort ++ tl) (visited ∪ {hd})
termination_by (n - visited.card, sizeOf stack)
decreasing_by
  · grind
  · have := card_finset_fin_le (visited ∪ {hd})
    grind

def depthFirstSearch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  depthFirstSearch.helper G [v] ∅

section correctness

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma reachableVertices_eq_iff {v : Fin n} {S : Finset (Fin n)} :
    S = reachableVertices G v ↔
      v ∈ S ∧ (∀ u ∈ S, G.Reachable v u) ∧ ∀ u w, u ∈ S → G.Adj u w → w ∈ S := by
  constructor
  · intro h
    simp only [h, reachableVertices, Finset.mem_filter, Finset.mem_univ, SimpleGraph.Reachable.rfl,
      and_self, true_and, imp_self, implies_true]
    intro u w h₁ h₂
    apply SimpleGraph.Reachable.trans h₁ (SimpleGraph.Adj.reachable h₂)
  · rintro ⟨h₁, h₂, h₃⟩
    simp only [reachableVertices, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    intro u
    refine Iff.intro (h₂ u) ?_
    simp only [SimpleGraph.Reachable, Nonempty.forall]
    intro p
    induction p with
    | nil => assumption
    | cons h p ih =>
      expose_names
      apply ih (h₃ _ _ h₁ h)
      intro u' hu'
      apply SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm (SimpleGraph.Adj.reachable h))
        (h₂ u' hu')

lemma finset_eq_univ_of_n_sub_card_eq_zero {n : ℕ} {S : Finset (Fin n)} (h : n - S.card = 0) :
    S = Finset.univ := by
  rw [Nat.sub_eq_zero_iff_le] at h
  have h' := card_finset_fin_le S
  simp [← Finset.card_eq_iff_eq_univ, Nat.le_antisymm h h']


lemma depthFirstSearch.helper_univ_eq_univ {stack : List (Fin n)} :
    depthFirstSearch.helper G stack Finset.univ = Finset.univ := by
  induction stack with
  | nil => simp [helper]
  | cons hd tl ih => simp [helper, ih]

lemma depthFirstSearch.helper_returns_superset {stack : List (Fin n)} {visited : Finset (Fin n)} :
    visited ⊆ depthFirstSearch.helper G stack visited := by
  induction h : n - visited.card generalizing stack visited with
  | zero =>
    simp [finset_eq_univ_of_n_sub_card_eq_zero h, helper_univ_eq_univ]
  | succ m ih =>
    induction stack with
    | nil => simp [helper]
    | cons hd tl =>
      grind [helper]

lemma depthFirstSearch.helper_contains_stack {v : Fin n} {stack : List (Fin n)}
  {visited : Finset (Fin n)} (hv : v ∈ stack) :
    v ∈ depthFirstSearch.helper G stack visited := by
  induction h : n - visited.card generalizing stack visited with
  | zero =>
    simp [finset_eq_univ_of_n_sub_card_eq_zero h, helper_univ_eq_univ]
  | succ m ih =>
      induction stack with
      | nil => simp at hv
      | cons hd tl ih' =>
        simp only [List.mem_cons] at hv
        simp only [helper, Finset.union_singleton, dite_eq_ite]
        split
        · cases hv with
          | inl hv =>
            rw [hv]
            apply helper_returns_superset
            assumption
          | inr hv => apply ih' hv
        · cases hv with
          | inl hv =>
            rw [hv]
            apply helper_returns_superset
            simp
          | inr hv =>
            apply ih (by simp[hv]) (by grind)

lemma depthFirstSearch.helper_contains_reachable_of_contains_reachable {v : Fin n}
  {stack : List (Fin n)} {visited : Finset (Fin n)} (h₁ : ∀ u ∈ visited, G.Reachable v u)
  (h₂ : ∀ u ∈ stack, G.Reachable v u) :
    ∀ u ∈ (depthFirstSearch.helper G stack visited), G.Reachable v u := by
  induction h : n - visited.card generalizing stack visited with
  | zero =>
    simp only [finset_eq_univ_of_n_sub_card_eq_zero h, Finset.mem_univ, forall_const,
      helper_univ_eq_univ] at ⊢ h₁
    apply h₁
  | succ m ih =>
    induction stack generalizing visited with
    | nil => simpa [helper]
    | cons hd tl ih' =>
      simp only [helper, Finset.union_singleton, dite_eq_ite]
      split
      · intro u hu
        apply ih' h₁ (by grind) h u hu
      · refine ih (by grind) ?_ (by grind)
        simp only [List.mem_append, Finset.mem_sort, SimpleGraph.mem_neighborFinset]
        intro u hu
        cases hu with
        | inl hu =>
          specialize h₂ hd (by simp)
          apply SimpleGraph.Reachable.trans h₂ (SimpleGraph.Adj.reachable hu)
        | inr hu =>
          apply h₂
          simp [hu]

lemma depthFirstSearch.helper_closed_under_neighbor_of_closed_under_neighbor {stack : List (Fin n)}
  {visited : Finset (Fin n)} (h : ∀ u v, v ∈ visited → G.Adj v u → u ∈ visited ∨ u ∈ stack) :
    ∀ u v, v ∈ depthFirstSearch.helper G stack visited → G.Adj v u
      → u ∈ depthFirstSearch.helper G stack visited := by
  induction h' : n - visited.card generalizing stack visited with
  | zero =>
    simp [finset_eq_univ_of_n_sub_card_eq_zero h', helper_univ_eq_univ]
  | succ m ih =>
    induction stack generalizing visited with
    | nil =>
      simp only [List.not_mem_nil, or_false] at h
      simpa [helper]
    | cons hd tl ih' =>
      simp only [helper, Finset.union_singleton, dite_eq_ite]
      split
      · apply ih' _ h'
        grind
      · intro u v h₁ h₂
        apply ih _ (by grind) u v h₁ h₂
        simp
        grind

theorem depthFirstSearch_eq_reachableVertices {v : Fin n} :
    depthFirstSearch G v = reachableVertices G v := by
  simp only [depthFirstSearch, reachableVertices_eq_iff, List.mem_cons, List.not_mem_nil, or_false,
    depthFirstSearch.helper_contains_stack, true_and]
  constructor
  · apply depthFirstSearch.helper_contains_reachable_of_contains_reachable
    · simp
    · simp
  · intro u w h₁ h₂
    apply depthFirstSearch.helper_closed_under_neighbor_of_closed_under_neighbor (by simp) w u h₁ h₂

end correctness

open Prog

def getNeighborhood.helper {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : (Fin n))
  (i : ℕ) (hi : i < G.degree v) :
    Prog (graphAccessQuery G) (List (Fin n)) := do
  let element ← (graphAccessQuery.getNeighbor v ⟨i, hi⟩)
  if hi' : i + 1 < G.degree v
  then
    return element :: (← getNeighborhood.helper G v (i+1) hi')
  else
    return [element]
termination_by G.degree v - i
decreasing_by
  lia

def getNeighborhood {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : (Fin n)) :
    Prog (graphAccessQuery G) (List (Fin n)) := do
  if h : 0 < (G.neighborFinset v).card
  then getNeighborhood.helper G v 0 h
  else return []

def depthFirstSearch.helperProg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  (stack : List (Fin n)) (visited : Finset (Fin n)) :
    Prog (graphAccessQuery G) (Finset (Fin n)) := do
  match stack with
  | .nil => return visited
  | .cons hd tl =>
    if hd ∈ visited
    then depthFirstSearch.helperProg G tl visited
    else depthFirstSearch.helperProg G ((← getNeighborhood G hd) ++ tl) (visited ∪ {hd})
termination_by (n - visited.card, sizeOf stack)
decreasing_by
  · grind
  · have := card_finset_fin_le (visited ∪ {hd})
    grind

def depthFirstSearchProg {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Prog (graphAccessQuery G) (Finset (Fin n)) :=
  depthFirstSearch.helperProg G [v] ∅

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

lemma getNeighborhood.helper_eval {v : Fin n} {i : ℕ} {hi : i < G.degree v} :
    (getNeighborhood.helper G v i hi).eval (graphAccessModel G)
      = (G.neighborFinset v).sort.drop i := by
  induction h : G.degree v - i generalizing i with
  | zero => grind
  | succ m ih =>
    unfold helper
    simp only [bind_pure_comp, eval_bind, eval_lift, graphAccessModel_evalQuery, Fin.getElem_fin]
    by_cases h' : i+1 < G.degree v
    · simp only [h', ↓reduceDIte, eval_map]
      rw [ih (by lia)]
      simp
    · have hi' : i = G.degree v - 1 := by lia
      simp only [h', ↓reduceDIte, eval_pure]
      apply List.ext_get
      · simp [hi']
        lia
      · simp

lemma getNeighborhood.helper_cost {v : Fin n} {i : ℕ} {hi : i < G.degree v} :
    (getNeighborhood.helper G v i hi).time (graphAccessModel G) = G.degree v - i := by
  induction h : G.degree v - i generalizing i with
  | zero => grind
  | succ m ih =>
    unfold helper
    simp only [bind_pure_comp, time_bind, time_lift, graphAccessModel_cost, eval_lift,
      graphAccessModel_evalQuery, Fin.getElem_fin]
    by_cases h' : i+1 < G.degree v
    · simp only [h', ↓reduceDIte, time_map]
      rw [ih, Nat.add_comm]
      lia
    · simp [h']
      lia

lemma getNeighborhood_eval {v : (Fin n)} :
    (getNeighborhood G v).eval (graphAccessModel G) = (G.neighborFinset v).sort := by
  simp [getNeighborhood]
  by_cases h : 0 < G.degree v
  · simp [h, getNeighborhood.helper_eval]
  · simp [h]
    simp only [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_pos,
      Finset.not_nonempty_iff_eq_empty] at h
    simp [h]

lemma getNeighborhood_cost {v : (Fin n)} :
    (getNeighborhood G v).time (graphAccessModel G) = G.degree v := by
  simp [getNeighborhood]
  by_cases h : 0 < G.degree v
  · simp [h, getNeighborhood.helper_cost]
  · simp [h]
    lia

lemma depthFirstSearch.helperProg_eval {stack : List (Fin n)} {visited : Finset (Fin n)} :
    (depthFirstSearch.helperProg G stack visited).eval (graphAccessModel G) =
      depthFirstSearch.helper G stack visited := by
  induction h : n - visited.card generalizing stack visited with
  | zero =>
    induction stack generalizing visited with
    | nil => simp [helperProg, helper]
    | cons hd tl ih =>
      simpa [helperProg, helper, finset_eq_univ_of_n_sub_card_eq_zero, h] using ih h
  | succ m ih =>
    induction stack generalizing visited with
    | nil => simp [helperProg, helper]
    | cons hd tl ih' =>
      simp only [helperProg, Finset.union_singleton, helper, dite_eq_ite]
      split
      · apply ih' h
      · simp only [eval_bind, getNeighborhood_eval]
        apply ih
        simp [Finset.card_insert_eq_ite]
        lia

lemma depthFirstSearch.helperProg_time {stack : List (Fin n)} {visited : Finset (Fin n)} :
    (depthFirstSearch.helperProg G stack visited).time (graphAccessModel G) ≤
      ∑ (v ∉ visited), G.degree v := by
  induction h : n - visited.card generalizing stack visited with
  | zero =>
    induction stack with
    | nil => simp [helperProg]
    | cons hd tl ih =>
      simp [finset_eq_univ_of_n_sub_card_eq_zero, h] at ih
      simp [helperProg, finset_eq_univ_of_n_sub_card_eq_zero, h, ih]
  | succ m ih =>
    induction stack generalizing visited with
    | nil => simp [helperProg]
    | cons hd tl ih' =>
      simp only [helperProg, Finset.union_singleton]
      split
      · apply ih' h
      · simp only [time_bind, getNeighborhood_cost]
        grw [ih]
        · simp only [Finset.compl_insert]
          rw [Finset.add_sum_erase (f := fun v => G.degree v)]
          apply Finset.mem_compl.mpr
          assumption
        · simp [Finset.card_insert_eq_ite]
          lia

theorem depthFirstSearchProg_eval {v : Fin n} :
    (depthFirstSearchProg G v).eval (graphAccessModel G) = reachableVertices G v := by
  simp [← depthFirstSearch_eq_reachableVertices, depthFirstSearch, depthFirstSearchProg,
    depthFirstSearch.helperProg_eval]

theorem depthFirstSearchProg_time {v : Fin n} :
    (depthFirstSearchProg G v).time (graphAccessModel G) ≤ 2 * G.edgeFinset.card := by
  simp only [depthFirstSearchProg, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  grw [depthFirstSearch.helperProg_time]
  simp

end Algolean.Algorithms
