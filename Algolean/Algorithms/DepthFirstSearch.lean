module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Int.ConditionallyCompleteOrder

@[expose] public section

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
    else depthFirstSearch.helper G ((G.neighborSet hd).toFinset.sort ++ tl) (visited ∪ {hd})
termination_by (n - visited.card, sizeOf stack)
decreasing_by
  · grind
  · have := card_finset_fin_le (visited ∪ {hd})
    grind

def depthFirstSearch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    Finset (Fin n) :=
  depthFirstSearch.helper G [v] ∅

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
        simp only [List.mem_append, Finset.mem_sort, Set.mem_toFinset, SimpleGraph.mem_neighborSet]
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
