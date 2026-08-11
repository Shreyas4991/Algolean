/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.ListComparisonSort
public import Algolean.Models.RandomSample
public import Mathlib.Probability.Distributions.Uniform

/-!
# Randomized quicksort of a list

This file defines randomized quicksort in the comparison-query model and proves that it always
returns a sorted permutation of its input. The proof is by `mvcgen` through the support-based
weakest-precondition semantics of `PMF`.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

namespace Models

open SortOps Std.Do

/-- Keep the elements of `xs` whose corresponding flag in `bs` is `true`. -/
def keepFlagged (xs : List α) (bs : List Bool) : List α :=
  ((xs.zip bs).filter (·.2)).map Prod.fst

theorem keepFlagged_length_le (xs : List α) (bs : List Bool) :
    (keepFlagged xs bs).length ≤ xs.length :=
  calc (keepFlagged xs bs).length
      = ((xs.zip bs).filter (·.2)).length := by rw [keepFlagged, List.length_map]
    _ ≤ (xs.zip bs).length := List.length_filter_le _ _
    _ ≤ xs.length := by rw [List.length_zip]; exact Nat.min_le_left _ _

/-- Draw a pivot uniformly, partition the rest by comparison against it, sort each side. -/
noncomputable def randomQuicksort (l : List α) :
    Prog (RandomizeQuery (SortOps α)) (List α) :=
  match l with
  | [] => pure []
  | x :: xs => do
    let r ← RandomizeQuery.draw (PMF.uniformOfFintype (Fin (xs.length + 1)))
    let pivot := (x :: xs).get r
    let rest := (x :: xs).eraseIdx r
    let flags ← rest.mapM (fun y ↦ RandomizeQuery.query (SortOps.cmpLE y pivot))
    let lt := keepFlagged rest flags
    let rt := keepFlagged rest (flags.map (!·))
    let sortedlt ← randomQuicksort lt
    let sortedrt ← randomQuicksort rt
    pure (sortedlt ++ [pivot] ++ sortedrt)
termination_by l.length
decreasing_by
  all_goals
    calc _ ≤ rest.length := keepFlagged_length_le _ _
      _ = xs.length := by simp [rest, List.length_eraseIdx, r.isLt]
      _ < (x :: xs).length := by simp

section Correctness

variable {α : Type}

/-- The order relation `x ≤ y` under `[Ord α]`. -/
local notation:50 a:51 " ≼ " b:51 => Ordering.isLE (compare a b) = true

set_option mvcgen.warning false in
/-- A comparison query returns whether `y ≤ p` under the `Ord` model. -/
theorem query_cmpLE_spec [Ord α] (y p : α) :
    ⦃⌜True⌝⦄
      (RandomizeQuery.query (SortOps.cmpLE y p) : Prog (RandomizeQuery (SortOps α)) Bool)
      ⦃⇓ b => ⌜b = (compare y p).isLE⌝⦄ := by
  mvcgen [RandomizeQuery.query]
  intro b hb
  exact (PMF.mem_support_pure_iff ((compare y p).isLE) b).mp hb

set_option mvcgen.warning false in
/-- Comparing every element of `xs` against `p` yields the flags `xs.map (compare · p |>.isLE)`. -/
theorem mapM_cmpLE_spec [Ord α] (p : α) (xs : List α) :
    ⦃⌜True⌝⦄ (xs.mapM (fun y ↦ RandomizeQuery.query (SortOps.cmpLE y p))
        : Prog (RandomizeQuery (SortOps α)) (List Bool))
      ⦃⇓ flags => ⌜flags = xs.map (fun y ↦ (compare y p).isLE)⌝⦄ := by
  induction xs with
  | nil => mvcgen
  | cons a as ih =>
    rw [List.mapM_cons]
    mvcgen [query_cmpLE_spec, ih]
    simp_all

/-- Keeping the elements flagged by `xs.map g` is filtering by `g`. -/
private lemma keepFlagged_map (g : α → Bool) (xs : List α) :
    keepFlagged xs (xs.map g) = xs.filter g := by
  unfold keepFlagged
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
    cases hg : g a <;> simp_all

/-- Gluing `sl`, `sr` (permutations of the two filter-partitions of `rest`) around `pivot` gives a
permutation of `pivot :: rest`. -/
private lemma partition_glue_perm (pivot : α) (g : α → Bool) (rest sl sr : List α)
    (hslp : sl.Perm (rest.filter g)) (hsrp : sr.Perm (rest.filter (fun y ↦ !g y))) :
    (sl ++ [pivot] ++ sr).Perm (pivot :: rest) := by
  have h3 :
      (rest.filter g ++ [pivot] ++ rest.filter (fun y ↦ !g y)).Perm (pivot :: rest) := by
    rw [List.append_assoc]
    exact List.perm_middle.trans ((List.filter_append_perm g rest).cons pivot)
  exact (((hslp.append_right [pivot]).append_right sr).trans
    (List.Perm.append_left _ hsrp)).trans h3

/-- The glued list is sorted: each half is sorted and lies on its side of the pivot. -/
private lemma sorted_glue [Ord α] [Std.TransCmp (compare : α → α → Ordering)]
    (pivot : α) (rest sl sr : List α)
    (hslp : sl.Perm (rest.filter (fun y ↦ (compare y pivot).isLE)))
    (hsls : sl.Pairwise (· ≼ ·))
    (hsrp : sr.Perm (rest.filter (fun y ↦ !(compare y pivot).isLE)))
    (hsrs : sr.Pairwise (· ≼ ·)) :
    (sl ++ [pivot] ++ sr).Pairwise (· ≼ ·) := by
  have hle : ∀ a ∈ sl, a ≼ pivot :=
    fun a ha ↦ (List.mem_filter.mp (hslp.mem_iff.mp ha)).2
  have hge : ∀ b ∈ sr, pivot ≼ b := by
    intro b hb
    have h2 := (List.mem_filter.mp (hsrp.mem_iff.mp hb)).2
    rw [(Std.OrientedCmp.eq_swap : compare pivot b = _)]
    cases h : compare b pivot <;> simp_all [Ordering.swap, Ordering.isLE]
  have hcross : ∀ a ∈ sl, ∀ c ∈ pivot :: sr, a ≼ c := by
    intro a ha c hc
    cases List.mem_cons.mp hc with
    | inl h => exact h ▸ hle a ha
    | inr h => exact Std.TransCmp.isLE_trans (hle a ha) (hge c h)
  rw [List.append_assoc, List.singleton_append, List.pairwise_append]
  exact ⟨hsls, List.pairwise_cons.mpr ⟨hge, hsrs⟩, hcross⟩

/-- The glued list is a sorted permutation of `pivot :: rest`. -/
private lemma quicksort_combine [Ord α] [Std.TransCmp (compare : α → α → Ordering)]
    (pivot : α) (rest sl sr : List α)
    (hslp : sl.Perm (rest.filter (fun y ↦ (compare y pivot).isLE)))
    (hsls : sl.Pairwise (· ≼ ·))
    (hsrp : sr.Perm (rest.filter (fun y ↦ !(compare y pivot).isLE)))
    (hsrs : sr.Pairwise (· ≼ ·)) :
    (sl ++ [pivot] ++ sr).Perm (pivot :: rest) ∧ (sl ++ [pivot] ++ sr).Pairwise (· ≼ ·) :=
  ⟨partition_glue_perm pivot _ rest sl sr hslp hsrp,
    sorted_glue pivot rest sl sr hslp hsls hsrp hsrs⟩

set_option mvcgen.warning false in
/-- Randomized quicksort always returns a sorted permutation of its input. -/
theorem randomQuicksort_spec [Ord α] [Std.TransCmp (compare : α → α → Ordering)]
    (l : List α) :
    ⦃⌜True⌝⦄ randomQuicksort l
      ⦃⇓ out => ⌜out.Perm l ∧ out.Pairwise (· ≼ ·)⌝⦄ := by
  fun_induction randomQuicksort l
  next => mvcgen; exact ⟨.refl _, .nil⟩
  next x xs ih_lt ih_rt =>
    mvcgen [RandomizeQuery.draw]
    intro r _hr
    mvcgen [mapM_cmpLE_spec, ih_lt, ih_rt]
    rename_i flags hflags sl hsl sr hsr
    subst hflags
    simp only [keepFlagged_map, List.map_map, Function.comp_def] at hsl hsr
    have hc := quicksort_combine ((x :: xs).get r) ((x :: xs).eraseIdx ↑r) sl sr
      hsl.1 hsl.2 hsr.1 hsr.2
    exact ⟨hc.1.trans (List.getElem_cons_eraseIdx_perm r.isLt), hc.2⟩

end Correctness

end Models

end Algorithms

end Algolean
