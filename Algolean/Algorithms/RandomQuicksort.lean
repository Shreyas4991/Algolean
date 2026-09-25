/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.ListComparisonSort
public import Algolean.Models.UniformSample

/-!
# Randomized quicksort of a list

This file defines randomized quicksort in the comparison-query model and proves that it always
returns a sorted permutation of its input. The proof is by `mvcgen` through the support-based
weakest-precondition semantics of `PMF`.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.
- `randomQuicksortModel`: interpret comparisons with a supplied Boolean comparator and
  pivot draws with a supplied sampling model.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
- `randomQuicksort_spec_of_queries`: correctness for any handler satisfying the query contracts.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

namespace Models

open SortOps Std.Do Cslib

/-- Comparison queries and computable finite pivot requests. -/
abbrev RandomQuicksortOps (α : Type) := fun β => Sum (SortOps α β) (UniformSample β)

/-- Interpret comparisons with `le`, charging one per comparison and using `sampling` for draws. -/
def randomQuicksortModel [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) : ModelM (RandomQuicksortOps α) m ℕ :=
  ModelM.sum
    { evalQuery := fun q => pure ((sortModelNat le).evalQuery q)
      cost := (sortModelNat le).cost }
    sampling

/-- Compare two values through the model's Boolean comparator. -/
def queryCmpLE (y p : α) : Prog (RandomQuicksortOps α) Bool :=
  FreeM.lift (.inl (SortOps.cmpLE y p))

/-- Request a pivot index without embedding a probability distribution in the program. -/
def drawPivot (n : Nat) : Prog (RandomQuicksortOps α) (Fin (n + 1)) :=
  FreeM.lift (.inr (.fin n))

/-- Keep the elements of `xs` whose corresponding flag in `bs` is `true`. -/
def keepFlagged (xs : List α) (bs : List Bool) : List α :=
  ((xs.zip bs).filter (·.2)).map Prod.fst

theorem keepFlagged_length_le (xs : List α) (bs : List Bool) :
    (keepFlagged xs bs).length ≤ xs.length :=
  calc (keepFlagged xs bs).length
      = ((xs.zip bs).filter (·.2)).length := by rw [keepFlagged, List.length_map]
    _ ≤ (xs.zip bs).length := List.length_filter_le _ _
    _ ≤ xs.length := by rw [List.length_zip]; exact Nat.min_le_left _ _

/-- Draw a pivot, partition the rest by comparison against it, and sort each side.

Like `mergeSort`, this program obtains its comparator from the model. Using
`randomQuicksortModel le UniformSample.pmfModel` gives uniform randomized semantics.
-/
def randomQuicksort (l : List α) : Prog (RandomQuicksortOps α) (List α) :=
  match l with
  | [] => pure []
  | x :: xs => do
    let r ← drawPivot xs.length
    let pivot := (x :: xs).get r
    let rest := (x :: xs).eraseIdx r
    let flags ← rest.mapM (fun y ↦ queryCmpLE y pivot)
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

variable (le : α → α → Bool)

set_option mvcgen.warning false in
/-- A comparison query returns the supplied comparator's answer. -/
theorem query_cmpLE_spec (y p : α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃⌜True⌝⦄
      queryCmpLE y p
      ⦃⇓b => ⌜b = le y p⌝⦄ := by
  mvcgen [queryCmpLE]
  intro b hb
  exact (PMF.mem_support_pure_iff (le y p) b).mp hb

set_option mvcgen.warning false in
/-- Comparing every element against `p` yields the flags `xs.map (le · p)`. -/
theorem mapM_cmpLE_spec [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (y p : α), ⦃⌜True⌝⦄ queryCmpLE y p ⦃⇓b => ⌜b = le y p⌝⦄)
    (p : α) (xs : List α) :
    ⦃⌜True⌝⦄ (xs.mapM (fun y ↦ queryCmpLE y p))
      ⦃⇓ flags => ⌜flags = xs.map (fun y ↦ le y p)⌝⦄ := by
  induction xs with
  | nil => mvcgen
  | cons a as ih =>
    rw [List.mapM_cons]
    mvcgen [hcmp, ih]
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
private lemma sorted_glue [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (pivot : α) (rest sl sr : List α)
    (hslp : sl.Perm (rest.filter (fun y ↦ le y pivot)))
    (hsls : sl.Pairwise (fun a b => le a b = true))
    (hsrp : sr.Perm (rest.filter (fun y ↦ !le y pivot)))
    (hsrs : sr.Pairwise (fun a b => le a b = true)) :
    (sl ++ [pivot] ++ sr).Pairwise (fun a b => le a b = true) := by
  have hle : ∀ a ∈ sl, le a pivot = true :=
    fun a ha ↦ (List.mem_filter.mp (hslp.mem_iff.mp ha)).2
  have hge : ∀ b ∈ sr, le pivot b = true := by
    intro b hb
    have h2 := (List.mem_filter.mp (hsrp.mem_iff.mp hb)).2
    have ht := Std.Total.total (r := fun a b => le a b = true) pivot b
    simp_all
  have hcross : ∀ a ∈ sl, ∀ c ∈ pivot :: sr, le a c = true := by
    intro a ha c hc
    cases List.mem_cons.mp hc with
    | inl h => exact h ▸ hle a ha
    | inr h =>
      exact IsTrans.trans (r := fun a b => le a b = true)
        a pivot c (hle a ha) (hge c h)
  rw [List.append_assoc, List.singleton_append, List.pairwise_append]
  exact ⟨hsls, List.pairwise_cons.mpr ⟨hge, hsrs⟩, hcross⟩

/-- The glued list is a sorted permutation of `pivot :: rest`. -/
private lemma quicksort_combine [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (pivot : α) (rest sl sr : List α)
    (hslp : sl.Perm (rest.filter (fun y ↦ le y pivot)))
    (hsls : sl.Pairwise (fun a b => le a b = true))
    (hsrp : sr.Perm (rest.filter (fun y ↦ !le y pivot)))
    (hsrs : sr.Pairwise (fun a b => le a b = true)) :
    (sl ++ [pivot] ++ sr).Perm (pivot :: rest) ∧
      (sl ++ [pivot] ++ sr).Pairwise (fun a b => le a b = true) :=
  ⟨partition_glue_perm pivot _ rest sl sr hslp hsrp,
    sorted_glue le pivot rest sl sr hslp hsls hsrp hsrs⟩

set_option mvcgen.warning false in
/-- Correctness only needs accurate comparisons and a pivot in the requested finite range. -/
theorem randomQuicksort_spec_of_queries
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (hcmp : ∀ (y p : α), ⦃⌜True⌝⦄ queryCmpLE y p ⦃⇓b => ⌜b = le y p⌝⦄)
    (hdraw : ∀ n, ⦃⌜True⌝⦄ (drawPivot n : Prog (RandomQuicksortOps α) _)
      ⦃⇓_ => ⌜True⌝⦄)
    (l : List α) :
    ⦃⌜True⌝⦄ randomQuicksort l
      ⦃⇓ out => ⌜out.Perm l ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
  fun_induction randomQuicksort l
  next => mvcgen; exact ⟨.refl _, .nil⟩
  next x xs ih_lt ih_rt =>
    have hflags := mapM_cmpLE_spec le hcmp
    mvcgen [hdraw]
    rename_i r pivot rest
    dsimp +zetaDelta only
    mvcgen [hflags, ih_lt, ih_rt]
    rename_i flags hflags sl hsl sr hsr
    subst hflags
    simp only [keepFlagged_map, List.map_map, Function.comp_def] at hsl hsr
    have hc := quicksort_combine le ((x :: xs).get r) ((x :: xs).eraseIdx ↑r) sl sr
      hsl.1 hsl.2 hsr.1 hsr.2
    exact ⟨hc.1.trans (List.getElem_cons_eraseIdx_perm r.isLt), hc.2⟩

set_option mvcgen.warning false in
/-- Uniform randomized quicksort returns a sorted permutation under the supplied comparator. -/
theorem randomQuicksort_spec [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (l : List α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃⌜True⌝⦄ randomQuicksort l
      ⦃⇓ out => ⌜out.Perm l ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
  apply @randomQuicksort_spec_of_queries α le
    (randomQuicksortModel le UniformSample.pmfModel).hasHandler _ _
    (query_cmpLE_spec le)
  intro n
  mvcgen [drawPivot]
  exact fun _ _ => True.intro

end Correctness

end Models

end Algorithms

end Algolean
