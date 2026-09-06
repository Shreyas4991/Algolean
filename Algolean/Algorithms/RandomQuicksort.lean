/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.ListComparisonSort
public import Algolean.Models.UniformSample
public import Algolean.QueryComposition
public import Batteries.Data.Array.Pairwise

/-!
# Randomized quicksort with Hoare partitioning

This file defines randomized quicksort in the comparison-query model and proves that it always
returns a sorted permutation of its input. The proof is by `mvcgen` through the support-based
weakest-precondition semantics of `PMF`.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.
- `hoarePartition`: partition using two inward scans, stopping on equivalent elements.
- `randomQuicksortModel`: interpret comparisons with a supplied Boolean comparator and
  pivot draws with a supplied sampling model.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
- `randomQuicksort_spec_of_queries`: correctness for any handler satisfying the query contracts.
- `hoarePartition_spec`: the two groups lie weakly on opposite sides of the pivot.
- `hoarePartition_costM`: partitioning costs exactly one comparison per non-pivot element.
- `hoarePartition_balanced_spec`: comparator-equivalent inputs split evenly.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

namespace Models

open SortOps Std.Do Cslib

/-- Comparison queries and computable finite pivot requests. -/
abbrev RandomQuicksortOps (α : Type) := compositeQuery (SortOps α) UniformSample

/-- Interpret comparisons with `le`, charging one per comparison and using `sampling` for draws.

`randomQuicksortModel le UniformSample.pmfModel` is the probabilistic model. Its per-query costs
are natural numbers; `(randomQuicksort xs).costM (randomQuicksortModel le UniformSample.pmfModel)`
is the `PMF ℕ` of total comparison counts.
-/
def randomQuicksortModel [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) : ModelM (RandomQuicksortOps α) m ℕ :=
  ModelM.sum
    { evalQuery := fun q => pure ((sortModelNat le).evalQuery q)
      cost := (sortModelNat le).cost }
    sampling

@[simp] theorem randomQuicksortModel_evalQuery_cmpLE [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (x y : α) :
    (randomQuicksortModel le sampling).evalQuery (.inl (.cmpLE x y)) = pure (le x y) := rfl

@[simp] theorem randomQuicksortModel_cost_cmpLE [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (x y : α) :
    (randomQuicksortModel le sampling).cost (.inl (.cmpLE x y)) = 1 := rfl

/-- Compare two values through the model's Boolean comparator. -/
def queryCmpLE (y p : α) : Prog (RandomQuicksortOps α) Bool :=
  FreeM.lift (.inl (SortOps.cmpLE y p))

/-- Request a pivot index without embedding a probability distribution in the program. -/
def drawPivot (n : Nat) : Prog (RandomQuicksortOps α) (Fin (n + 1)) :=
  FreeM.lift (.inr (.fin n))

/-- A permuted array with a reserved pivot in its final slot and two recursive partition views. -/
structure HoarePartition (xs : Array α) (pivot : α) where
  /-- The array after exchanging stopped scan endpoints. -/
  array : Array α
  /-- The left partition ends here; the right partition starts here. -/
  split : Fin array.size
  /-- Partitioning preserves the input elements. -/
  perm : array.Perm xs
  /-- The reserved final slot still contains the selected pivot. -/
  pivot_eq : array[array.size - 1]'(by have := split.isLt; lia) = pivot

namespace HoarePartition

variable {α : Type} {xs ys : Array α} {pivot : α}

/-- Transport the input permutation without changing the partitioned array or boundary. -/
@[simps] def cast (h : xs.Perm ys) (p : HoarePartition xs pivot) : HoarePartition ys pivot :=
  ⟨p.array, p.split, p.perm.trans h, p.pivot_eq⟩

/-- The prefix view, sharing the partitioned array. -/
def left (p : HoarePartition xs pivot) : Subarray α := p.array[*...p.split.val]

/-- The right view, ending before the reserved pivot slot. -/
def right (p : HoarePartition xs pivot) : Subarray α := p.array[p.split.val...(p.array.size - 1)]

/-- The partition views and reserved pivot reconstruct the entire array. -/
theorem parts_eq (p : HoarePartition xs pivot) :
    (p.left.toArray ++ p.right.toArray).push pivot = p.array := by
  have hb : p.split.val ≤ p.array.size - 1 := by have := p.split.isLt; lia
  simp only [left, right, Array.toArray_mkSlice_rio, Array.toArray_mkSlice_rco,
    Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right hb]
  have hn : p.array.size - 1 + 1 = p.array.size := by have := p.split.isLt; lia
  calc
    _ = (p.array.extract 0 (p.array.size - 1)).push p.array[p.array.size - 1] :=
      congrArg (fun x => (p.array.extract 0 (p.array.size - 1)).push x) p.pivot_eq.symm
    _ = p.array := by
      rw [Array.push_extract_getElem (by have := p.split.isLt; lia)]
      simp [hn]

/-- Joining the two views around the pivot preserves the original input. -/
theorem parts_perm (p : HoarePartition xs pivot) :
    (p.left.toArray ++ #[pivot] ++ p.right.toArray).Perm xs := by
  have hm : (p.left.toArray ++ #[pivot] ++ p.right.toArray).Perm
      ((p.left.toArray ++ p.right.toArray).push pivot) := by
    apply Array.Perm.of_toList_perm
    simpa [List.append_assoc] using
      ((List.perm_append_singleton pivot p.right.toList).symm.append_left p.left.toList)
  rw [p.parts_eq] at hm
  exact hm.trans p.perm

/-- Scan `[lo, hi)` from both ends, swapping endpoints when both scans stop.

When `stopped` is true, the left endpoint has already answered `le pivot x = true`.
If the scans meet, that already-compared element belongs to the right partition.
The strict upper bound keeps the reserved final slot outside the scan. -/
def loop (pivot : α) (a : Array α) (lo hi : Nat) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot)
    (stopped : Bool) : Prog (RandomQuicksortOps α) (HoarePartition a pivot) := do
  if h : lo < hi then
    let x := a[lo]'(by lia)
    if stopped then
      if hp : lo + 1 < hi then
        let y := a[hi - 1]'(by lia)
        if ← queryCmpLE y pivot then
          let p ← loop pivot (a.swap lo (hi - 1) (by lia) (by lia))
            (lo + 1) (hi - 1) (by lia) (by simp; lia) (by
              simpa [Array.getElem_swap, show a.size - 1 ≠ lo by lia,
                show a.size - 1 ≠ hi - 1 by lia] using hpivot) false
          return p.cast (by exact Array.swap_perm ..)
        else
          loop pivot a lo (hi - 1) (by lia) (by lia) hpivot true
      else
        return ⟨a, ⟨lo, by lia⟩, .rfl, hpivot⟩
    else
      if ← queryCmpLE pivot x then
        loop pivot a lo hi hl hh hpivot true
      else
        loop pivot a (lo + 1) hi (by lia) hh hpivot false
  else
    return ⟨a, ⟨lo, by lia⟩, .rfl, hpivot⟩
termination_by 2 * (hi - lo) + if stopped then 0 else 1
decreasing_by
  all_goals simp_all
  all_goals lia

end HoarePartition

/-- Reserve the chosen pivot in the final slot and partition the remaining interval.
The pivot is swapped into place without erasing or shifting any elements. -/
def hoarePartition (xs : Array α) (pivotIndex : Fin xs.size) :
    Prog (RandomQuicksortOps α) (HoarePartition xs xs[pivotIndex.val]) := do
  let pivot := xs[pivotIndex.val]
  let a := xs.swap pivotIndex.val (xs.size - 1) pivotIndex.isLt (by have := pivotIndex.isLt; lia)
  let p ← HoarePartition.loop pivot a 0 (xs.size - 1) (by lia)
    (by simp [a]; have := pivotIndex.isLt; lia) (by simp [a, pivot]) false
  return p.cast (by exact Array.swap_perm ..)

/-- Draw a pivot, partition from both ends, and recursively sort both groups.

Like `mergeSort`, this program obtains its comparator from the model. Using
`randomQuicksortModel le UniformSample.pmfModel` gives uniform randomized semantics.
The reserved pivot belongs to neither recursive view, so both recursive inputs are smaller.
-/
def randomQuicksort (xs : Array α) : Prog (RandomQuicksortOps α) (Array α) :=
  if h : xs.size = 0 then
    pure #[]
  else do
    let r ← drawPivot (xs.size - 1)
    have hr : r.val < xs.size := by have := r.isLt; lia
    let pivot := xs[r.val]
    let parts ← hoarePartition xs ⟨r.val, hr⟩
    let sortedLeft ← randomQuicksort parts.left.toArray
    let sortedRight ← randomQuicksort parts.right.toArray
    pure (sortedLeft ++ #[pivot] ++ sortedRight)
termination_by xs.size
decreasing_by
  all_goals
    have hparts := parts.parts_perm.size_eq
    simp only [Array.size_append, Array.size_singleton] at hparts
    lia

private theorem HoarePartition.loop_costM [Monad m] [LawfulMonad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (pivot : α) (a : Array α)
    (lo hi : Nat) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot) (stopped : Bool) :
    (HoarePartition.loop pivot a lo hi hl hh hpivot stopped).costM
        (randomQuicksortModel le sampling) =
      pure (hi - lo - if stopped then 1 else 0) := by
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped
  next a lo hi hl hh hpivot h x hp y ihSwap ihRight =>
    cases hy : le y pivot <;> simp [queryCmpLE, hy, ihSwap, ihRight]
    all_goals congr 1; lia
  next a lo hi hl hh hpivot h x hp =>
    simp
    congr 1
    lia
  next a lo hi hl hh hpivot stopped h x hstop ihRight ihLeft =>
    cases hx : le pivot x <;> simp [queryCmpLE, hx, ihRight, ihLeft, hstop]
    all_goals congr 1; lia
  next a lo hi hl hh hpivot stopped h =>
    simp [Nat.sub_eq_zero_of_le (show hi ≤ lo by lia)]

/-- Every element except the reserved pivot is queried exactly once. -/
@[simp] theorem hoarePartition_costM [Monad m] [LawfulMonad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (xs : Array α) (pivotIndex : Fin xs.size) :
    (hoarePartition xs pivotIndex).costM (randomQuicksortModel le sampling) =
      pure (xs.size - 1) := by
  simp [hoarePartition, HoarePartition.loop_costM]

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
private theorem HoarePartition.loop_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (pivot : α) (a : Array α) (lo hi : Nat) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot) (stopped : Bool)
    (hleft : ∀ i (h : i < a.size), i < lo → le a[i] pivot = true)
    (hright : ∀ i (h : i < a.size), hi ≤ i → le pivot a[i] = true)
    (hs : stopped = true → ∀ h : lo < hi, le pivot (a[lo]'(by lia)) = true) :
    ⦃⌜True⌝⦄ HoarePartition.loop pivot a lo hi hl hh hpivot stopped
      ⦃⇓p => ⌜(∀ i (h : i < p.array.size), i < p.split → le p.array[i] pivot = true) ∧
        (∀ i (h : i < p.array.size), p.split ≤ i → le pivot p.array[i] = true)⌝⦄ := by
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped
  next a lo hi hl hh hpivot h hp y ihSwap ihRight =>
    have hx := hs rfl h
    have ihs (hy : le y pivot = true) := ihSwap (by
      intro i hidx hilt
      by_cases he : i = lo
      · subst i; simpa using hy
      · rw [Array.getElem_swap_of_ne he (by lia)]
        exact hleft i (by simpa using hidx) (by lia)) (by
      intro i hidx hige
      by_cases he : i = hi - 1
      · subst i; simpa using hx
      · rw [Array.getElem_swap_of_ne (by lia) he]
        exact hright i (by simpa using hidx) (by lia)) (by simp)
    have ihr (hy : le y pivot = false) := ihRight hleft (by
      intro i hidx hige
      by_cases he : i = hi - 1
      · subst i
        have ht := Std.Total.total (r := fun a b => le a b = true) pivot y
        simpa [hy, y] using ht
      · exact hright i hidx (by lia)) (fun _ _ => hx)
    mvcgen [hcmp, ihs, ihr]
    all_goals simp_all [y]
  next a lo hi hl hh hpivot h hp =>
    have hx := hs rfl h
    mvcgen
    refine ⟨hleft, ?_⟩
    intro i hidx hige
    by_cases he : i = lo
    · subst i; exact hx
    · exact hright i hidx (by lia)
  next a lo hi hl hh hpivot stopped h x hstop ihRight ihLeft =>
    have ihr (hx : le pivot x = true) := ihRight hleft hright (fun _ _ => hx)
    have ihl (hx : le pivot x = false) := ihLeft (by
      intro i hidx hilt
      by_cases he : i = lo
      · subst i
        have ht := Std.Total.total (r := fun a b => le a b = true) pivot x
        simpa [hx, x] using ht
      · exact hleft i hidx (by lia)) hright (by simp)
    mvcgen [hcmp, ihr, ihl]
    all_goals simp_all [x]
  next a lo hi hl hh hpivot stopped h =>
    mvcgen
    refine ⟨hleft, ?_⟩
    intro i hidx hige
    exact hright i hidx (by lia)
set_option mvcgen.warning false in
/-- The left and right views lie weakly before and after the pivot, respectively. -/
theorem hoarePartition_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (pivotIndex : Fin xs.size) :
    ⦃⌜True⌝⦄ hoarePartition xs pivotIndex
      ⦃⇓p => ⌜(∀ x ∈ p.left.toArray, le x xs[pivotIndex.val] = true) ∧
        (∀ y ∈ p.right.toArray, le xs[pivotIndex.val] y = true)⌝⦄ := by
  have hrefl : le xs[pivotIndex.val] xs[pivotIndex.val] = true :=
    (Std.Total.total (r := fun a b => le a b = true) _ _).elim id id
  have hs := HoarePartition.loop_spec le hcmp xs[pivotIndex.val]
    (xs.swap pivotIndex.val (xs.size - 1) pivotIndex.isLt (by have := pivotIndex.isLt; lia))
    0 (xs.size - 1) (by lia) (by simp; have := pivotIndex.isLt; lia) (by simp) false
    (by simp) (by
      intro i hi h
      have he : i = xs.size - 1 := by simp only [Array.size_swap] at hi; lia
      subst i
      simpa using hrefl) (by simp)
  mvcgen [hoarePartition, hs]
  rename_i p hp
  obtain ⟨hpl, hpr⟩ := hp
  constructor
  · intro x hx
    rw [Array.mem_iff_getElem] at hx
    obtain ⟨i, hi, he⟩ := hx
    simp only [HoarePartition.left, HoarePartition.cast,
      Array.toArray_mkSlice_rio, Array.size_extract] at hi he
    rw [← he]
    have hi' : i < p.array.size := by lia
    simpa using hpl i hi' (by lia)
  · intro x hx
    rw [Array.mem_iff_getElem] at hx
    obtain ⟨i, hi, he⟩ := hx
    simp only [HoarePartition.right, HoarePartition.cast,
      Array.toArray_mkSlice_rco, Array.size_extract] at hi he
    rw [← he]
    simpa using hpr (p.split + i) (by lia) (by lia)

set_option mvcgen.warning false in
private theorem HoarePartition.loop_balanced_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (pivot : α) (a : Array α) (lo hi : Nat) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot) (stopped : Bool)
    (he : ∀ x ∈ a, le x pivot = true ∧ le pivot x = true) :
    ⦃⌜True⌝⦄ HoarePartition.loop pivot a lo hi hl hh hpivot stopped
      ⦃⇓p => ⌜p.split.val = lo + (hi - lo) / 2⌝⦄ := by
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped
  next a lo hi hl hh hpivot h hp y ihSwap ihRight =>
    have hy := (he y (by simp [y])).1
    have ihs := ihSwap (fun x hx => he x ((Array.swap_perm ..).mem_iff.mp hx))
    have ihr := ihRight he
    mvcgen [hcmp, ihs, ihr]
    all_goals simp_all [y]
    all_goals lia
  next a lo hi hl hh hpivot h hp =>
    mvcgen
    simp
    lia
  next a lo hi hl hh hpivot stopped h x hstop ihRight ihLeft =>
    have hx := (he x (by simp [x])).2
    have ihr := ihRight he
    have ihl := ihLeft he
    mvcgen [hcmp, ihr, ihl]
    all_goals simp_all [x]
  next a lo hi hl hh hpivot stopped h =>
    mvcgen
    simp [Nat.sub_eq_zero_of_le (show hi ≤ lo by lia)]

set_option mvcgen.warning false in
/-- Comparator-equivalent inputs split evenly, with any extra element on the right. -/
theorem hoarePartition_balanced_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (pivotIndex : Fin xs.size)
    (he : ∀ x ∈ xs, le x xs[pivotIndex.val] = true ∧ le xs[pivotIndex.val] x = true) :
    ⦃⌜True⌝⦄ hoarePartition xs pivotIndex
      ⦃⇓p => ⌜p.left.size = (xs.size - 1) / 2 ∧ p.right.size = xs.size / 2⌝⦄ := by
  have hs := HoarePartition.loop_balanced_spec le hcmp xs[pivotIndex.val]
    (xs.swap pivotIndex.val (xs.size - 1) pivotIndex.isLt (by have := pivotIndex.isLt; lia))
    0 (xs.size - 1) (by lia) (by simp; have := pivotIndex.isLt; lia) (by simp) false
    (fun x hx => he x ((Array.swap_perm ..).mem_iff.mp hx))
  mvcgen [hoarePartition, hs]
  rename_i p hp
  have hsize := p.perm.size_eq
  simp only [Array.size_swap] at hsize
  simp only [HoarePartition.left, HoarePartition.right, HoarePartition.cast,
    Array.size_mkSlice_rio, Array.size_mkSlice_rco]
  have hb := p.split.isLt
  simp only [Nat.sub_zero, Nat.zero_add] at hp
  constructor <;> lia

/-- Sorted permutations of the two partitions can be joined with the pivot. -/
private lemma quicksort_combine [IsTrans α (fun a b => le a b = true)]
    (pivot : α) (xs : Array α) (p : HoarePartition xs pivot) (sl sr : Array α)
    (hparts : (∀ x ∈ p.left.toArray, le x pivot = true) ∧
      (∀ y ∈ p.right.toArray, le pivot y = true))
    (hslp : sl.Perm p.left.toArray) (hsls : sl.Pairwise (fun a b => le a b = true))
    (hsrp : sr.Perm p.right.toArray) (hsrs : sr.Pairwise (fun a b => le a b = true)) :
    (sl ++ #[pivot] ++ sr).Perm xs ∧
      (sl ++ #[pivot] ++ sr).Pairwise (fun a b => le a b = true) := by
  have hle : ∀ a ∈ sl, le a pivot = true :=
    fun a ha => hparts.1 a (hslp.mem_iff.mp ha)
  have hge : ∀ b ∈ sr, le pivot b = true :=
    fun b hb => hparts.2 b (hsrp.mem_iff.mp hb)
  constructor
  · exact (((hslp.append (Array.Perm.refl #[pivot])).append hsrp).trans p.parts_perm)
  · rw [Array.pairwise_append, Array.pairwise_append]
    refine ⟨⟨hsls, Array.pairwise_singleton _ _, ?_⟩, hsrs, ?_⟩
    · intro a ha b hb
      simp only [Array.mem_singleton] at hb
      subst b
      exact hle a ha
    · intro a ha b hb
      rcases Array.mem_append.mp ha with ha | ha
      · exact IsTrans.trans (r := fun a b => le a b = true) a pivot b (hle a ha) (hge b hb)
      · simp only [Array.mem_singleton] at ha
        subst a
        exact hge b hb

set_option mvcgen.warning false in
/-- Correctness only needs accurate comparisons and a pivot in the requested finite range. -/
theorem randomQuicksort_spec_of_queries
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (hdraw : ∀ n, ⦃⌜True⌝⦄ (drawPivot n : Prog (RandomQuicksortOps α) _)
      ⦃⇓_ => ⌜True⌝⦄)
    (xs : Array α) :
    ⦃⌜True⌝⦄ randomQuicksort xs
      ⦃⇓out => ⌜out.Perm xs ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
  fun_induction randomQuicksort xs
  next xs h =>
    mvcgen
    have he : xs = #[] := Array.size_eq_zero_iff.mp h
    subst xs
    exact ⟨.rfl, Array.pairwise_empty⟩
  next xs h ihLeft ihRight =>
    have hpart := hoarePartition_spec le hcmp
    mvcgen [hdraw]
    rename_i r hr pivot
    dsimp +zetaDelta only
    mvcgen [hpart, ihLeft, ihRight]
    rename_i parts hparts sl hsl sr hsr
    have hc := quicksort_combine le xs[r.val] xs parts sl sr
      hparts hsl.1 hsl.2 hsr.1 hsr.2
    exact hc

set_option mvcgen.warning false in
/-- Uniform randomized quicksort returns a sorted permutation under the supplied comparator. -/
theorem randomQuicksort_spec [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (xs : Array α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃⌜True⌝⦄ randomQuicksort xs
      ⦃⇓out => ⌜out.Perm xs ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
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
