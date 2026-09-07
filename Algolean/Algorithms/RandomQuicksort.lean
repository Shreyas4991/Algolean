/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.ExpectedCost
public import Algolean.Models.ListComparisonSort
public import Algolean.Models.UniformSample
public import Algolean.QueryComposition
public import Batteries.Data.Array.Pairwise
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Randomized quicksort with Hoare partitioning

This file defines randomized quicksort in the comparison-query model and proves that it returns
a sorted permutation with expected comparison cost `O(n * log n)`, including inputs with repeated
elements. Correctness and partition-size specifications use `mvcgen`. The complexity proof combines
these specifications with uniform pivot probabilities and a harmonic potential.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.
- `hoarePartition`: partition using two inward scans, stopping on equivalent elements.
- `randomQuicksortModel`: interpret comparisons with a supplied Boolean ordering relation and
  pivot draws with a supplied sampling model.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
- `randomQuicksort_spec_of_queries`: correctness for any handler satisfying the query contracts.
- `hoarePartition_spec`: the two groups lie weakly on opposite sides of the pivot.
- `hoarePartition_costM`: partitioning costs exactly one comparison per non-pivot element.
- `hoarePartition_balanced_spec`: inputs equivalent under `le` split evenly.
- `quicksortRecurrence_eq_harmonic`: the exact solution of the standalone uniform-rank recurrence.
- `quicksortRecurrence_le_two_mul_log`: its `2 * n * log n` upper bound.
- `randomQuicksort_expectedCost_le`: expected comparison cost is at most `8 * n * log n + 16 * n`.
- `randomQuicksort_expectedCost_isBigO`: the corresponding asymptotic bound.
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

/-- Compare two values through the model's Boolean ordering relation. -/
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

Like `mergeSort`, this program obtains its ordering relation from the model. Using
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

set_option mvcgen.warning false

variable {α : Type}

variable (le : α → α → Bool)

/-- A comparison query returns the supplied ordering relation's answer. -/
theorem query_cmpLE_spec (y p : α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃⌜True⌝⦄
      queryCmpLE y p
      ⦃⇓b => ⌜b = le y p⌝⦄ := by
  mvcgen [queryCmpLE]
  intro b hb
  exact (PMF.mem_support_pure_iff (le y p) b).mp hb

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

/-- Inputs equivalent under `le` split evenly, with any extra element on the right. -/
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

/-- Uniform randomized quicksort returns a sorted permutation under `le`. -/
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

private theorem countP_extract_left (f : α → Bool) (a : Array α) {lo hi : ℕ}
    (hl : lo < hi) (hh : hi ≤ a.size) :
    (a.extract lo hi).countP f = (if f a[lo] then 1 else 0) +
      (a.extract (lo + 1) hi).countP f := by
  have hs : a.extract lo (lo + 1) = #[a[lo]] := by
    simpa [Array.extract_empty_of_stop_le_start (Nat.le_refl lo)] using
      (Array.push_extract_getElem (as := a) (i := lo) (j := lo) (by lia)).symm
  have he : a.extract lo (lo + 1) ++ a.extract (lo + 1) hi = a.extract lo hi := by
    rw [Array.extract_append_extract, Nat.min_eq_left (by lia), Nat.max_eq_right (by lia)]
  rw [← he, Array.countP_append, hs, Array.countP_singleton]

private theorem countP_extract_right (f : α → Bool) (a : Array α) {lo hi : ℕ}
    (hl : lo < hi) (hh : hi ≤ a.size) :
    (a.extract lo hi).countP f = (a.extract lo (hi - 1)).countP f +
      (if f a[hi - 1] then 1 else 0) := by
  have he : (a.extract lo (hi - 1)).push a[hi - 1] = a.extract lo hi := by
    rw [Array.push_extract_getElem, Nat.min_eq_left (by lia)]
    congr 1
    lia
  rw [← he, Array.countP_push]

private theorem extract_swap_inner (a : Array α) {lo hi : ℕ}
    (hl : lo + 1 < hi) (hh : hi ≤ a.size) :
    (a.swap lo (hi - 1) (by lia) (by lia)).extract (lo + 1) (hi - 1) =
      a.extract (lo + 1) (hi - 1) := by
  ext i h₁ h₂
  · simp
  · simp only [Array.getElem_extract]
    rw [Array.getElem_swap_of_ne (by lia) (by simp only [Array.size_extract] at h₂; lia)]

private theorem countP_extract_le (f : α → Bool) (a : Array α) {lo hi : ℕ}
    (hl : lo ≤ hi) (hh : hi ≤ a.size) :
    (a.extract lo hi).countP f ≤ a.countP f := by
  have he : (a.extract 0 lo ++ a.extract lo hi) ++ a.extract hi a.size = a := by
    simp only [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
      Nat.max_eq_right hl, Nat.max_eq_right hh, Array.extract_size]
  rw [← he, Array.countP_append, Array.countP_append]
  lia

private theorem countP_perm (f : α → Bool) {a b : Array α} (h : a.Perm b) :
    a.countP f = b.countP f := by
  simpa using h.toList.countP_eq f

private theorem HoarePartition.loop_size_spec
    (le : α → α → Bool)
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (pivot : α) (a : Array α) (lo hi : ℕ) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot) (stopped : Bool) :
    ⦃⌜True⌝⦄ HoarePartition.loop pivot a lo hi hl hh hpivot stopped
      ⦃⇓p => ⌜lo ≤ p.split.val ∧ p.split.val ≤ hi ∧
        2 * (p.split.val - lo) ≤ hi - lo +
          (a.extract lo hi).countP (fun x => !(le pivot x)) ∧
        2 * (hi - p.split.val) ≤ hi - lo +
          (a.extract lo hi).countP (fun x => !(le x pivot)) + 1⌝⦄ := by
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped
  next a lo hi hl hh hpivot h hp y ihSwap ihRight =>
    have hinner := extract_swap_inner a hp (by lia)
    have hleft := countP_extract_left (fun x => !(le pivot x)) a h (by lia)
    have hleft' := countP_extract_right (fun x => !(le pivot x)) a hp (by lia)
    have hright := countP_extract_left (fun x => !(le x pivot)) a h (by lia)
    have hright' := countP_extract_right (fun x => !(le x pivot)) a hp (by lia)
    have hrightFull := countP_extract_right (fun x => !(le x pivot)) a h (by lia)
    have hleftFull := countP_extract_right (fun x => !(le pivot x)) a h (by lia)
    mvcgen [hcmp, ihSwap, ihRight]
    all_goals simp_all
    all_goals lia
  next a lo hi hl hh hpivot h hp =>
    mvcgen
    simp
    lia
  next a lo hi hl hh hpivot stopped h x hstop ihRight ihLeft =>
    have hleft := countP_extract_left (fun x => !(le pivot x)) a h (by lia)
    have hright := countP_extract_left (fun x => !(le x pivot)) a h (by lia)
    mvcgen [hcmp, ihRight, ihLeft]
    all_goals simp_all
    all_goals lia
  next a lo hi hl hh hpivot stopped h =>
    mvcgen
    simp
    lia
/-- Bounds on both partition sizes in terms of strict comparisons with the pivot. -/
theorem hoarePartition_size_spec (le : α → α → Bool)
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (r : Fin xs.size) :
    ⦃⌜True⌝⦄ hoarePartition xs r
      ⦃⇓p => ⌜2 * p.left.size ≤ xs.size - 1 + xs.countP (fun x => !(le xs[r.val] x)) ∧
        2 * p.right.size ≤ xs.size + xs.countP (fun x => !(le x xs[r.val]))⌝⦄ := by
  have hs := HoarePartition.loop_size_spec le hcmp xs[r.val]
    (xs.swap r.val (xs.size - 1) r.isLt (by have := r.isLt; lia))
    0 (xs.size - 1) (by lia) (by simp; have := r.isLt; lia) (by simp) false
  have hleft := countP_extract_le (fun x => !(le xs[r.val] x))
    (xs.swap r.val (xs.size - 1) r.isLt (by have := r.isLt; lia))
    (lo := 0) (hi := xs.size - 1) (by lia) (by simp)
  have hright := countP_extract_le (fun x => !(le x xs[r.val]))
    (xs.swap r.val (xs.size - 1) r.isLt (by have := r.isLt; lia))
    (lo := 0) (hi := xs.size - 1) (by lia) (by simp)
  rw [countP_perm _ (Array.swap_perm ..)] at hleft hright
  mvcgen [hoarePartition, hs]
  rename_i p hp
  have hsize := p.perm.size_eq
  have hb := p.split.isLt
  have hn := r.isLt
  simp only [Array.size_swap] at hsize
  simp only [HoarePartition.left, HoarePartition.right, HoarePartition.cast,
    Array.size_mkSlice_rio, Array.size_mkSlice_rco]
  simp only [Nat.sub_zero] at hp
  have hL := hp.2.2.1.trans (Nat.add_le_add_left hleft _)
  have hR := hp.2.2.2.trans (Nat.add_le_add_right (Nat.add_le_add_left hright _) 1)
  simp only [Nat.min_eq_left (Nat.sub_le _ _), hsize]
  constructor
  · simpa only [Nat.min_eq_left (show p.split.val ≤ xs.size by lia)] using hL
  · convert hR using 1 <;> first | rfl | lia

end Correctness

section Complexity

/-- The scalar quicksort recurrence with a uniform pivot rank and one comparison per
non-pivot element: `C 0 = 0` and `C (n + 1) = n + 2 / (n + 1) * ∑ i ≤ n, C i`.

This numerical recurrence is analyzed independently of the program semantics. The expected-cost
proof for Hoare partitioning uses the larger `quicksortPotential` to account for elements
equivalent under `le`. -/
noncomputable def quicksortRecurrence : ℕ → ℝ
  | 0 => 0
  | n + 1 => n + 2 / (n + 1) * ∑ i : Fin (n + 1), quicksortRecurrence i
termination_by n => n

@[simp] theorem quicksortRecurrence_zero : quicksortRecurrence 0 = 0 := by
  rw [quicksortRecurrence]

private theorem quicksortRecurrence_step (n : ℕ) :
    (n + 1 : ℝ) * quicksortRecurrence (n + 1) =
      n * (n + 1) + 2 * ∑ i : Fin (n + 1), quicksortRecurrence i := by
  rw [quicksortRecurrence]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

private theorem quicksortRecurrence_adjacent (n : ℕ) :
    (n + 1 : ℝ) * quicksortRecurrence (n + 1) =
      (n + 2) * quicksortRecurrence n + 2 * n := by
  cases n with
  | zero => simpa using quicksortRecurrence_step 0
  | succ n =>
    have h := quicksortRecurrence_step n
    have h' := quicksortRecurrence_step (n + 1)
    rw [Fin.sum_univ_castSucc] at h'
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at h' ⊢
    nlinarith

/-- The exact solution of the uniform-rank quicksort recurrence. -/
theorem quicksortRecurrence_eq_harmonic (n : ℕ) :
    quicksortRecurrence n = 2 * (n + 1) * (harmonic n : ℝ) - 4 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := quicksortRecurrence_adjacent n
    rw [ih] at h
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    rw [harmonic_succ]
    push_cast
    apply (mul_left_cancel₀ hn)
    field_simp
    nlinarith

/-- The recurrence is bounded by `2 * n * log n`, including at sizes zero and one. -/
theorem quicksortRecurrence_le_two_mul_log (n : ℕ) :
    quicksortRecurrence n ≤ 2 * n * Real.log n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [quicksortRecurrence_eq_harmonic]
    have hh := harmonic_le_one_add_log (n + 1)
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n + 1) by positivity)
    push_cast at hh ⊢
    nlinarith

/-- The scalar recurrence has nonnegative values. -/
theorem quicksortRecurrence_nonneg (n : ℕ) : 0 ≤ quicksortRecurrence n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [quicksortRecurrence]
      exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun i _ => ih i i.isLt))

/-- Each pivot rank contributes the costs of its two recursive subproblems. -/
theorem quicksortRecurrence_succ (n : ℕ) :
    quicksortRecurrence (n + 1) = n + (∑ i : Fin (n + 1),
      (quicksortRecurrence i + quicksortRecurrence (n - i))) / (n + 1) := by
  have hr : (∑ i : Fin (n + 1), quicksortRecurrence (n - i)) =
      ∑ i : Fin (n + 1), quicksortRecurrence i := by
    simpa using (Equiv.sum_comp (⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩)
      (fun i : Fin (n + 1) => quicksortRecurrence i))
  rw [quicksortRecurrence, Finset.sum_add_distrib, hr]
  ring

/-- The standalone recurrence grows at most as `n * log n`. -/
theorem quicksortRecurrence_isBigO :
    quicksortRecurrence =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  refine Asymptotics.isBigO_iff.mpr ⟨2, Filter.Eventually.of_forall fun n => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (quicksortRecurrence_nonneg n), Real.norm_eq_abs]
  calc
    _ ≤ 2 * ((n : ℝ) * Real.log n) := by
      simpa [mul_assoc] using quicksortRecurrence_le_two_mul_log n
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)


/-- The smaller of the numbers of elements weakly above and weakly below the pivot under `le`. -/
def pivotWeight (le : α → α → Bool) (xs : Array α) (p : α) : ℕ :=
  min (xs.size - xs.countP (fun x => !(le p x)))
    (xs.size - xs.countP (fun x => !(le x p)))

private theorem sorted_strict_counts (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)]
    (xs : Array α) (hs : xs.Pairwise (fun a b => le a b = true)) (r : Fin xs.size) :
    xs.countP (fun x => !(le xs[r.val] x)) ≤ r.val ∧
      xs.countP (fun x => !(le x xs[r.val])) ≤ xs.size - 1 - r.val := by
  have hrefl : le xs[r.val] xs[r.val] = true :=
    (Std.Total.total (r := fun a b => le a b = true) _ _).elim id id
  have hs' := Array.pairwise_iff_getElem.mp hs
  constructor
  · have hz : (xs.extract r.val xs.size).countP (fun x => !(le xs[r.val] x)) = 0 := by
      apply Array.countP_eq_zero.mpr
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
      simp only [Array.size_extract, Nat.min_self] at hi
      simp only [Array.getElem_extract]
      have he : le xs[r.val] xs[r.val + i] = true := by
        by_cases h : i = 0
        · simpa [h] using hrefl
        · exact hs' _ _ r.isLt (by lia) (by lia)
      simp [he]
    have he : xs.extract 0 r.val ++ xs.extract r.val xs.size = xs := by
      simp only [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
        Nat.max_eq_right r.isLt.le, Array.extract_size]
    have hc := congrArg (fun a => a.countP (fun x => !(le xs[r.val] x))) he
    rw [Array.countP_append, hz, Nat.add_zero] at hc
    rw [← hc]
    have hb := Array.countP_le_size (p := fun x => !(le xs[r.val] x))
      (xs := xs.extract 0 r.val)
    simpa [Array.size_extract, Nat.min_eq_left r.isLt.le] using hb
  · have hz : (xs.extract 0 (r.val + 1)).countP (fun x => !(le x xs[r.val])) = 0 := by
      apply Array.countP_eq_zero.mpr
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
      simp only [Array.size_extract, Nat.sub_zero] at hi
      simp only [Array.getElem_extract, Nat.zero_add]
      have he : le xs[i] xs[r.val] = true := by
        by_cases h : i = r.val
        · subst i; exact hrefl
        · exact hs' _ _ (by lia) r.isLt (by lia)
      simp [he]
    have he : xs.extract 0 (r.val + 1) ++ xs.extract (r.val + 1) xs.size = xs := by
      simp only [Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
        Nat.max_eq_right (show r.val + 1 ≤ xs.size by lia), Array.extract_size]
    have hc := congrArg (fun a => a.countP (fun x => !(le x xs[r.val]))) he
    rw [Array.countP_append, hz, Nat.zero_add] at hc
    rw [← hc]
    have hb := Array.countP_le_size (p := fun x => !(le x xs[r.val]))
      (xs := xs.extract (r.val + 1) xs.size)
    simpa [Array.size_extract, Nat.sub_sub, Nat.add_comm] using hb

private theorem sum_getElem (xs : Array α) (f : α → ℕ) :
    (∑ i : Fin xs.size, f xs[i.val]) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  have h := List.ofFn_getElem_eq_map xs.toList f
  simpa [← Array.toList_map, Array.sum_toList] using congrArg List.sum h

private def rankWeightSum (n : ℕ) : ℕ := ∑ i : Fin n, min (i.val + 1) (n - i.val)

private theorem rankWeightSum_step (n : ℕ) :
    rankWeightSum (n + 2) = rankWeightSum n + n + 2 := by
  unfold rankWeightSum
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
  have he (i : Fin n) : min (i.val + 1 + 1) (n + 2 - (i.val + 1)) =
      min (i.val + 1) (n - i.val) + 1 := by have := i.isLt; lia
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  lia

private theorem rankWeightSum_lower (n : ℕ) : n * n ≤ 4 * rankWeightSum n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [rankWeightSum]
  | one => simp [rankWeightSum]
  | more n ih _ => rw [rankWeightSum_step]; nlinarith

private theorem pivotWeight_perm (le : α → α → Bool) {xs ys : Array α}
    (h : xs.Perm ys) (p : α) : pivotWeight le xs p = pivotWeight le ys p := by
  have hl := h.toList.countP_eq (fun x => !(le p x))
  have hr := h.toList.countP_eq (fun x => !(le x p))
  simp only [pivotWeight, h.size_eq, ← Array.countP_toList, hl, hr]

/-- The sum of pivot weights is at least one quarter of the square of the input size. -/
theorem sum_pivotWeight_lower (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) : xs.size * xs.size ≤
      4 * ∑ i : Fin xs.size, pivotWeight le xs xs[i.val] := by
  have hp : (xs.mergeSort le).Perm xs := Array.mergeSort_perm
  have hs : (xs.mergeSort le).Pairwise (fun a b => le a b = true) :=
    Array.pairwise_mergeSort (le := le) (xs := xs)
      (fun a b c hab hbc => trans_of (fun a b => le a b = true) hab hbc)
      (fun a b => by simpa using Std.Total.total (r := fun a b => le a b = true) a b)
  have hr (i : Fin (xs.mergeSort le).size) :
      min (i.val + 1) ((xs.mergeSort le).size - i.val) ≤
        pivotWeight le (xs.mergeSort le) (xs.mergeSort le)[i.val] := by
    have h := sorted_strict_counts le (xs.mergeSort le) hs i
    dsimp [pivotWeight]
    have hi := i.isLt
    lia
  have hb := (rankWeightSum_lower (xs.mergeSort le).size).trans
    (Nat.mul_le_mul_left 4 (Finset.sum_le_sum fun i _ => hr i))
  rw [sum_getElem] at hb ⊢
  have hm := (hp.toList.map (pivotWeight le xs)).sum_eq
  have he : ((xs.mergeSort le).map (pivotWeight le (xs.mergeSort le))).sum =
      (xs.map (pivotWeight le xs)).sum := by
    have hf : pivotWeight le (xs.mergeSort le) = pivotWeight le xs :=
      funext (pivotWeight_perm le hp)
    rw [hf]
    simpa [← Array.toList_map, Array.sum_toList] using hm
  rw [he, hp.size_eq] at hb
  exact hb

private theorem harmonic_gap (k n : ℕ) (h : k ≤ n) :
    0 ≤ (harmonic n : ℝ) - harmonic k ∧
      (n : ℝ) - k ≤ n * ((harmonic n : ℝ) - harmonic k) := by
  induction n generalizing k with
  | zero =>
    have hk : k = 0 := by lia
    subst k
    simp
  | succ n ih =>
    by_cases hk : k = n + 1
    · subst k; simp
    have hi := ih k (by lia)
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    have hc := mul_inv_cancel₀ hn
    have hn' : 0 ≤ (n + 1 : ℝ)⁻¹ := by positivity
    rw [harmonic_succ]
    push_cast
    constructor <;> nlinarith [hi.1, hi.2]

/-- Harmonic potential used to bound the expected comparison cost, including equivalent elements. -/
noncomputable def quicksortPotential (n : ℕ) : ℝ := 8 * (n + 1) * harmonic n

@[simp] theorem quicksortPotential_zero : quicksortPotential 0 = 0 := by
  simp [quicksortPotential]

/-- The harmonic potential is nonnegative. -/
theorem quicksortPotential_nonneg (n : ℕ) : 0 ≤ quicksortPotential n := by
  have h := (harmonic_gap 0 n (Nat.zero_le _)).1
  simp only [harmonic_zero, Rat.cast_zero, sub_zero] at h
  exact mul_nonneg (by positivity) h

/-- An explicit `n * log n` bound on the harmonic potential. -/
theorem quicksortPotential_le (n : ℕ) :
    quicksortPotential n ≤ 8 * n * Real.log n + 16 * n := by
  have h := quicksortRecurrence_le_two_mul_log n
  rw [quicksortRecurrence_eq_harmonic] at h
  dsimp [quicksortPotential]
  nlinarith

/-- The decrease in potential pays four times the pivot weight. -/
theorem quicksortPotential_split (n l r w : ℕ) (hn : 0 < n)
    (hs : l + r + 1 = n) (hw : w ≤ 2 * (n - max l r)) :
    quicksortPotential l + quicksortPotential r + 4 * w ≤ quicksortPotential n := by
  have hl := harmonic_gap l n (by lia)
  have hr := harmonic_gap r n (by lia)
  have hls := mul_le_mul_of_nonneg_left hl.2 (show (0 : ℝ) ≤ l + 1 by positivity)
  have hrs := mul_le_mul_of_nonneg_left hr.2 (show (0 : ℝ) ≤ r + 1 by positivity)
  have hln : (l : ℝ) ≤ max l r := by exact_mod_cast Nat.le_max_left l r
  have hrn : (r : ℝ) ≤ max l r := by exact_mod_cast Nat.le_max_right l r
  have hsq1 := mul_le_mul_of_nonneg_left hln (show (0 : ℝ) ≤ l by positivity)
  have hsq2 := mul_le_mul_of_nonneg_left hrn (show (0 : ℝ) ≤ r by positivity)
  have hs' : (l : ℝ) + r + 1 = n := by exact_mod_cast hs
  have hw' : (w : ℝ) ≤ 2 * ((n : ℝ) - max l r) := by
    rw [← Nat.cast_sub (show max l r ≤ n by lia)]
    exact_mod_cast hw
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : quicksortPotential n - quicksortPotential l - quicksortPotential r =
      8 * ((l + 1) * ((harmonic n : ℝ) - harmonic l) +
        (r + 1) * ((harmonic n : ℝ) - harmonic r)) := by
    dsimp [quicksortPotential]
    rw [← hs']
    ring
  have hdrop : 8 * ((n : ℝ) - max l r) ≤
      quicksortPotential n - quicksortPotential l - quicksortPotential r := by
    apply (mul_le_mul_iff_right₀ hn').mp
    rw [hd]
    nlinarith
  linarith

open scoped ENNReal

private theorem support_of_spec (P : Prog Q α) (M : ModelM Q PMF ℕ) (post : α → Prop)
    (h : letI := M.hasHandler; ⦃⌜True⌝⦄ P ⦃⇓a => ⌜post a⌝⦄) :
    ∀ a ∈ (P.evalM M).support, post a := by
  change (∀ (_ : True), ((FreeM.wpH M.handler P).apply
    (PostCond.noThrow fun a => ⌜post a⌝)).down) at h
  rw [ModelM.wp_eq_wp_evalM] at h
  exact h True.intro

private theorem weight_bound (n l r a b : ℕ)
    (hl : 2 * l ≤ n - 1 + a) (hr : 2 * r ≤ n + b) :
    min (n - a) (n - b) ≤ 2 * (n - max l r) := by lia

private theorem partition_potential_bound (le : α → α → Bool)
    (xs : Array α) (r : Fin xs.size)
    (p : HoarePartition xs xs[r.val])
    (hp : p ∈ ((hoarePartition xs r).evalM
      (randomQuicksortModel le UniformSample.pmfModel)).support) :
    quicksortPotential p.left.toArray.size + quicksortPotential p.right.toArray.size +
      4 * pivotWeight le xs xs[r.val] ≤ quicksortPotential xs.size := by
  have h := support_of_spec (hoarePartition xs r)
    (randomQuicksortModel le UniformSample.pmfModel) _
    (@hoarePartition_size_spec α le
      (randomQuicksortModel le UniformSample.pmfModel).hasHandler (query_cmpLE_spec le) xs r) p hp
  have hs := p.parts_perm.size_eq
  simp only [Array.size_append, Array.size_singleton] at hs
  apply quicksortPotential_split xs.size _ _ _ (by have := r.isLt; lia) (by lia)
  dsimp only [pivotWeight]
  apply weight_bound
  · simpa only [Subarray.size_toArray] using h.1
  · simpa only [Subarray.size_toArray] using h.2

@[simp] private theorem expectedCost_hoarePartition (le : α → α → Bool)
    (xs : Array α) (r : Fin xs.size) :
    (hoarePartition xs r).expectedCost (randomQuicksortModel le UniformSample.pmfModel) =
      (xs.size - 1 : ℕ) := by
  simp [Prog.expectedCost]

@[simp] private theorem expectedCost_drawPivot (le : α → α → Bool) (n : ℕ) :
    (drawPivot n).expectedCost (randomQuicksortModel le UniformSample.pmfModel) = 0 := by
  simp [Prog.expectedCost, drawPivot, randomQuicksortModel,
    UniformSample.pmfModel, UniformSample.model]

@[simp] private theorem evalM_drawPivot (le : α → α → Bool) (n : ℕ) :
    (drawPivot n).evalM (randomQuicksortModel le UniformSample.pmfModel) =
      PMF.uniformOfFintype (Fin (n + 1)) := by
  simp [drawPivot, randomQuicksortModel, UniformSample.pmfModel, UniformSample.model]

private theorem uniform_pivotWeight_bound (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) (n : ℕ) (hn : xs.size = n + 1) :
    (xs.size : ℝ≥0∞) ≤ (PMF.uniformOfFintype (Fin (n + 1))).expectation
      (fun i => ((4 * pivotWeight le xs (xs[i.val]'(by have := i.isLt; lia)) : ℕ) : ℝ≥0∞)) := by
  rw [PMF.expectation_uniformOfFintype]
  simp only [Fintype.card_fin]
  apply (ENNReal.mul_le_iff_le_inv (by simp) (by simp)).mp
  rw [← Nat.cast_sum]
  have he : (∑ i : Fin (n + 1), 4 * pivotWeight le xs (xs[i.val]'(by have := i.isLt; lia))) =
      4 * ∑ i : Fin xs.size, pivotWeight le xs xs[i.val] := by
    rw [← Finset.mul_sum]
    congr 1
    simpa using (Equiv.sum_comp (finCongr hn.symm)
      (fun i : Fin xs.size => pivotWeight le xs xs[i.val]))
  rw [he, ← hn, ← Nat.cast_mul]
  exact_mod_cast sum_pivotWeight_lower le xs

/-- Expected comparison cost is bounded by the harmonic potential
for any total transitive ordering relation `le`. -/
theorem randomQuicksort_expectedCost_le_potential (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) :
    (randomQuicksort xs).expectedCost (randomQuicksortModel le UniformSample.pmfModel) ≤
      ENNReal.ofReal (quicksortPotential xs.size) := by
  induction xs using (measure (fun a : Array α => a.size)).wf.induction with
  | h xs ih =>
    by_cases hn : xs.size = 0
    · rw [randomQuicksort, dif_pos hn]
      simp
    have hlocal (r : Fin xs.size) :
        ((hoarePartition xs r).evalM (randomQuicksortModel le UniformSample.pmfModel)).expectation
          (fun p => (randomQuicksort p.left.toArray).expectedCost
              (randomQuicksortModel le UniformSample.pmfModel) +
            (randomQuicksort p.right.toArray).expectedCost
              (randomQuicksortModel le UniformSample.pmfModel)) +
          ((4 * pivotWeight le xs xs[r.val] : ℕ) : ℝ≥0∞) ≤
            ENNReal.ofReal (quicksortPotential xs.size) := by
      rw [← PMF.expectation_const
        ((hoarePartition xs r).evalM (randomQuicksortModel le UniformSample.pmfModel))
        ((4 * pivotWeight le xs xs[r.val] : ℕ) : ℝ≥0∞), ← PMF.expectation_add]
      apply le_trans (PMF.expectation_mono _ (g := fun _ =>
        ENNReal.ofReal (quicksortPotential xs.size)) ?_) (by simp)
      intro p hp
      have hs := p.parts_perm.size_eq
      simp only [Array.size_append, Array.size_singleton] at hs
      have hl := ih p.left.toArray (by change p.left.toArray.size < xs.size; lia)
      have hr := ih p.right.toArray (by change p.right.toArray.size < xs.size; lia)
      have hpot := partition_potential_bound le xs r p hp
      calc
        _ ≤ ENNReal.ofReal (quicksortPotential p.left.toArray.size) +
            ENNReal.ofReal (quicksortPotential p.right.toArray.size) +
            ((4 * pivotWeight le xs xs[r.val] : ℕ) : ℝ≥0∞) :=
          add_le_add (add_le_add hl hr) le_rfl
        _ = ENNReal.ofReal (quicksortPotential p.left.toArray.size +
            quicksortPotential p.right.toArray.size + 4 * pivotWeight le xs xs[r.val]) := by
          rw [ENNReal.ofReal_add (add_nonneg (quicksortPotential_nonneg _)
            (quicksortPotential_nonneg _)) (by positivity),
            ENNReal.ofReal_add (quicksortPotential_nonneg _) (quicksortPotential_nonneg _)]
          simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal hpot
    rw [randomQuicksort, dif_neg hn]
    simp only [Prog.expectedCost_bind, Prog.expectedCost_pure, PMF.expectation_const,
      expectedCost_drawPivot, expectedCost_hoarePartition, evalM_drawPivot, add_zero, zero_add]
    have havg := PMF.expectation_mono
      (PMF.uniformOfFintype (Fin (xs.size - 1 + 1)))
      (fun i _ => hlocal ⟨i.val, by have := i.isLt; lia⟩)
    simp only [PMF.expectation_add, PMF.expectation_const] at havg ⊢
    have hw := uniform_pivotWeight_bound le xs (xs.size - 1) (by lia)
    have hc : ((xs.size - 1 : ℕ) : ℝ≥0∞) ≤ xs.size := by
      exact_mod_cast Nat.sub_le xs.size 1
    rw [add_comm] at havg
    exact (add_le_add (hc.trans hw) le_rfl).trans havg

/-- Uniform randomized quicksort uses at most
`8 * n * log n + 16 * n` comparisons in expectation. -/
theorem randomQuicksort_expectedCost_le (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) :
    (randomQuicksort xs).expectedCost (randomQuicksortModel le UniformSample.pmfModel) ≤
      ENNReal.ofReal (8 * xs.size * Real.log xs.size + 16 * xs.size) :=
  (randomQuicksort_expectedCost_le_potential le xs).trans
    (ENNReal.ofReal_le_ofReal (quicksortPotential_le xs.size))

/-- The expected comparison cost is finite. -/
theorem randomQuicksort_expectedCost_ne_top (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) :
    (randomQuicksort xs).expectedCost (randomQuicksortModel le UniformSample.pmfModel) ≠ ⊤ :=
  ne_of_lt ((randomQuicksort_expectedCost_le_potential le xs).trans_lt ENNReal.ofReal_lt_top)

/-- Expected comparison cost is `O(n * log n)` uniformly over inputs of size `n`. -/
theorem randomQuicksort_expectedCost_isBigO (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (inputs : ℕ → Array α) (hsize : ∀ n, (inputs n).size = n) :
    (fun n => ((randomQuicksort (inputs n)).expectedCost
      (randomQuicksortModel le UniformSample.pmfModel)).toReal)
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  refine Asymptotics.isBigO_iff.mpr ⟨8 + 16 / Real.log 2, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogn : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogn' : 0 ≤ Real.log (n : ℝ) := hlog.le.trans hlogn
  have he := (ENNReal.toReal_le_of_le_ofReal (quicksortPotential_nonneg (inputs n).size)
    (randomQuicksort_expectedCost_le_potential le (inputs n))).trans
      (quicksortPotential_le (inputs n).size)
  rw [hsize] at he
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogn')]
  apply he.trans
  have hc := (le_div_iff₀ hlog).mpr (show (16 : ℝ) * Real.log 2 ≤
    16 * Real.log n by gcongr)
  have hmul := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ n by positivity)
  calc
    _ ≤ 8 * n * Real.log n + n * (16 * Real.log n / Real.log 2) := by
      nlinarith only [hmul]
    _ = _ := by ring

end Complexity

end Models

end Algorithms

end Algolean
