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

namespace Algolean.Algorithms.Models

open SortOps Std.Do Cslib

/-- Comparison queries and computable finite pivot requests. -/
abbrev RandomQuicksortOps (α : Type) := compositeQuery (SortOps α) UniformSample

/-- Interpret comparisons with `le`, charging one per comparison and using `sampling` for draws.

`randomQuicksortModel le UniformSample.pmfModel` is the probabilistic model. Its per-query costs
are natural numbers; `(randomQuicksort xs).costM (randomQuicksortPMFModel le)`
is the `PMF ℕ` of total comparison counts.
-/
def randomQuicksortModel [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) : ModelM (RandomQuicksortOps α) m ℕ :=
  ModelM.sum
    { evalQuery := fun q => pure ((sortModelNat le).evalQuery q)
      cost := (sortModelNat le).cost }
    sampling

/-- Uniform pivot sampling with comparison costs under `le`. -/
noncomputable abbrev randomQuicksortPMFModel (le : α → α → Bool) :=
  randomQuicksortModel le UniformSample.pmfModel

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

attribute [grind =] cast_split

/-- The prefix view, sharing the partitioned array. -/
def left (p : HoarePartition xs pivot) : Subarray α := p.array[*...p.split.val]

/-- The right view, ending before the reserved pivot slot. -/
def right (p : HoarePartition xs pivot) : Subarray α := p.array[p.split.val...(p.array.size - 1)]

@[simp, grind =] theorem size_array (p : HoarePartition xs pivot) : p.array.size = xs.size :=
  p.perm.size_eq

@[simp] theorem size_left (p : HoarePartition xs pivot) : p.left.size = p.split.val := by
  simp only [left, Array.size_mkSlice_rio, Nat.min_eq_left p.split.isLt.le]

@[simp] theorem size_right (p : HoarePartition xs pivot) :
    p.right.size = xs.size - 1 - p.split.val := by simp [right]

@[simp] theorem left_cast (h : xs.Perm ys) (p : HoarePartition xs pivot) :
    (p.cast h).left = p.left := rfl

@[simp] theorem right_cast (h : xs.Perm ys) (p : HoarePartition xs pivot) :
    (p.cast h).right = p.right := rfl

/-- The partition views and reserved pivot reconstruct the entire array. -/
theorem parts_eq (p : HoarePartition xs pivot) :
    (p.left.toArray ++ p.right.toArray).push pivot = p.array := by
  have := p.split.isLt
  simp only [left, right, Array.toArray_mkSlice_rio, Array.toArray_mkSlice_rco,
    Array.extract_append_extract, Nat.min_eq_left (Nat.zero_le _),
    Nat.max_eq_right (show p.split.val ≤ p.array.size - 1 by lia)]
  simpa only [p.pivot_eq, show p.array.size - 1 + 1 = p.array.size by lia,
    Nat.min_eq_left (Nat.zero_le _), Array.extract_size] using
    (Array.push_extract_getElem (as := p.array) (i := 0) (j := p.array.size - 1) (by lia))

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

@[grind =] theorem sizes (p : HoarePartition xs pivot) :
    p.left.toArray.size + 1 + p.right.toArray.size = xs.size := by
  simpa using p.parts_perm.size_eq

grind_pattern sizes => p.left
grind_pattern sizes => p.right

@[grind .] theorem left_lt (p : HoarePartition xs pivot) :
    p.left.toArray.size < xs.size := by grind [p.sizes]

@[grind .] theorem right_lt (p : HoarePartition xs pivot) :
    p.right.toArray.size < xs.size := by grind [p.sizes]

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
  let a := xs.swap pivotIndex.val (xs.size - 1) pivotIndex.isLt (by grind [pivotIndex.isLt])
  let p ← HoarePartition.loop pivot a 0 (xs.size - 1) (by lia)
    (by simp [a]; grind [pivotIndex.isLt]) (by simp [a, pivot]) false
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
    have hr : r.val < xs.size := by grind
    let pivot := xs[r.val]
    let parts ← hoarePartition xs ⟨r.val, hr⟩
    let sortedLeft ← randomQuicksort parts.left.toArray
    let sortedRight ← randomQuicksort parts.right.toArray
    pure (sortedLeft ++ #[pivot] ++ sortedRight)
termination_by xs.size
decreasing_by all_goals first | exact parts.left_lt | exact parts.right_lt

private theorem HoarePartition.loop_costM [Monad m] [LawfulMonad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (pivot : α) (a : Array α)
    (lo hi : Nat) (hl : lo ≤ hi) (hh : hi < a.size)
    (hpivot : a[a.size - 1]'(by lia) = pivot) (stopped : Bool) :
    (HoarePartition.loop pivot a lo hi hl hh hpivot stopped).costM
        (randomQuicksortModel le sampling) =
      pure (hi - lo - if stopped then 1 else 0) := by
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped <;>
    simp_all only [queryCmpLE, bind_pure_comp, Prog.costM_liftBind, Prog.costM_pure,
      randomQuicksortModel_evalQuery_cmpLE, randomQuicksortModel_cost_cmpLE, pure_bind,
      Bool.false_eq_true, Bool.not_eq_true, ↓reduceIte, tsub_zero] <;>
    (try split) <;> simp_all <;> congr 1 <;> lia

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
    letI := (randomQuicksortPMFModel le).hasHandler
    ⦃⌜True⌝⦄
      queryCmpLE y p
      ⦃⇓b => ⌜b = le y p⌝⦄ := by
  mvcgen [queryCmpLE]
  exact fun b hb => (PMF.mem_support_pure_iff (le y p) b).mp hb

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
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped <;>
    mvcgen [*] <;> grind [Std.Total.total (r := fun a b => le a b = true)]

/-- The left and right views lie weakly before and after the pivot, respectively. -/
theorem hoarePartition_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (pivotIndex : Fin xs.size) :
    ⦃⌜True⌝⦄ hoarePartition xs pivotIndex
      ⦃⇓p => ⌜(∀ x ∈ p.left.toArray, le x xs[pivotIndex.val] = true) ∧
        (∀ y ∈ p.right.toArray, le xs[pivotIndex.val] y = true)⌝⦄ := by
  have hs := HoarePartition.loop_spec le hcmp
  mvcgen [hoarePartition, hs] <;>
    (try simp_all only [HoarePartition.left, HoarePartition.right,
      HoarePartition.cast_array, HoarePartition.cast_split, Array.toArray_mkSlice_rio,
      Array.toArray_mkSlice_rco, Array.mem_iff_getElem]) <;>
    grind [Std.Total.total (r := fun a b => le a b = true)]

/-- Sorted permutations of the two partitions can be joined with the pivot. -/
private lemma quicksort_combine [IsTrans α (fun a b => le a b = true)]
    (pivot : α) (xs : Array α) (p : HoarePartition xs pivot) (sl sr : Array α)
    (hparts : (∀ x ∈ p.left.toArray, le x pivot = true) ∧
      (∀ y ∈ p.right.toArray, le pivot y = true))
    (hslp : sl.Perm p.left.toArray) (hsls : sl.Pairwise (fun a b => le a b = true))
    (hsrp : sr.Perm p.right.toArray) (hsrs : sr.Pairwise (fun a b => le a b = true)) :
    (sl ++ #[pivot] ++ sr).Perm xs ∧
      (sl ++ #[pivot] ++ sr).Pairwise (fun a b => le a b = true) := by
  constructor
  · exact (((hslp.append (Array.Perm.refl #[pivot])).append hsrp).trans p.parts_perm)
  · simp only [Array.pairwise_append, Array.pairwise_singleton]
    grind [hslp.mem_iff, hsrp.mem_iff, IsTrans.trans (r := fun a b => le a b = true)]

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
  have hpart := hoarePartition_spec le hcmp
  fun_induction randomQuicksort xs
  next => mvcgen; simp_all [Array.size_eq_zero_iff, Array.pairwise_empty]
  next xs h ihLeft ihRight =>
    mvcgen [hdraw]
    dsimp +zetaDelta only
    mvcgen [hpart, ihLeft, ihRight]
    rename_i parts hparts sl hsl sr hsr
    exact quicksort_combine le _ _ _ _ _ hparts hsl.1 hsl.2 hsr.1 hsr.2

/-- Uniform randomized quicksort returns a sorted permutation under `le`. -/
theorem randomQuicksort_spec [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (xs : Array α) :
    letI := (randomQuicksortPMFModel le).hasHandler
    ⦃⌜True⌝⦄ randomQuicksort xs
      ⦃⇓out => ⌜out.Perm xs ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
  apply @randomQuicksort_spec_of_queries α le
    (randomQuicksortPMFModel le).hasHandler _ _
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
    rw [Array.push_extract_getElem]
    congr 1 <;> lia
  rw [← he, Array.countP_push]

grind_pattern countP_extract_left =>
  (a.extract lo hi).countP f, (a.extract (lo + 1) hi).countP f

grind_pattern countP_extract_right =>
  (a.extract lo hi).countP f, (a.extract lo (hi - 1)).countP f

private theorem countP_extract_inner_le (f : α → Bool) (a : Array α) {lo hi : ℕ}
    (hl : lo + 1 < hi) (hh : hi ≤ a.size) :
    (a.extract (lo + 1) (hi - 1)).countP f ≤ (a.extract lo hi).countP f := by
  have := countP_extract_left f a (show lo < hi by lia) hh
  have := countP_extract_right f a hl hh
  lia

grind_pattern countP_extract_inner_le =>
  (a.extract lo hi).countP f, (a.extract (lo + 1) (hi - 1)).countP f

@[grind =] private theorem extract_swap_inner (a : Array α) {lo hi : ℕ}
    (hl : lo + 1 < hi) (hh : hi ≤ a.size) :
    (a.swap lo (hi - 1) (by lia) (by lia)).extract (lo + 1) (hi - 1) =
      a.extract (lo + 1) (hi - 1) := by
  ext i h₁ h₂ <;> grind

private theorem countP_extract_le (f : α → Bool) (a : Array α) (lo hi : ℕ) :
    (a.extract lo hi).countP f ≤ a.countP f := by
  simpa only [← Array.countP_toList, Array.toList_extract, List.extract_eq_take_drop] using
    ((List.take_sublist (hi - lo) (a.toList.drop lo)).trans
      (List.drop_sublist lo a.toList)).countP_le

grind_pattern countP_extract_le => (a.extract lo hi).countP f

private theorem countP_perm {α : Type*} (f : α → Bool) {a b : Array α} (h : a.Perm b) :
    a.countP f = b.countP f := by
  simpa using h.toList.countP_eq f

@[simp, grind =] private theorem countP_swap (f : α → Bool) (a : Array α) (i j hi hj) :
    (a.swap i j hi hj).countP f = a.countP f := countP_perm f (Array.swap_perm ..)

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
  fun_induction HoarePartition.loop pivot a lo hi hl hh hpivot stopped <;>
    mvcgen [*] <;> grind

/-- Bounds on both partition sizes in terms of strict comparisons with the pivot. -/
theorem hoarePartition_size_spec (le : α → α → Bool)
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (r : Fin xs.size) :
    ⦃⌜True⌝⦄ hoarePartition xs r
      ⦃⇓p => ⌜2 * p.left.size ≤ xs.size - 1 + xs.countP (fun x => !(le xs[r.val] x)) ∧
        2 * p.right.size ≤ xs.size + xs.countP (fun x => !(le x xs[r.val]))⌝⦄ := by
  have hs := HoarePartition.loop_size_spec le hcmp
  mvcgen [hoarePartition, hs]
  simp_all only [HoarePartition.left_cast, HoarePartition.right_cast,
    HoarePartition.size_left, HoarePartition.size_right, Nat.sub_zero]
  grind

/-- Inputs equivalent under `le` split evenly, with any extra element on the right. -/
theorem hoarePartition_balanced_spec
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (xs : Array α) (pivotIndex : Fin xs.size)
    (he : ∀ x ∈ xs, le x xs[pivotIndex.val] = true ∧ le xs[pivotIndex.val] x = true) :
    ⦃⌜True⌝⦄ hoarePartition xs pivotIndex
      ⦃⇓p => ⌜p.left.size = (xs.size - 1) / 2 ∧ p.right.size = xs.size / 2⌝⦄ := by
  have hl : xs.countP (fun x => !(le xs[pivotIndex.val] x)) = 0 := by
    simp only [Array.countP_eq_zero]; grind
  have hr : xs.countP (fun x => !(le x xs[pivotIndex.val])) = 0 := by
    simp only [Array.countP_eq_zero]; grind
  have hpart := hoarePartition_size_spec le hcmp
  mvcgen [hpart]
  simp_all only [Nat.add_zero]
  grind [Subarray.size_toArray]

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
  fun_induction quicksortRecurrence n
  · simp
  · exact add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => by grind))

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

/-- A predicate confined to an index interval holds at most as often as its length. -/
private theorem countP_le_interval (f : α → Bool) (xs : Array α) (lo hi : ℕ)
    (hl : lo ≤ hi) (hh : hi ≤ xs.size)
    (h : ∀ i (hidx : i < xs.size), f xs[i] = true → lo ≤ i ∧ i < hi) :
    xs.countP f ≤ hi - lo := by
  have hz (a b : ℕ) (hab : b ≤ lo ∨ hi ≤ a) : (xs.extract a b).countP f = 0 := by
    simp only [Array.countP_eq_zero, Array.mem_iff_getElem]
    grind
  have he : xs.extract 0 lo ++ xs.extract lo hi ++ xs.extract hi xs.size = xs := by
    simp [Array.extract_append_extract, Nat.max_eq_right hl,
      Nat.max_eq_right hh]
  have hc := congrArg (Array.countP f) he
  simp only [Array.countP_append, hz 0 lo (Or.inl le_rfl), hz hi xs.size (Or.inr le_rfl),
    Nat.zero_add, Nat.add_zero] at hc
  have := Array.countP_le_size (p := f) (xs := xs.extract lo hi)
  grind

private theorem sorted_strict_counts (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)]
    (xs : Array α) (hs : xs.Pairwise (fun a b => le a b = true)) (r : Fin xs.size) :
    xs.countP (fun x => !(le xs[r.val] x)) ≤ r.val ∧
      xs.countP (fun x => !(le x xs[r.val])) ≤ xs.size - 1 - r.val := by
  have hs' := Array.pairwise_iff_getElem.mp hs
  constructor
  · simpa using countP_le_interval (fun x => !(le xs[r.val] x)) xs 0 r.val
      (by lia) (by grind) (by grind [Std.Total.total (r := fun a b => le a b = true)])
  · simpa [Nat.sub_sub, Nat.add_comm] using
      countP_le_interval (fun x => !(le x xs[r.val])) xs (r.val + 1) xs.size
        (by grind) le_rfl (by grind [Std.Total.total (r := fun a b => le a b = true)])

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
      min (i.val + 1) (n - i.val) + 1 := by grind
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
  simp only [pivotWeight, h.size_eq, countP_perm _ h]

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
    grind [pivotWeight]
  have hb := (rankWeightSum_lower (xs.mergeSort le).size).trans
    (Nat.mul_le_mul_left 4 (Finset.sum_le_sum fun i _ => hr i))
  rw [sum_getElem] at hb ⊢
  simpa only [hp.size_eq, funext (pivotWeight_perm le hp), ← Array.sum_toList, Array.toList_map,
    (hp.toList.map (pivotWeight le xs)).sum_eq] using hb

private theorem harmonic_gap (k n : ℕ) (h : k ≤ n) :
    0 ≤ (harmonic n : ℝ) - harmonic k ∧
      (n : ℝ) - k ≤ n * ((harmonic n : ℝ) - harmonic k) := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hc := mul_inv_cancel₀ (show (n + 1 : ℝ) ≠ 0 by positivity)
    rw [harmonic_succ]
    push_cast
    constructor <;> nlinarith [ih.1, ih.2, inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n + 1)]

/-- Harmonic potential used to bound the expected comparison cost, including equivalent elements. -/
noncomputable def quicksortPotential (n : ℕ) : ℝ := 8 * (n + 1) * harmonic n

@[simp] theorem quicksortPotential_zero : quicksortPotential 0 = 0 := by
  simp [quicksortPotential]

/-- The harmonic potential is nonnegative. -/
@[simp] theorem quicksortPotential_nonneg (n : ℕ) : 0 ≤ quicksortPotential n := by
  unfold quicksortPotential harmonic
  positivity

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
  have hw' : w * n ≤ 4 * (l + 1) * (r + 1) := by
    have hwl : w ≤ 2 * (l + 1) := by lia
    have hwr : w ≤ 2 * (r + 1) := by lia
    rcases le_total l r with h | h <;> nlinarith
  have hl := mul_le_mul_of_nonneg_left (harmonic_gap l n (by lia)).2
    (show (0 : ℝ) ≤ l + 1 by positivity)
  have hr := mul_le_mul_of_nonneg_left (harmonic_gap r n (by lia)).2
    (show (0 : ℝ) ≤ r + 1 by positivity)
  have hwR : (w : ℝ) * n ≤ 4 * (l + 1) * (r + 1) := by exact_mod_cast hw'
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < n by positivity)).mp
  subst n
  dsimp [quicksortPotential]
  push_cast at *
  nlinarith

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
      (randomQuicksortPMFModel le)).support) :
    quicksortPotential p.left.toArray.size + quicksortPotential p.right.toArray.size +
      4 * pivotWeight le xs xs[r.val] ≤ quicksortPotential xs.size := by
  have h := support_of_spec (hoarePartition xs r)
    (randomQuicksortPMFModel le) _
    (@hoarePartition_size_spec α le
      (randomQuicksortPMFModel le).hasHandler (query_cmpLE_spec le) xs r) p hp
  apply quicksortPotential_split xs.size _ _ _ (by grind) (by grind)
  dsimp only [pivotWeight]
  simpa only [Subarray.size_toArray] using weight_bound _ _ _ _ _ h.1 h.2

@[simp] private theorem expectedCost_hoarePartition (le : α → α → Bool)
    (xs : Array α) (r : Fin xs.size) :
    (hoarePartition xs r).expectedCost (randomQuicksortPMFModel le) =
      (xs.size - 1 : ℕ) := by
  simp [Prog.expectedCost]

@[simp] private theorem expectedCost_drawPivot (le : α → α → Bool) (n : ℕ) :
    (drawPivot n).expectedCost (randomQuicksortPMFModel le) = 0 := by
  simp [Prog.expectedCost, drawPivot, randomQuicksortModel,
    UniformSample.pmfModel, UniformSample.model]

@[simp] private theorem evalM_drawPivot (le : α → α → Bool) (n : ℕ) :
    (drawPivot n).evalM (randomQuicksortPMFModel le) =
      PMF.uniformOfFintype (Fin (n + 1)) := by
  simp [drawPivot, randomQuicksortModel, UniformSample.pmfModel, UniformSample.model]

private theorem uniform_pivotWeight_bound (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) (n : ℕ) (hn : xs.size = n + 1) :
    (xs.size : ℝ≥0∞) ≤ (PMF.uniformOfFintype (Fin (n + 1))).expectation
      (fun i => ((4 * pivotWeight le xs (xs[i.val]'(by grind)) : ℕ) : ℝ≥0∞)) := by
  rw [PMF.expectation_uniformOfFintype]
  simp only [Fintype.card_fin]
  apply (ENNReal.mul_le_iff_le_inv (by simp) (by simp)).mp
  rw [← Nat.cast_sum]
  have he : (∑ i : Fin (n + 1), 4 * pivotWeight le xs (xs[i.val]'(by grind))) =
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
    (randomQuicksort xs).expectedCost (randomQuicksortPMFModel le) ≤
      ENNReal.ofReal (quicksortPotential xs.size) := by
  induction xs using (measure (fun a : Array α => a.size)).wf.induction with
  | h xs ih =>
    by_cases hn : xs.size = 0
    · rw [randomQuicksort, dif_pos hn]
      simp
    have hlocal (r : Fin xs.size) :
        ((hoarePartition xs r).evalM (randomQuicksortPMFModel le)).expectation
          (fun p => (randomQuicksort p.left.toArray).expectedCost
              (randomQuicksortPMFModel le) +
            (randomQuicksort p.right.toArray).expectedCost
              (randomQuicksortPMFModel le)) +
          ((4 * pivotWeight le xs xs[r.val] : ℕ) : ℝ≥0∞) ≤
            ENNReal.ofReal (quicksortPotential xs.size) := by
      apply PMF.expectation_add_le
      intro p hp
      refine (add_le_add (add_le_add (ih _ p.left_lt) (ih _ p.right_lt)) le_rfl).trans ?_
      simpa [ENNReal.ofReal_add, add_nonneg] using
        ENNReal.ofReal_le_ofReal (partition_potential_bound le xs r p hp)
    rw [randomQuicksort, dif_neg hn]
    simp only [Prog.expectedCost_bind, Prog.expectedCost_pure, PMF.expectation_const,
      expectedCost_drawPivot, expectedCost_hoarePartition, evalM_drawPivot, add_zero, zero_add]
    have havg := PMF.expectation_mono
      (PMF.uniformOfFintype (Fin (xs.size - 1 + 1)))
      (fun i _ => hlocal ⟨i.val, by grind⟩)
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
    (randomQuicksort xs).expectedCost (randomQuicksortPMFModel le) ≤
      ENNReal.ofReal (8 * xs.size * Real.log xs.size + 16 * xs.size) :=
  (randomQuicksort_expectedCost_le_potential le xs).trans
    (ENNReal.ofReal_le_ofReal (quicksortPotential_le xs.size))

/-- The expected comparison cost is finite. -/
theorem randomQuicksort_expectedCost_ne_top (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (xs : Array α) :
    (randomQuicksort xs).expectedCost (randomQuicksortPMFModel le) ≠ ⊤ :=
  ne_of_lt ((randomQuicksort_expectedCost_le_potential le xs).trans_lt ENNReal.ofReal_lt_top)

/-- Expected comparison cost is `O(n * log n)` uniformly over inputs of size `n`. -/
theorem randomQuicksort_expectedCost_isBigO (le : α → α → Bool)
    [Std.Total (fun a b => le a b = true)] [IsTrans α (fun a b => le a b = true)]
    (inputs : ℕ → Array α) (hsize : ∀ n, (inputs n).size = n) :
    (fun n => ((randomQuicksort (inputs n)).expectedCost
      (randomQuicksortPMFModel le)).toReal)
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) * Real.log n) := by
  refine Asymptotics.isBigO_iff.mpr ⟨24, ?_⟩
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (Filter.eventually_ge_atTop 1)] with n hn
  change 1 ≤ Real.log (n : ℝ) at hn
  have he := (ENNReal.toReal_le_of_le_ofReal (quicksortPotential_nonneg (inputs n).size)
    (randomQuicksort_expectedCost_le_potential le (inputs n))).trans
      (quicksortPotential_le (inputs n).size)
  rw [hsize] at he
  simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  nlinarith [mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    le_abs_self ((n : ℝ) * Real.log n)]

end Complexity

end Algolean.Algorithms.Models
