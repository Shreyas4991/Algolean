/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.ListComparisonSort
public import Algolean.Models.UniformSample
public import Algolean.QueryComposition

/-!
# Randomized three-way quicksort of a list

This file defines randomized quicksort in the comparison-query model and proves that it always
returns a sorted permutation of its input. The proof is by `mvcgen` through the support-based
weakest-precondition semantics of `PMF`.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.
- `queryCmp`: obtain an `Ordering` using two opposite-direction comparison queries.
- `partition3`: partition into strict-less, equivalent, and strict-greater groups.
- `randomQuicksortModel`: interpret comparisons with a supplied Boolean comparator and
  pivot draws with a supplied sampling model.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
- `randomQuicksort_spec_of_queries`: correctness for any handler satisfying the query contracts.
- `partition3_spec`: the partition groups agree with the comparator's filter predicates.
- `partition3_costM`: partitioning costs exactly two comparisons per element.
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

/-- Determine an ordering using exactly two comparison queries, in opposite directions.

For a total comparator, two `true` answers mean equivalence, and exactly one `true` answer
determines the strict order. If both answers are `false`, this returns `.gt`; totality excludes
that case in the sorting specifications.
-/
def queryCmp (x y : α) : Prog (RandomQuicksortOps α) Ordering := do
  let xy ← queryCmpLE x y
  let yx ← queryCmpLE y x
  return if xy then (if yx then .eq else .lt) else .gt

/-- Three groups preserving all input elements. The permutation proof also bounds their sizes. -/
structure Partition3 (xs : List α) where
  /-- Elements less than the pivot. -/
  lt : List α
  /-- Elements equivalent to the pivot under the comparator. -/
  eq : List α
  /-- Elements greater than the pivot. -/
  gt : List α
  /-- Partitioning neither adds nor drops elements. -/
  perm : (lt ++ eq ++ gt).Perm xs

namespace Partition3

/-- Add the next input element to the less-than group. -/
def consLt (x : α) (p : Partition3 xs) : Partition3 (x :: xs) :=
  ⟨x :: p.lt, p.eq, p.gt, p.perm.cons x⟩

/-- Add the next input element to the equivalent group. -/
def consEq (x : α) (p : Partition3 xs) : Partition3 (x :: xs) :=
  ⟨p.lt, x :: p.eq, p.gt, by
    apply List.Perm.trans _ (p.perm.cons x)
    simp only [List.append_assoc, List.cons_append]
    exact List.perm_middle⟩

/-- Add the next input element to the greater-than group. -/
def consGt (x : α) (p : Partition3 xs) : Partition3 (x :: xs) :=
  ⟨p.lt, p.eq, x :: p.gt, List.perm_middle.trans (p.perm.cons x)⟩

theorem lt_length_le (p : Partition3 xs) : p.lt.length ≤ xs.length := by
  have h := p.perm.length_eq
  simp only [List.length_append] at h
  lia

theorem gt_length_le (p : Partition3 xs) : p.gt.length ≤ xs.length := by
  have h := p.perm.length_eq
  simp only [List.length_append] at h
  lia

end Partition3

/-- Partition around `pivot`, preserving input order within each group.

Every element is compared with the pivot in both directions. Equivalence is determined by the
comparator, so the middle group can contain distinct values with the same comparison key.
-/
def partition3 (pivot : α) (xs : List α) : Prog (RandomQuicksortOps α) (Partition3 xs) :=
  match xs with
  | [] => pure ⟨[], [], [], .refl _⟩
  | x :: xs => do
    match ← queryCmp x pivot with
    | .lt => Partition3.consLt x <$> partition3 pivot xs
    | .eq => Partition3.consEq x <$> partition3 pivot xs
    | .gt => Partition3.consGt x <$> partition3 pivot xs

/-- Computing an `Ordering` always costs two comparisons. -/
@[simp] theorem queryCmp_costM [Monad m] [LawfulMonad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (x y : α) :
    (queryCmp x y).costM (randomQuicksortModel le sampling) = pure 2 := by
  simp [queryCmp, queryCmpLE]

/-- Three-way partitioning costs exactly two comparisons per input element. -/
@[simp] theorem partition3_costM [Monad m] [LawfulMonad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) (pivot : α) (xs : List α) :
    (partition3 pivot xs).costM (randomQuicksortModel le sampling) = pure (2 * xs.length) := by
  induction xs with
  | nil => simp [partition3]
  | cons x xs ih =>
    cases hxy : le x pivot <;> cases hyx : le pivot x <;>
      simp [partition3, queryCmp, queryCmpLE, hxy, hyx, ih,
        Nat.mul_add, Nat.add_comm]
    all_goals
      congr 1
      lia

/-- Draw a pivot, partition into three groups, and recurse only on the strict groups.

Like `mergeSort`, this program obtains its comparator from the model. Using
`randomQuicksortModel le UniformSample.pmfModel` gives uniform randomized semantics.
The pivot and all comparator-equivalent elements are emitted together without further sorting.
-/
def randomQuicksort (l : List α) : Prog (RandomQuicksortOps α) (List α) :=
  match l with
  | [] => pure []
  | x :: xs => do
    let r ← drawPivot xs.length
    let pivot := (x :: xs).get r
    let rest := (x :: xs).eraseIdx r
    let parts ← partition3 pivot rest
    let sortedlt ← randomQuicksort parts.lt
    let sortedgt ← randomQuicksort parts.gt
    pure (sortedlt ++ [pivot] ++ parts.eq ++ sortedgt)
termination_by l.length
decreasing_by
  all_goals
    have hrest : rest.length = xs.length := by
      simp [rest, List.length_eraseIdx, r.isLt]
    have hlt := parts.lt_length_le
    have hgt := parts.gt_length_le
    simp only [List.length_cons]
    lia

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
/-- The two query answers determine the resulting `Ordering`. -/
theorem queryCmp_spec [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (x y : α) :
    ⦃⌜True⌝⦄ queryCmp x y
      ⦃⇓o => ⌜o = if le x y then (if le y x then .eq else .lt) else .gt⌝⦄ := by
  mvcgen [queryCmp, hcmp]
  all_goals simp_all

set_option mvcgen.warning false in
/-- The three groups are exactly the strict-less, equivalent, and remaining filters.
Under a total comparator the remaining group is strictly greater than the pivot. -/
theorem partition3_spec [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (pivot : α) (xs : List α) :
    ⦃⌜True⌝⦄ partition3 pivot xs
      ⦃⇓p => ⌜p.lt = xs.filter (fun x => le x pivot && !le pivot x) ∧
        p.eq = xs.filter (fun x => le x pivot && le pivot x) ∧
        p.gt = xs.filter (fun x => !le x pivot)⌝⦄ := by
  induction xs with
  | nil => mvcgen [partition3]
  | cons x xs ih =>
    mvcgen [partition3, queryCmp, hcmp, ih]
    all_goals
      cases hxy : le x pivot <;> cases hyx : le pivot x <;>
        simp_all [Partition3.consLt, Partition3.consEq, Partition3.consGt]

/-- Replacing the strict groups by sorted permutations gives a sorted permutation of the input
with the pivot added back. Equivalent elements need no recursive sorting. -/
private lemma quicksort_combine [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (pivot : α) (rest : List α) (p : Partition3 rest) (sl sr : List α)
    (hparts : p.lt = rest.filter (fun x => le x pivot && !le pivot x) ∧
      p.eq = rest.filter (fun x => le x pivot && le pivot x) ∧
      p.gt = rest.filter (fun x => !le x pivot))
    (hslp : sl.Perm p.lt) (hsls : sl.Pairwise (fun a b => le a b = true))
    (hsrp : sr.Perm p.gt) (hsrs : sr.Pairwise (fun a b => le a b = true)) :
    (sl ++ [pivot] ++ p.eq ++ sr).Perm (pivot :: rest) ∧
      (sl ++ [pivot] ++ p.eq ++ sr).Pairwise (fun a b => le a b = true) := by
  have hle : ∀ a ∈ sl, le a pivot = true := by
    intro a ha
    have hm := hslp.mem_iff.mp ha
    rw [hparts.1] at hm
    have hh := (List.mem_filter.mp hm).2
    simp only [Bool.and_eq_true] at hh
    exact hh.1
  have hge : ∀ b ∈ sr, le pivot b = true := by
    intro b hb
    have hm := hsrp.mem_iff.mp hb
    rw [hparts.2.2] at hm
    have hn := (List.mem_filter.mp hm).2
    have ht := Std.Total.total (r := fun a b => le a b = true) pivot b
    simp_all
  have heq : ∀ a ∈ p.eq, le a pivot = true ∧ le pivot a = true := by
    intro a ha
    rw [hparts.2.1] at ha
    simpa only [Bool.and_eq_true] using (List.mem_filter.mp ha).2
  have hrefl : le pivot pivot = true :=
    (Std.Total.total (r := fun a b => le a b = true) pivot pivot).elim id id
  have hmiddle : ∀ a ∈ pivot :: p.eq, le a pivot = true ∧ le pivot a = true := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨hrefl, hrefl⟩
    · exact heq a ha
  have htrans := IsTrans.trans (r := fun a b => le a b = true)
  have hsorted : (sl ++ (pivot :: p.eq) ++ sr).Pairwise (fun a b => le a b = true) := by
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨⟨hsls, List.pairwise_of_forall_mem_list ?_, ?_⟩, hsrs, ?_⟩
    · intro a ha b hb
      exact htrans a pivot b (hmiddle a ha).1 (hmiddle b hb).2
    · intro a ha b hb
      exact htrans a pivot b (hle a ha) (hmiddle b hb).2
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact htrans a pivot b (hle a ha) (hge b hb)
      · exact htrans a pivot b (hmiddle a ha).1 (hge b hb)
  have hperm : (sl ++ (pivot :: p.eq) ++ sr).Perm (pivot :: rest) := by
    have hmove : (sl ++ (pivot :: p.eq) ++ sr).Perm (pivot :: (sl ++ p.eq ++ sr)) := by
      simp only [List.append_assoc, List.cons_append]
      exact List.perm_middle
    exact hmove.trans ((((hslp.append_right p.eq).append hsrp).cons pivot).trans
      (p.perm.cons pivot))
  simpa only [List.append_assoc, List.singleton_append] using And.intro hperm hsorted

set_option mvcgen.warning false in
/-- Correctness only needs accurate comparisons and a pivot in the requested finite range. -/
theorem randomQuicksort_spec_of_queries
    [FreeM.HasHandler (RandomQuicksortOps α) .pure]
    [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (hcmp : ∀ (x y : α), ⦃⌜True⌝⦄ queryCmpLE x y ⦃⇓b => ⌜b = le x y⌝⦄)
    (hdraw : ∀ n, ⦃⌜True⌝⦄ (drawPivot n : Prog (RandomQuicksortOps α) _)
      ⦃⇓_ => ⌜True⌝⦄)
    (l : List α) :
    ⦃⌜True⌝⦄ randomQuicksort l
      ⦃⇓out => ⌜out.Perm l ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
  fun_induction randomQuicksort l
  next => mvcgen; exact ⟨.refl _, .nil⟩
  next x xs ih_lt ih_gt =>
    have hpart := partition3_spec le hcmp
    mvcgen [hdraw]
    rename_i r pivot rest
    dsimp +zetaDelta only
    mvcgen [hpart, ih_lt, ih_gt]
    rename_i parts hparts sl hsl sr hsr
    have hc := quicksort_combine le ((x :: xs).get r) ((x :: xs).eraseIdx ↑r) parts sl sr
      hparts hsl.1 hsl.2 hsr.1 hsr.2
    exact ⟨hc.1.trans (List.getElem_cons_eraseIdx_perm r.isLt), hc.2⟩

set_option mvcgen.warning false in
/-- Uniform randomized quicksort returns a sorted permutation under the supplied comparator. -/
theorem randomQuicksort_spec [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (l : List α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃⌜True⌝⦄ randomQuicksort l
      ⦃⇓out => ⌜out.Perm l ∧ out.Pairwise (fun a b => le a b = true)⌝⦄ := by
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
