/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.ListComparisonSort
public import Algolean.Models.UniformSample
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Randomized quicksort of a list

This file defines randomized quicksort in the comparison-query model, proves that it always
returns a sorted permutation of its input, and computes its expected number of comparisons.
Correctness is proved by `vcgen` through the support-based weakest-precondition semantics of
`PMF`; the expected number of comparisons is computed from the cost distribution `Prog.costM`.

## Main definitions

- `randomQuicksort`: randomized quicksort in the `SortOps` query model.
- `randomQuicksortModel`: interpret comparisons with a supplied Boolean comparator and
  pivot draws with a supplied sampling model.
- `expectedComparisons`: the expected number of comparisons of uniform randomized quicksort.

## Main results

- `randomQuicksort_spec`: randomized quicksort returns a sorted permutation.
- `randomQuicksort_spec_of_queries`: correctness for any handler satisfying the query contracts.
- `costM_randomQuicksort_cons`: the cost distribution of one call, for any sampling model.
- `expectedComparisons_cons`: the expected number of comparisons of one call, for any comparator.
- `randomQuicksort_expected_cost`: on `n` distinct elements, uniform randomized quicksort makes
  `2 (n + 1) H_n - 4 n` comparisons in expectation, where `H_n` is the `n`-th harmonic number.
- `randomQuicksort_expected_cost_le`, `randomQuicksort_expected_cost_isBigO`: this is at most
  `2 n log n`, hence `O(n log n)`.
-/

@[expose] public section

namespace List

variable {α : Type*} [LinearOrder α]

/-- In a list of distinct elements, each element has a distinct cardinality for the set of
elements smaller than it: if `l.Nodup`, then `i ↦ (l.filter (· < l[i])).length` is injective on
the positions `i` of `l`. -/
theorem Nodup.injective_length_filter_lt {l : List α} (hl : l.Nodup) :
    Function.Injective fun i : Fin l.length => (l.filter (· < l[i])).length := by
  have key {i j : Fin l.length} (h : l[i] < l[j]) :
      (l.filter (· < l[i])).length < (l.filter (· < l[j])).length := by
    have hsub : (l.filter (· < l[i])).Sublist (l.filter (· < l[j])) :=
      monotone_filter_right _ fun y hy => by simpa using (by simpa using hy : y < l[i]).trans h
    apply hsub.length_le.lt_of_ne
    intro heq
    have : l[i] ∈ l.filter (· < l[j]) := mem_filter.2 ⟨getElem_mem _, by simpa⟩
    rw [← hsub.eq_of_length heq] at this
    simp at this
  intro i j hij
  rcases lt_trichotomy l[i] l[j] with h | h | h
  · exact absurd hij (key h).ne
  · exact Fin.ext (hl.getElem_inj_iff.1 h)
  · exact absurd hij (key h).ne'

/-- If `l.Nodup` and `i` is a position of `l`, then `l.eraseIdx i` has as many elements at most
`l[i]` as `l` has elements smaller than `l[i]`. -/
theorem Nodup.length_filter_eraseIdx_le {l : List α} (hl : l.Nodup) (i : Fin l.length) :
    ((l.eraseIdx i).filter (· ≤ l[i])).length = (l.filter (· < l[i])).length := by
  have hp := getElem_cons_eraseIdx_perm i.isLt
  have hi := (nodup_cons.1 (hp.nodup_iff.2 hl)).1
  rw [← (hp.filter _).length_eq, filter_cons_of_neg (by simp)]
  congr 1
  apply filter_congr
  intro y hy
  simp only [le_iff_lt_or_eq, decide_eq_decide, or_iff_left_iff_imp]
  rintro rfl
  exact absurd hy hi

/-- If `l.Nodup`, then as `i` ranges over the positions of `l`, the number of elements of `l`
smaller than `l[i]` takes each value below `l.length` exactly once. Hence for any `f : ℕ → M`,
summing `f` of this number over the positions of `l` gives `∑ j < l.length, f j`. -/
theorem Nodup.sum_length_filter_lt {M : Type*} [AddCommMonoid M] {l : List α} (hl : l.Nodup)
    (f : ℕ → M) :
    ∑ i : Fin l.length, f (l.filter (· < l[i])).length = ∑ i ∈ Finset.range l.length, f i := by
  let g (i : Fin l.length) : Fin l.length :=
    ⟨(l.filter (· < l[i])).length,
      length_filter_lt_length_iff_exists.2 ⟨l[i], getElem_mem _, by simp⟩⟩
  have hg : Function.Injective g := fun i j h => hl.injective_length_filter_lt (congrArg Fin.val h)
  exact ((Finite.injective_iff_bijective.1 hg).sum_comp (f ·)).trans
    (Fin.sum_univ_eq_sum_range f _)

/-- If `l.Nodup`, then for each position `i` of `l`, partitioning `l.eraseIdx i` into the
elements at most `l[i]` and the elements greater than `l[i]` gives sides of sizes `j` and
`l.length - 1 - j`, and `j` takes each value below `l.length` exactly once as `i` varies. Hence for
any `f : ℕ → ℕ → M`, summing `f` of the two sizes over the positions of `l` gives
`∑ j < l.length, f j (l.length - 1 - j)`. -/
theorem Nodup.sum_length_filter_eraseIdx {M : Type*} [AddCommMonoid M] {l : List α}
    (hl : l.Nodup) (f : ℕ → ℕ → M) :
    ∑ i : Fin l.length, f ((l.eraseIdx i).filter (· ≤ l[i])).length
        ((l.eraseIdx i).filter (fun y => !decide (y ≤ l[i]))).length =
      ∑ i ∈ Finset.range l.length, f i (l.length - 1 - i) := by
  have h (i : Fin l.length) : ((l.eraseIdx i).filter (fun y => !decide (y ≤ l[i]))).length =
      l.length - 1 - ((l.eraseIdx i).filter (· ≤ l[i])).length := by
    have := (l.eraseIdx i).length_eq_length_filter_add (· ≤ l[i])
    rw [length_eraseIdx_of_lt i.isLt] at this
    lia
  simp only [h, hl.length_filter_eraseIdx_le]
  exact hl.sum_length_filter_lt fun j => f j (l.length - 1 - j)

end List

namespace Algolean

namespace Algorithms

namespace Models

open SortOps Std.WP Cslib

/-- Comparison queries and computable finite pivot requests. -/
abbrev RandomQuicksortOps (α : Type) := fun β => Sum (SortOps α β) (UniformSample β)

/-- Interpret comparisons with `le`, charging one per comparison and using `sampling` for draws. -/
def randomQuicksortModel [Monad m] (le : α → α → Bool)
    (sampling : ModelM UniformSample m ℕ) : ModelM (RandomQuicksortOps α) m ℕ :=
  ModelM.sum (ModelM.ofModel (sortModelNat le)) sampling

section Model

variable {α β : Type} {m : Type → Type*} [Monad m] (le : α → α → Bool)
  (sampling : ModelM UniformSample m ℕ)

/-- `randomQuicksortModel le sampling` answers the comparison `cmpLE x y` with `le x y`. -/
@[simp] theorem randomQuicksortModel_evalQuery_cmpLE (x y : α) :
    (randomQuicksortModel le sampling).evalQuery (.inl (.cmpLE x y)) = pure (le x y) := rfl

/-- `randomQuicksortModel le sampling` charges one unit for each comparison. -/
@[simp] theorem randomQuicksortModel_cost_cmpLE (x y : α) :
    (randomQuicksortModel le sampling).cost (.inl (.cmpLE x y)) = 1 := rfl

/-- `randomQuicksortModel le sampling` answers each sampling query as `sampling` does. -/
@[simp] theorem randomQuicksortModel_evalQuery_sample (q : UniformSample β) :
    (randomQuicksortModel le sampling).evalQuery (.inr q) = sampling.evalQuery q := rfl

/-- `randomQuicksortModel le sampling` charges for each sampling query what `sampling` charges. -/
@[simp] theorem randomQuicksortModel_cost_sample (q : UniformSample β) :
    (randomQuicksortModel le sampling).cost (.inr q) = sampling.cost q := rfl

end Model

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

/-- Keeping the elements of `xs` whose flag in `xs.map g` is `true` gives `xs.filter g`. -/
theorem keepFlagged_map (g : α → Bool) (xs : List α) :
    keepFlagged xs (xs.map g) = xs.filter g := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases h : g a <;> simp_all [keepFlagged]

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

set_option experimental.vcgen true in
/-- A comparison query returns the supplied comparator's answer. -/
theorem query_cmpLE_spec (y p : α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃ True ⦄
      queryCmpLE y p
      ⦃ fun b => b = le y p ⦄ := by
  let _ := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
  vcgen [queryCmpLE]
  change ∀ b ∈ (PMF.pure (le y p)).support, b = le y p
  simp

set_option experimental.vcgen true in
/-- Comparing every element against `p` yields the flags `xs.map (le · p)`. -/
theorem mapM_cmpLE_spec [FreeM.HasHandler (RandomQuicksortOps α) Prop EStack⟨⟩]
    (hcmp : ∀ (y p : α), ⦃ True ⦄ queryCmpLE y p ⦃ fun b => b = le y p ⦄)
    (p : α) (xs : List α) :
    ⦃ True ⦄ (xs.mapM (fun y ↦ queryCmpLE y p))
      ⦃ fun flags => flags = xs.map (fun y ↦ le y p) ⦄ := by
  induction xs with
  | nil => simp only [List.mapM_nil, List.map_nil]; vcgen
  | cons a as ih =>
    rw [List.mapM_cons]
    vcgen [hcmp, ih]
    simp_all

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

set_option experimental.vcgen true in
/-- Correctness only needs accurate comparisons and a pivot in the requested finite range. -/
theorem randomQuicksort_spec_of_queries
    [FreeM.HasHandler (RandomQuicksortOps α) Prop EStack⟨⟩]
    [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (hcmp : ∀ (y p : α), ⦃ True ⦄ queryCmpLE y p ⦃ fun b => b = le y p ⦄)
    (hdraw : ∀ n, ⦃ True ⦄ (drawPivot n : Prog (RandomQuicksortOps α) _)
      ⦃ fun _ => True ⦄)
    (l : List α) :
    ⦃ True ⦄ randomQuicksort l
      ⦃ fun out => out.Perm l ∧ out.Pairwise (fun a b => le a b = true) ⦄ := by
  fun_induction randomQuicksort l
  next => exact ⟨fun _ => ⟨.refl _, .nil⟩⟩
  next x xs ih_lt ih_rt =>
    have hflags := mapM_cmpLE_spec le hcmp
    -- Specialize the induction hypotheses after the pivot and flags are in scope.
    vcgen [hdraw, hflags] until randomQuicksort _
    rename_i hflags_eq
    have hlt : ⦃ True ⦄ randomQuicksort lt
        ⦃ fun out => out.Perm lt ∧ out.Pairwise (fun a b => le a b = true) ⦄ := ih_lt r flags
    have hrt : ⦃ True ⦄ randomQuicksort rt
        ⦃ fun out => out.Perm rt ∧ out.Pairwise (fun a b => le a b = true) ⦄ := ih_rt r flags
    vcgen [hlt, hrt]
    rename_i hsl hsr
    subst hflags_eq
    dsimp +zetaDelta only at hsl hsr
    simp only [keepFlagged_map, List.map_map, Function.comp_def] at hsl hsr
    have hc := quicksort_combine le ((x :: xs).get r) ((x :: xs).eraseIdx ↑r) sortedlt sortedrt
      hsl.1 hsl.2 hsr.1 hsr.2
    exact ⟨hc.1.trans (List.getElem_cons_eraseIdx_perm r.isLt), hc.2⟩

set_option experimental.vcgen true in
/-- Uniform randomized quicksort returns a sorted permutation under the supplied comparator. -/
theorem randomQuicksort_spec [Std.Total (fun a b => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (l : List α) :
    letI := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
    ⦃ True ⦄ randomQuicksort l
      ⦃ fun out => out.Perm l ∧ out.Pairwise (fun a b => le a b = true) ⦄ := by
  let _ := (randomQuicksortModel le UniformSample.pmfModel).hasHandler
  apply @randomQuicksort_spec_of_queries α le
    (randomQuicksortModel le UniformSample.pmfModel).hasHandler _ _
    (query_cmpLE_spec le)
  intro n
  vcgen [drawPivot]
  change ∀ r ∈ ((UniformSample.pmfModel (Cost := ℕ)).evalQuery (.fin n)).support, True
  simp

end Correctness

section Cost

variable {α β : Type} {m : Type → Type*} [Monad m] [LawfulMonad m] (le : α → α → Bool)
  (sampling : ModelM UniformSample m ℕ)

/-- In `randomQuicksortModel le sampling`, comparing every element of `xs` with `p` and then
running `f` on the results has the cost distribution of `f (xs.map (le · p))` shifted by
`xs.length`, one unit per comparison. -/
theorem costM_mapM_queryCmpLE_bind (p : α) (xs : List α)
    (f : List Bool → Prog (RandomQuicksortOps α) β) :
    (xs.mapM (queryCmpLE · p) >>= f).costM (randomQuicksortModel le sampling) =
      (xs.length + ·) <$> (f (xs.map (le · p))).costM (randomQuicksortModel le sampling) := by
  induction xs generalizing f with
  | nil => simp
  | cons y ys ih =>
    rw [List.mapM_cons, bind_assoc, queryCmpLE, Prog.costM_liftBind]
    simp only [randomQuicksortModel_evalQuery_cmpLE, randomQuicksortModel_cost_cmpLE, pure_bind,
      bind_assoc, ih, Functor.map_map, List.length_cons, List.map_cons]
    congr 2
    funext k
    lia

/-- In `randomQuicksortModel le sampling`, the cost distribution of `randomQuicksort (x :: xs)` is
obtained by drawing a pivot position `r` from `sampling` and adding the cost of that draw,
`xs.length` comparisons against the pivot, and independent draws from the cost distributions of
the two recursive calls on the elements other than the pivot, split by comparison with it. -/
theorem costM_randomQuicksort_cons (x : α) (xs : List α) :
    (randomQuicksort (x :: xs)).costM (randomQuicksortModel le sampling) =
      sampling.evalQuery (.fin xs.length) >>= fun r =>
        (fun c => sampling.cost (.fin xs.length) + (xs.length + c)) <$>
          ((randomQuicksort (((x :: xs).eraseIdx r).filter (le · ((x :: xs).get r)))).costM
              (randomQuicksortModel le sampling) >>= fun a =>
            (a + ·) <$> (randomQuicksort (((x :: xs).eraseIdx r).filter
              (!le · ((x :: xs).get r)))).costM (randomQuicksortModel le sampling)) := by
  rw [randomQuicksort, drawPivot, Prog.costM_liftBind]
  simp only [randomQuicksortModel_evalQuery_sample, randomQuicksortModel_cost_sample]
  apply bind_congr
  intro r
  rw [costM_mapM_queryCmpLE_bind, Prog.costM_bind_of_forall_costM_eq _ _ _
    fun _ => by rw [bind_pure_comp, Prog.costM_map]]
  simp only [keepFlagged_map, List.map_map, Function.comp_def, Functor.map_map,
    List.length_eraseIdx_of_lt (l := x :: xs) r.isLt, List.length_cons, Nat.add_sub_cancel]

end Cost

section ExpectedComparisons

open scoped ENNReal

variable {α : Type} (le : α → α → Bool)

/-- The expected number of comparisons that `randomQuicksort` makes on `l` when comparisons are
answered by `le` and pivots are drawn uniformly at random. Pivot draws cost nothing. -/
noncomputable def expectedComparisons (l : List α) : ℝ≥0∞ :=
  ∑' k, (randomQuicksort l).costM (randomQuicksortModel le UniformSample.pmfModel) k * k

/-- Randomized quicksort makes no comparisons on the empty list. -/
@[simp] theorem expectedComparisons_nil : expectedComparisons le [] = 0 := by
  simp [expectedComparisons, randomQuicksort, PMF.monad_pure_eq_pure]

/-- The expected number of comparisons of randomized quicksort on `x :: xs` is `xs.length`, for
comparing the other elements with the pivot, plus the average over the `xs.length + 1` pivot
positions `r` of the expected numbers of comparisons on the two sides: the other elements `y`
with `le y (x :: xs)[r]` and those with `¬le y (x :: xs)[r]`. This holds for any comparator
`le`. -/
theorem expectedComparisons_cons (x : α) (xs : List α) :
    expectedComparisons le (x :: xs) = xs.length + (xs.length + 1 : ℝ≥0∞)⁻¹ *
      ∑ r : Fin (xs.length + 1),
        (expectedComparisons le (((x :: xs).eraseIdx r).filter (le · (x :: xs)[(r : ℕ)])) +
          expectedComparisons le (((x :: xs).eraseIdx r).filter (!le · (x :: xs)[(r : ℕ)]))) := by
  simp only [expectedComparisons, costM_randomQuicksort_cons, PMF.monad_bind_eq_bind,
    PMF.monad_map_eq_map, UniformSample.pmfModel_cost, zero_add, List.get_eq_getElem]
  rw [PMF.tsum_bind_mul]
  simp only [PMF.tsum_map_add_left_mul, PMF.tsum_bind_map_add_mul,
    UniformSample.pmfModel_evalQuery_fin_apply, tsum_fintype, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_add]
  rw [← mul_assoc, Nat.cast_add_one, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

end ExpectedComparisons

section ExpectedCost

open scoped ENNReal

variable {α : Type} [LinearOrder α]

/-- The closed form `2 (n + 1) H_n - 4 n`, where `H_n` is the `n`-th harmonic number. It is the
expected number of comparisons of randomized quicksort on `n` distinct elements. -/
private noncomputable def meanComparisons (n : ℕ) : ℝ := 2 * (n + 1) * harmonic n - 4 * n

/-- `∑ i ≤ n, (2 (i + 1) H_i - 4 i) = (n + 1) (n + 2) H_n - n (5 n + 7) / 2`. -/
private lemma sum_meanComparisons (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), meanComparisons i =
      (n + 1) * (n + 2) * harmonic n - n * (5 * n + 7) / 2 := by
  induction n with
  | zero => simp [meanComparisons]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, meanComparisons, harmonic_succ]
    push_cast
    field_simp
    ring

/-- The closed form satisfies the recurrence of randomized quicksort on distinct elements:
`e (n + 1) = n + 2 / (n + 1) * ∑ i ≤ n, e i`. -/
private lemma meanComparisons_succ (n : ℕ) :
    meanComparisons (n + 1) =
      n + 2 / (n + 1) * ∑ i ∈ Finset.range (n + 1), meanComparisons i := by
  rw [sum_meanComparisons, meanComparisons, harmonic_succ]
  push_cast
  field_simp
  ring

/-- `2 (n + 1) H_n - 4 n` is nonnegative. -/
private lemma meanComparisons_nonneg (n : ℕ) : 0 ≤ meanComparisons n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [meanComparisons]
    · rw [meanComparisons_succ]
      have := Finset.sum_nonneg fun i hi => ih i (Finset.mem_range.1 hi)
      positivity

/-- `2 (n + 1) H_n - 4 n ≤ 2 n log n`. -/
private lemma meanComparisons_le (n : ℕ) : meanComparisons n ≤ 2 * n * Real.log n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [meanComparisons]
  have := harmonic_le_one_add_log n
  have := Real.log_le_sub_one_of_pos (Nat.cast_pos.2 hn)
  rw [meanComparisons]
  nlinarith

/-- The recurrence `meanComparisons_succ` in `ℝ≥0∞`, with `2 ∑ i ≤ n, e i` written as
`∑ i ≤ n, (e i + e (n - i))` to match `expectedComparisons_cons`. -/
private lemma ofReal_meanComparisons_succ (n : ℕ) :
    ENNReal.ofReal (meanComparisons (n + 1)) =
      n + (n + 1 : ℝ≥0∞)⁻¹ * ∑ i ∈ Finset.range (n + 1),
        (ENNReal.ofReal (meanComparisons i) +
          ENNReal.ofReal (meanComparisons (n + 1 - 1 - i))) := by
  have hS := Finset.sum_nonneg fun i (_ : i ∈ Finset.range (n + 1)) => meanComparisons_nonneg i
  rw [Finset.sum_add_distrib,
    Finset.sum_range_reflect (fun i => ENNReal.ofReal (meanComparisons i)),
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => meanComparisons_nonneg i, meanComparisons_succ,
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_div_of_pos (by positivity)]
  simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [show ENNReal.ofReal (n + 1) = n + 1 by norm_cast, div_eq_mul_inv]
  ring

/-- On a list of `n` distinct elements of a linear order, randomized quicksort with uniformly
drawn pivots makes `2 (n + 1) H_n - 4 n` comparisons in expectation, where `H_n` is the `n`-th
harmonic number. -/
theorem randomQuicksort_expected_cost (l : List α) (hl : l.Nodup) :
    expectedComparisons (· ≤ ·) l =
      ENNReal.ofReal (2 * (l.length + 1) * harmonic l.length - 4 * l.length) := by
  change _ = ENNReal.ofReal (meanComparisons l.length)
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  subst hn
  rcases l with _ | ⟨x, xs⟩
  · simp [meanComparisons]
  have hrec (r : Fin (xs.length + 1)) (p : α → Bool) :=
    ih _ ((List.length_filter_le _ _).trans_lt
      (by simp [List.length_eraseIdx_of_lt (l := x :: xs) r.isLt])) _ ((hl.eraseIdx r).filter p) rfl
  rw [expectedComparisons_cons, List.length_cons, ofReal_meanComparisons_succ]
  simp only [hrec]
  congr 2
  exact hl.sum_length_filter_eraseIdx fun i j =>
    ENNReal.ofReal (meanComparisons i) + ENNReal.ofReal (meanComparisons j)

/-- On a list of `n` distinct elements of a linear order, randomized quicksort with uniformly
drawn pivots makes at most `2 n log n` comparisons in expectation. -/
theorem randomQuicksort_expected_cost_le (l : List α) (hl : l.Nodup) :
    expectedComparisons (· ≤ ·) l ≤ ENNReal.ofReal (2 * l.length * Real.log l.length) := by
  rw [randomQuicksort_expected_cost l hl]
  exact ENNReal.ofReal_le_ofReal (meanComparisons_le _)

open Asymptotics Filter in
/-- Randomized quicksort with uniformly drawn pivots makes `O(n log n)` comparisons in
expectation: if `ls n` is a list of `n` distinct elements of a linear order for each `n`, the
expected number of comparisons on `ls n` is `O(n log n)` as `n → ∞`. -/
theorem randomQuicksort_expected_cost_isBigO (ls : ℕ → List α) (hnodup : ∀ n, (ls n).Nodup)
    (hlength : ∀ n, (ls n).length = n) :
    (fun n => (expectedComparisons (· ≤ ·) (ls n)).toReal) =O[atTop]
      fun n => (n : ℝ) * Real.log n := by
  apply IsBigO.of_bound 2
  filter_upwards with n
  have h := randomQuicksort_expected_cost_le (ls n) (hnodup n)
  rw [hlength n] at h
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg (mul_nonneg n.cast_nonneg (Real.log_natCast_nonneg n)), ← mul_assoc]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end ExpectedCost

end Models

end Algorithms

end Algolean
