/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.ReadWriteVec
public import Mathlib.Data.List.Sort
public import Std.Tactic.Do

/-!
# Bubble sort in the read/write vector query model

Bubble sort written as a program in the `Vec` query model (`Prog (Vec α)`), using `read` and
`write` queries against a mutable vector threaded through `for` loops. This is the worked example
the query-model WP framework is built for: a *non-trivial* `mvcgen` development establishing full
functional correctness — both that the output is a permutation of the input and that it is sorted.

The algorithm is split into two pieces, each verified with its own single-loop `mvcgen` proof and
composed through a Hoare-triple spec (`bubblePass_spec`), which is the idiomatic way to keep loop
reasoning modular:

- `bubblePass` makes one left-to-right sweep over `[0, bound]`, bubbling the largest element of
  that range up to position `bound`.
- `bubbleSort` runs `n` such passes with shrinking bounds `n-1, n-2, …`, growing a sorted suffix.

## Main definitions

- `bubblePass` : one bubbling sweep in the `Vec` query model.
- `bubbleSort` : bubble sort in the `Vec` query model.

## Main results

- `bubbleSort_perm` : `bubbleSort` returns a permutation of its input.
- `bubbleSort_sorted` : `bubbleSort` returns a sorted vector (for a total, transitive `le`).
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog Std.Do

set_option mvcgen.warning false

/--
One bubbling sweep in the `Vec` query model: for each adjacent pair `v[j], v[j+1]` with
`j < bound`, read both and, if out of order under `le`, write them back swapped. After the sweep
the largest element of `[0, bound]` sits at position `bound`.
-/
def bubblePass (le : α → α → Bool) (bound : Nat) (hb : bound < n) (v : Vector α n) :
    Prog (Vec α) (Vector α n) := do
  let mut v := v
  for j in List.finRange bound do
    let a ← (Vec.read v ⟨j, by lia⟩      : Prog (Vec α) α)
    let b ← (Vec.read v ⟨j + 1, by lia⟩  : Prog (Vec α) α)
    if !le a b then
      v ← (Vec.write v ⟨j, by lia⟩     b : Prog (Vec α) (Vector α n))
      v ← (Vec.write v ⟨j + 1, by lia⟩ a : Prog (Vec α) (Vector α n))
  return v

/--
Bubble sort in the `Vec` query model: run `n` bubbling passes with shrinking bounds. After the
`k`-th pass the last `k` positions hold the `k` largest elements in sorted order.
-/
def bubbleSort (le : α → α → Bool) (v : Vector α n) : Prog (Vec α) (Vector α n) := do
  let mut v := v
  for i in List.finRange n do
    v ← bubblePass le (n - 1 - i) (by lia) v
  return v

/-! ### Invariants and pointwise lemmas

`MaxAt le w m` says `w[m]` dominates the prefix `[0, m]`; `SortedFrom le w b` says positions
`[b, n)` are sorted and dominated by the whole prefix. These are the loop invariants, with the
pointwise lemmas below feeding `mvcgen`'s verification conditions. -/

variable {α : Type} {n : Nat}

/-- `w[m]` is `≥` everything in the prefix `[0, m]`. -/
def MaxAt (le : α → α → Bool) (w : Vector α n) (m : Nat) : Prop :=
  ∀ p q : Fin n, (p : Nat) ≤ m → (q : Nat) = m → le w[p] w[q] = true

/-- Positions `[b, n)` are sorted and dominated by the whole prefix. -/
def SortedFrom (le : α → α → Bool) (w : Vector α n) (b : Nat) : Prop :=
  ∀ p q : Fin n, (p : Nat) ≤ (q : Nat) → b ≤ (q : Nat) → le w[p] w[q] = true

/-- In a `finRange` split, the cursor element sits at the prefix length. -/
private theorem fin_cur_eq {pref suff : List (Fin n)} {cur : Fin n}
    (h : List.finRange n = pref ++ cur :: suff) : (cur : Nat) = pref.length := by
  have hlt : pref.length < n := by have := congrArg List.length h; simp at this; lia
  have h2 := congrArg (fun l => l[pref.length]?) h
  simp only [List.getElem?_append_right (Nat.le_refl pref.length), Nat.sub_self,
    List.getElem?_cons_zero, List.getElem_finRange,
    List.getElem?_eq_getElem (show pref.length < (List.finRange n).length by simpa using hlt)] at h2
  exact (congrArg Fin.val (Option.some.inj h2)).symm

/-- Swapping two entries permutes the underlying list. -/
private lemma set_set_toList_perm (w : Vector α n) (i j : Nat) (hi : i < n) (hj : j < n) :
    ((w.set i (w[j]'hj) hi).set j (w[i]'hi) hj).toList.Perm w.toList := by
  simpa [Vector.toList_set, Vector.getElem_toList] using
    List.set_set_perm (as := w.toList) (by simpa using hi) (by simpa using hj)

/-- After swapping out-of-order `w[m], w[m+1]`, the prefix maximum moves to `m+1`. -/
private lemma maxAt_swap (le : α → α → Bool) (htot : ∀ a b : α, le a b = true ∨ le b a = true)
    (w : Vector α n) (m : Nat) (hm : m + 1 < n) (hmax : MaxAt le w m)
    (hsw : le (w[m]'(by lia)) (w[m + 1]'hm) = false) :
    MaxAt le ((w.set m (w[m + 1]'hm) (by lia)).set (m + 1) (w[m]'(by lia)) hm) (m + 1) := by
  intro p q hp hq
  have hcmp := (htot (w[m]'(by lia)) (w[m + 1]'hm)).resolve_left (by simp [hsw])
  have key : ∀ r : Fin n, (r : Nat) ≤ m → le w[r] (w[m]'(by lia)) = true :=
    fun r hr => hmax r ⟨m, by lia⟩ hr rfl
  grind

/-- When the pair is already in order, the prefix maximum still extends to `m+1`. -/
private lemma maxAt_noswap (le : α → α → Bool) (htot : ∀ a b : α, le a b = true ∨ le b a = true)
    (htr : ∀ a b c : α, le a b = true → le b c = true → le a c = true)
    (w : Vector α n) (m : Nat) (hm : m + 1 < n) (hmax : MaxAt le w m)
    (hns : le (w[m]'(by lia)) (w[m + 1]'hm) = true) : MaxAt le w (m + 1) := by
  intro p q hp hq
  have key : ∀ r : Fin n, (r : Nat) ≤ m → le w[r] (w[m]'(by lia)) = true :=
    fun r hr => hmax r ⟨m, by lia⟩ hr rfl
  grind

/-- A swap strictly below the boundary `b` preserves the sorted suffix `[b, n)`. -/
private lemma sortedFrom_swap (le : α → α → Bool) (w : Vector α n) (m b : Nat)
    (hm : m + 1 < n) (hmb : m + 1 < b) (hsort : SortedFrom le w b) :
    SortedFrom le ((w.set m (w[m + 1]'hm) (by lia)).set (m + 1) (w[m]'(by lia)) hm) b := by
  intro p q hp hq
  have e_m := hsort ⟨m, by lia⟩ q (show m ≤ (q : Nat) by lia) hq
  have e_m1 := hsort ⟨m + 1, hm⟩ q (show m + 1 ≤ (q : Nat) by lia) hq
  have hpq := hsort p q hp hq
  grind

/-- The prefix maximum at `k` extends a sorted suffix `[k+1, n)` to `[k, n)`. -/
private lemma sortedFrom_of_maxAt (le : α → α → Bool) (w : Vector α n) (k : Nat)
    (hmax : MaxAt le w k) (hsort : SortedFrom le w (k + 1)) : SortedFrom le w k := by
  intro p q hp hq
  rcases Nat.lt_or_ge (q : Nat) (k + 1) with h | h
  · exact hmax p q (by lia) (by lia)
  · exact hsort p q hp h

/-- The prefix maximum at `0` is trivial: `w[0] ≥ w[0]`. -/
private lemma maxAt_zero (le : α → α → Bool) (hrefl : ∀ a, le a a = true) (w : Vector α n) :
    MaxAt le w 0 := by
  intro p q hp hq
  obtain rfl : p = q := by ext; lia
  exact hrefl _

/-- `SortedFrom le w 0` is exactly sortedness of the underlying list. -/
private lemma sortedFrom_zero_pairwise {le : α → α → Bool} {w : Vector α n}
    (h : SortedFrom le w 0) : w.toList.Pairwise (fun a b => le a b = true) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj _
  simpa [Vector.getElem_toList] using
    h ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩ (by simp; lia) (Nat.zero_le _)

private lemma sub_one_sub_add (k : Nat) (h : k < n) : n - 1 - k + 1 = n - k := by lia
private lemma sub_succ (k : Nat) : n - (k + 1) = n - 1 - k := by lia

/-! ### Hoare specs via `mvcgen`

The two single-loop proofs that carry the work: each calls `mvcgen` with one hand-supplied loop
invariant, then discharges the (concrete, `grind`-friendly) verification conditions. -/

set_option mvcgen.warning false in
/-- One pass deposits the maximum of `[0, bound]` at `bound`, preserves the sorted suffix above,
and permutes the vector. -/
theorem bubblePass_spec (le : α → α → Bool) [Std.Total (fun a b : α => le a b = true)]
    [IsTrans α (fun a b => le a b = true)]
    (bound : Nat) (hb : bound < n) (v : Vector α n) (hpre : SortedFrom le v (bound + 1)) :
    ⦃⌜True⌝⦄ bubblePass le bound hb v
      ⦃⇓w => ⌜MaxAt le w bound ∧ SortedFrom le w (bound + 1) ∧ w.toList.Perm v.toList⌝⦄ := by
  mvcgen [bubblePass] invariants
    · ⇓⟨xs, w⟩ => ⌜MaxAt le w xs.prefix.length ∧ SortedFrom le w (bound + 1)
        ∧ w.toList.Perm v.toList⌝
  case vc3.pre =>
    simp only [List.length_nil]
    exact ⟨maxAt_zero le (Std.Refl.refl (r := fun a b : α => le a b = true)) v,
      hpre, List.Perm.refl _⟩
  case vc4.post.success =>
    obtain ⟨h1, h2, h3⟩ := ‹MaxAt le _ _ ∧ SortedFrom le _ _ ∧ List.Perm _ _›
    rw [List.length_finRange] at h1
    exact ⟨h1, h2, h3⟩
  case vc1.step.isTrue =>
    obtain ⟨hmax, hsort, hperm⟩ := ‹MaxAt le _ _ ∧ SortedFrom le _ _ ∧ List.Perm _ _›
    have hc := fin_cur_eq ‹List.finRange bound = _ ++ _ :: _›
    have hcb := (‹Fin bound› : Fin bound).isLt
    have hcmp := ‹(!le _ _) = true›
    simp only [Vec.hasModel_model, Bool.not_eq_true',
      List.length_append, List.length_cons, List.length_nil, ← hc] at hmax hcmp hcb ⊢
    exact ⟨maxAt_swap le Std.Total.total _ _ (by grind) hmax hcmp,
      sortedFrom_swap le _ _ _ (by grind) (by grind) hsort,
      (set_set_toList_perm _ _ _ (by grind) (by grind)).trans hperm⟩
  case vc2.step.isFalse =>
    obtain ⟨hmax, hsort, hperm⟩ := ‹MaxAt le _ _ ∧ SortedFrom le _ _ ∧ List.Perm _ _›
    have hc := fin_cur_eq ‹List.finRange bound = _ ++ _ :: _›
    have hcb := (‹Fin bound› : Fin bound).isLt
    have hns := ‹¬(!le _ _) = true›
    simp only [Vec.hasModel_model, Bool.not_eq_true,
      Bool.not_eq_false', List.length_append, List.length_cons, List.length_nil, ← hc]
      at hmax hns hcb ⊢
    exact ⟨maxAt_noswap le Std.Total.total IsTrans.trans _ _ (by lia) hmax hns, hsort, hperm⟩

set_option mvcgen.warning false in
/-- `bubbleSort` is correct: it sorts and permutes its input (for a total, transitive `le`). -/
theorem bubbleSort_spec (le : α → α → Bool) [Std.Total (fun a b : α => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (v : Vector α n) :
    ⦃⌜True⌝⦄ bubbleSort le v ⦃⇓w => ⌜SortedFrom le w 0 ∧ w.toList.Perm v.toList⌝⦄ := by
  mvcgen [bubbleSort, bubblePass_spec] invariants
    · ⇓⟨xs, w⟩ => ⌜SortedFrom le w (n - xs.prefix.length) ∧ w.toList.Perm v.toList⌝
  case vc1.hpre =>
    have hsort := (‹SortedFrom le _ _ ∧ List.Perm _ _›).1
    have hcb := (‹Fin n› : Fin n).isLt
    rw [fin_cur_eq ‹List.finRange n = _ ++ _ :: _›] at hcb ⊢
    rwa [sub_one_sub_add _ hcb]
  case vc2.step.success =>
    obtain ⟨hmax, hsort, hperm⟩ := ‹MaxAt le _ _ ∧ SortedFrom le _ _ ∧ List.Perm _ _›
    have hperm0 := (‹SortedFrom le _ _ ∧ List.Perm _ _›).2
    have key := sortedFrom_of_maxAt le _ _ hmax hsort
    rw [fin_cur_eq ‹List.finRange n = _ ++ _ :: _›] at key
    exact ⟨by simp only [List.length_append, List.length_cons, List.length_nil]; rwa [sub_succ],
      hperm.trans hperm0⟩
  case vc3.pre =>
    exact ⟨fun p q _ hq => absurd (by simpa using hq) (by have := q.isLt; lia), List.Perm.refl _⟩
  case vc4.post.success =>
    obtain ⟨h1, h2⟩ := ‹SortedFrom le _ _ ∧ List.Perm _ _›
    rw [List.length_finRange, Nat.sub_self] at h1
    exact ⟨h1, h2⟩

/-- `bubbleSort` returns a permutation of its input. -/
theorem bubbleSort_perm (le : α → α → Bool) [Std.Total (fun a b : α => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (v : Vector α n) :
    ((bubbleSort le v).eval Vec.natCost).toList.Perm v.toList :=
  (eval_of_triple (bubbleSort_spec le v)).2

/-- `bubbleSort` returns a sorted vector, for a total and transitive `le`. -/
theorem bubbleSort_sorted (le : α → α → Bool) [Std.Total (fun a b : α => le a b = true)]
    [IsTrans α (fun a b => le a b = true)] (v : Vector α n) :
    ((bubbleSort le v).eval Vec.natCost).toList.Pairwise (fun a b => le a b = true) :=
  sortedFrom_zero_pairwise (eval_of_triple (bubbleSort_spec le v)).1

end Algorithms

end Algolean
