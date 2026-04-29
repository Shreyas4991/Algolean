/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.Models.Comparison
public import Batteries.Data.List.Lemmas
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Intervals
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Range

@[expose] public section

/-!
# Knuth-Morris-Pratt pattern search

In this file we define the KMP search algorithm for finding all exact occurrences of a pattern
in a text, along with the longest-proper-prefix / suffix table used by KMP. We also prove
correctness and an upper bound for equality comparisons in the `Comparison` query model.
--

## Main definitions
- `buildLPS`: builds the longest-proper-prefix / suffix table for a pattern.
- `kmpSearchPositions`: returns all starting positions where a pattern occurs in a text.

## Main results

- `buildLPS_eval`: `buildLPS` evaluates identically to the standard LPS table definition.
- `kmpPatternSearch_eval`: `kmpSearchPositions` evaluates identically to `PatternSearchAll`.
- `buildLPS_time_complexity_upper_bound`: `buildLPS` takes at most
  `2 * (pat.length - 1)` comparisons.
- `kmpSearchPositions_time_complexity_upper_bound`: `kmpSearchPositions` takes at most
  `2 * (txt.length + pat.length - 1)` comparisons.


## References
1. [KMP Algorithm](https://www.geeksforgeeks.org/dsa/kmp-algorithm-for-pattern-searching/)
-/

namespace Algolean

namespace Algorithms

open Cslib Prog Comparison

/--
`buildLPSLoop fuel pos len pat lps` fills the standard KMP longest-prefix-suffix table.

It mirrors the usual imperative loop:
- `pos` is the index currently being filled,
- `len` is the current matched prefix length,
- `lps` stores the entries computed so far.

The extra `fuel` parameter bounds the recursion. Each recursive step consumes one unit
of fuel exactly when the loop performs a comparison, and `buildLPS` initializes it with
the standard `2 * (pat.length - 1)` KMP budget.
-/
def buildLPSLoop [BEq α]
    (fuel pos len : Nat) (pat : List α) (lps : List Nat) :
    Prog (Comparison α) (List Nat) := do
  if pos < pat.length then
    match fuel with
    | 0 =>
        return lps
    | fuel + 1 =>
        match pat[pos]?, pat[len]? with
        | some p, some q =>
            let same : Bool ← compare p q
            if same then
              let len' := len + 1
              buildLPSLoop fuel (pos + 1) len' pat (lps.set pos len')
            else if len = 0 then
              buildLPSLoop fuel (pos + 1) 0 pat (lps.set pos 0)
            else
              let len' := (lps[len - 1]?).getD 0
              buildLPSLoop fuel pos len' pat lps
        | _, _ =>
            return lps
  else
    return lps

/--
`buildLPS pat` constructs the standard KMP longest-prefix-suffix table for `pat`.

The returned list has the same length as `pat`, and the entry at index `i` is the length
of the longest proper prefix of `pat.take (i + 1)` that is also a suffix of it.
-/
def buildLPS [BEq α] (pat : List α) : Prog (Comparison α) (List Nat) := do
  match pat with
  | [] =>
      return []
  | _ =>
      buildLPSLoop (2 * (pat.length - 1)) 1 0 pat (List.replicate pat.length 0)

/--
`kmpSearchLoop fuel i j pat txt lps acc` executes the KMP scan after the LPS table
has already been built.

It mirrors the usual imperative search loop:
- `i` is the current text position,
- `j` is the current pattern position,
- `lps` is the precomputed longest-prefix-suffix table,
- `acc` stores matches found so far in reverse order.

As with `buildLPSLoop`, the `fuel` parameter bounds recursion by the number of
comparisons available to the search phase.
-/
def kmpSearchLoop [BEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat) :
    Prog (Comparison α) (List Nat) := do
  if i < txt.length then
    match fuel with
    | 0 =>
        return acc.reverse
    | fuel + 1 =>
        match txt[i]?, pat[j]? with
        | some t, some p =>
            let same : Bool ← compare t p
            if same then
              let i' := i + 1
              let j' := j + 1
              if j' = pat.length then
                let acc' := (i' - j') :: acc
                let j'' := (lps[j' - 1]?).getD 0
                kmpSearchLoop fuel i' j'' pat txt lps acc'
              else
                kmpSearchLoop fuel i' j' pat txt lps acc
            else if j = 0 then
              kmpSearchLoop fuel (i + 1) 0 pat txt lps acc
            else
              let j' := (lps[j - 1]?).getD 0
              kmpSearchLoop fuel i j' pat txt lps acc
        | _, _ =>
            return acc.reverse
  else
    return acc.reverse

/--
`kmpSearchPositions pat txt` returns the starting positions of all occurrences of `pat`
inside `txt`, in increasing order.

For the empty pattern, this matches `PatternSearchAll` and returns every position inside
the text, namely `0, 1, ..., txt.length - 1`.
-/
def kmpSearchPositions [BEq α] (pat txt : List α) : Prog (Comparison α) (List Nat) := do
  match pat with
  | [] =>
      return List.range txt.length
  | _ =>
      let lps ← buildLPS pat
      kmpSearchLoop (2 * txt.length) 0 0 pat txt lps []

section Correctness

/--
`PrefixSuffixOf pat n l` says that `l` is a proper prefix-length of `pat.take n`
whose prefix is also a suffix of that same length.
-/
def PrefixSuffixOf (pat : List α) (n l : Nat) : Prop :=
  l < n ∧ ∀ j, j < l → pat[j]? = pat[n - l + j]?

/--
`LongestPrefixSuffixOf pat n l` says that `l` is the maximum proper prefix/suffix
length for `pat.take n`.
-/
def LongestPrefixSuffixOf (pat : List α) (n l : Nat) : Prop :=
  PrefixSuffixOf pat n l ∧ ∀ l', PrefixSuffixOf pat n l' → l' ≤ l

private def EntriesCorrect (pat : List α) (pos : Nat) (lps : List Nat) : Prop :=
  ∀ i, i < pos → ∃ l, lps[i]? = some l ∧ LongestPrefixSuffixOf pat (i + 1) l

private def SearchInvariant (pat : List α) (pos len : Nat) : Prop :=
  PrefixSuffixOf pat pos len ∧
    ∀ m, len < m → m < pos → PrefixSuffixOf pat pos m → pat[m]? ≠ pat[pos]?

private lemma prefixSuffix_succ_iff :
    PrefixSuffixOf pat (n + 1) (l + 1) ↔
      PrefixSuffixOf pat n l ∧ pat[l]? = pat[n]? := by
  constructor
  · intro h
    refine ⟨⟨Nat.lt_of_succ_lt_succ h.1, ?_⟩, ?_⟩
    · intro j hj
      simpa [Nat.succ_sub_succ_eq_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        h.2 j (Nat.lt_trans hj (Nat.lt_succ_self _))
    · have := h.2 l (Nat.lt_succ_self l)
      have hle : l ≤ n := Nat.le_of_lt (Nat.lt_of_succ_lt_succ h.1)
      simpa [Nat.succ_sub_succ_eq_sub, Nat.sub_add_cancel hle, Nat.add_comm] using this
  · rintro ⟨h, hlast⟩
    refine ⟨Nat.succ_lt_succ h.1, ?_⟩
    intro j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj' | rfl
    · simpa [Nat.succ_sub_succ_eq_sub, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        h.2 j hj'
    · simpa [Nat.succ_sub_succ_eq_sub, Nat.sub_add_cancel (Nat.le_of_lt h.1)] using hlast

private lemma prefixSuffix_trans
    (h₁ : PrefixSuffixOf pat m l) (h₂ : PrefixSuffixOf pat n m) :
    PrefixSuffixOf pat n l := by
  refine ⟨lt_trans h₁.1 h₂.1, fun j hj => ?_⟩
  have hjm : m - l + j < m := by have := h₁.1; omega
  calc pat[j]? = pat[m - l + j]? := h₁.2 j hj
    _ = pat[n - m + (m - l + j)]? := h₂.2 _ hjm
    _ = pat[n - l + j]? := by congr 1; have := h₁.1; have := h₂.1; omega

private lemma prefixSuffix_of_lt_of_prefixSuffix
    (h₁ : PrefixSuffixOf pat n l) (h₂ : PrefixSuffixOf pat n m) (hlm : l < m) :
    PrefixSuffixOf pat m l := by
  refine ⟨hlm, fun j hj => ?_⟩
  calc pat[j]? = pat[n - l + j]? := h₁.2 j hj
    _ = pat[n - m + (m - l + j)]? := by congr 1; have := h₂.1; omega
    _ = pat[m - l + j]? := (h₂.2 _ (by omega)).symm

private lemma searchInvariant_match_longest
    (hs : SearchInvariant pat pos len) (hmatch : pat[len]? = pat[pos]?) :
    LongestPrefixSuffixOf pat (pos + 1) (len + 1) := by
  refine ⟨(prefixSuffix_succ_iff).2 ⟨hs.1, hmatch⟩, ?_⟩
  intro l' hl'
  cases l' with
  | zero => omega
  | succ m =>
      rcases (prefixSuffix_succ_iff).1 hl' with ⟨hm, hm'⟩
      by_cases hml : len < m
      · exact (hs.2 m hml hm.1 hm hm').elim
      · omega

private lemma searchInvariant_zero_longest
    (hs : SearchInvariant pat pos 0) (hmis : pat[0]? ≠ pat[pos]?) :
    LongestPrefixSuffixOf pat (pos + 1) 0 := by
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · intro j hj
    omega
  intro l' hl'
  cases l' with
  | zero => omega
  | succ m =>
      rcases (prefixSuffix_succ_iff).1 hl' with ⟨hm, hm'⟩
      cases m with
      | zero => exact (hmis hm').elim
      | succ m =>
          exact (hs.2 (m + 1) (by omega) hm.1 hm hm').elim

private lemma searchInvariant_fallback
    (hs : SearchInvariant pat pos len)
    (hlong : LongestPrefixSuffixOf pat len len')
    (hmis : pat[len]? ≠ pat[pos]?) :
    SearchInvariant pat pos len' := by
  refine ⟨prefixSuffix_trans hlong.1 hs.1, fun m hm hmpos hm' => ?_⟩
  rcases lt_trichotomy m len with hml | rfl | hml
  · exact fun _ => absurd (hlong.2 m (prefixSuffix_of_lt_of_prefixSuffix hm' hs.1 hml)) (by omega)
  · exact hmis
  · exact hs.2 m (by omega) hmpos hm'

private lemma entriesCorrect_set
    (h : EntriesCorrect pat pos lps)
    (hi : pos < lps.length)
    (hlong : LongestPrefixSuffixOf pat (pos + 1) l) :
    EntriesCorrect pat (pos + 1) (lps.set pos l) := by
  intro i hi'
  by_cases hEq : i = pos
  · subst hEq; exact ⟨l, List.getElem?_set_eq_of_lt _ hi, hlong⟩
  · obtain ⟨x, hx, hx'⟩ := h i (by omega)
    exact ⟨x, by grind [List.getElem?_set_of_lt], hx'⟩

private lemma buildLPSLoop_correct
    [BEq α] [LawfulBEq α]
    (fuel pos len : Nat) (pat : List α) (lps : List Nat)
    (hpot : 2 * (pat.length - pos) + len ≤ fuel)
    (hpos : pos ≤ pat.length)
    (hlen : lps.length = pat.length)
    (hentries : EntriesCorrect pat pos lps)
    (hs : SearchInvariant pat pos len) :
    let out := (buildLPSLoop fuel pos len pat lps).eval Comparison.natCost
    out.length = pat.length ∧ EntriesCorrect pat pat.length out := by
  induction fuel generalizing pos len lps with
  | zero =>
      have hEq : pos = pat.length := by omega
      subst hEq; simp [buildLPSLoop, hlen]; simpa [EntriesCorrect] using hentries
  | succ fuel ih =>
      by_cases hpos' : pos < pat.length
      · have hlen' : len < pat.length := lt_trans hs.1.1 hpos'
        by_cases hcmp : pat[pos]'hpos' = pat[len]'hlen'
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = true := by simp [hcmp]
          have hmatch : pat[len]? = pat[pos]? := by
            simp [List.getElem?_eq_getElem hlen', List.getElem?_eq_getElem hpos', hcmp]
          have hlong := searchInvariant_match_longest hs hmatch
          have hrec := ih (pos + 1) (len + 1) (lps.set pos (len + 1))
            (by omega) (by omega) (by simpa [List.length_set] using hlen)
            (entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong)
            ⟨hlong.1, fun m hm _ hm' _ => absurd (hlong.2 m hm') (by omega)⟩
          simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
            List.getElem?_eq_getElem hlen', hcmp'] using hrec
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = false := by simp [hcmp]
          by_cases hzero : len = 0
          · subst hzero
            have hmis : pat[0]? ≠ pat[pos]? := by
              grind [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hpos']
            have hlong := searchInvariant_zero_longest hs hmis
            have hrec := ih (pos + 1) 0 (lps.set pos 0)
              (by omega) (by omega) (by simpa [List.length_set] using hlen)
              (entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong)
              ⟨hlong.1, fun m hm _ hm' _ => absurd (hlong.2 m hm') (by omega)⟩
            simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
              List.getElem?_eq_getElem (by omega : 0 < pat.length), hcmp'] using hrec
          · obtain ⟨len', hlen'', hlong⟩ := hentries (len - 1) (by have := hs.1.1; omega)
            have hlong' : LongestPrefixSuffixOf pat len len' := by
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ len)] using hlong
            have hmis : pat[len]? ≠ pat[pos]? := by
              grind [List.getElem?_eq_getElem hlen', List.getElem?_eq_getElem hpos']
            have hrec := ih pos len' lps
              (by have := hlong'.1.1; omega) hpos hlen hentries
              (searchInvariant_fallback hs hlong' hmis)
            simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
              List.getElem?_eq_getElem hlen', hcmp', hzero, hlen''] using hrec
      · have hEq : pos = pat.length := by omega
        subst hEq; simp [buildLPSLoop, hlen]; simpa [EntriesCorrect] using hentries

/--
Correctness of `buildLPS`: every entry of the produced LPS table is the longest proper
prefix/suffix length for the corresponding prefix of the pattern.
-/
theorem buildLPS_eval [BEq α] [LawfulBEq α] (pat : List α) :
    let lps := (buildLPS pat).eval Comparison.natCost
    ∃ hlen : lps.length = pat.length,
      ∀ i (hi : i < pat.length),
        LongestPrefixSuffixOf pat (i + 1) (lps[i]'(by simpa [hlen] using hi)) := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      let lps0 := List.replicate (List.length (x :: xs)) 0
      obtain ⟨hlen, hentries⟩ := buildLPSLoop_correct
        (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0
        (by simp) (by simp) (by simp [lps0])
        (by
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          refine ⟨0, ?_, ?_⟩
          · simp [lps0]
          · refine ⟨⟨by omega, nofun⟩, ?_⟩
            intro l hl
            have := hl.1
            omega)
        ⟨⟨by omega, nofun⟩, fun m hm _ hm' => by grind⟩
      refine ⟨by simpa [buildLPS, lps0] using hlen, fun i hi => ?_⟩
      obtain ⟨l, hlps, hlong⟩ := hentries i hi
      have hilen : i < ((buildLPSLoop _ 1 0 _ lps0).eval Comparison.natCost).length := hlen ▸ hi
      have hget : ((buildLPSLoop _ 1 0 _ lps0).eval Comparison.natCost)[i]'hilen = l := by
        have hout :
            ((buildLPSLoop _ 1 0 _ lps0).eval Comparison.natCost)[i]? =
              some (((buildLPSLoop _ 1 0 _ lps0).eval Comparison.natCost)[i]'hilen) :=
          List.getElem?_eq_getElem hilen
        rw [hout] at hlps
        exact Option.some.inj hlps
      have hget' :
          ((buildLPS (x :: xs)).eval Comparison.natCost)[i]'(by
            simpa [buildLPS, lps0] using hilen) = l := by
        simpa [buildLPS, lps0] using hget
      rw [hget']
      exact hlong

private def MatchAt (pat txt : List α) (start len : Nat) : Prop :=
  ∀ k, k < len → txt[start + k]? = pat[k]?

private lemma matchAt_zero (pat txt : List α) (start : Nat) : MatchAt pat txt start 0 :=
  nofun

private lemma matchAt_succ
    (pat txt : List α) (start len : Nat)
    (hmatch : MatchAt pat txt start len)
    (hlast : txt[start + len]? = pat[len]?) :
    MatchAt pat txt start (len + 1) := by
  intro k hk
  obtain hk' | rfl := lt_or_eq_of_le (Nat.le_of_lt_succ hk)
  · exact hmatch k hk'
  · simpa using hlast

private lemma prefix_iff_matchAt [BEq α] [LawfulBEq α]
    (pat txt : List α) (start : Nat) :
    pat <+: txt.drop start ↔ MatchAt pat txt start pat.length := by
  simp only [List.prefix_iff_getElem?, MatchAt]
  constructor <;> intro h k hk <;>
    simpa [List.getElem?_drop, List.getElem?_eq_getElem hk] using h k hk

private lemma isPrefixOf_eq_true_iff_prefix [BEq α] [LawfulBEq α]
    (xs ys : List α) :
    xs.isPrefixOf ys = true ↔ xs <+: ys := by
  rw [← List.isSome_isPrefixOf?_eq_isPrefixOf]
  constructor
  · intro h
    obtain ⟨zs, hopt⟩ := Option.isSome_iff_exists.mp h
    exact ⟨zs, (List.isPrefixOf?_eq_some_iff_append_eq).1 hopt⟩
  · rintro ⟨zs, rfl⟩
    simp

private lemma isPrefixOf_drop_eq_true_iff_matchAt [BEq α] [LawfulBEq α]
    (pat txt : List α) (start : Nat) :
    pat.isPrefixOf (txt.drop start) = true ↔ MatchAt pat txt start pat.length := by
  rw [isPrefixOf_eq_true_iff_prefix pat (txt.drop start), prefix_iff_matchAt pat txt start]

private lemma occurrence_of_matchAt [BEq α] [LawfulBEq α]
    (pat txt : List α) (start : Nat)
    (hmatch : MatchAt pat txt start pat.length) :
    pat.isPrefixOf (txt.drop start) = true :=
  (isPrefixOf_drop_eq_true_iff_matchAt pat txt start).2 hmatch

private lemma no_occurrence_of_length [BEq α] [LawfulBEq α]
    (pat txt : List α) (start : Nat)
    (hpat : 0 < pat.length)
    (hshort : txt.length < start + pat.length) :
    pat.isPrefixOf (txt.drop start) = false := by
  grind

private lemma matchAt_of_prefixSuffix
    (pat txt : List α) (start n l : Nat)
    (hmatch : MatchAt pat txt start n)
    (hps : PrefixSuffixOf pat n l) :
    MatchAt pat txt (start + (n - l)) l := by
  intro k hk
  calc txt[start + (n - l) + k]? = txt[start + (n - l + k)]? := by rw [Nat.add_assoc]
    _ = pat[n - l + k]? := by simpa using hmatch (n - l + k) (by have := hps.1; omega)
    _ = pat[k]? := (hps.2 k hk).symm

private lemma prefixSuffix_of_overlap
    (pat txt : List α) (s t n : Nat)
    (hnp : n ≤ pat.length)
    (hmatch : MatchAt pat txt s n)
    (hocc : MatchAt pat txt t pat.length)
    (hst : s < t)
    (ht : t ≤ s + n) :
    PrefixSuffixOf pat n (n - (t - s)) := by
  refine ⟨by omega, fun k hk => ?_⟩
  calc pat[k]? = txt[t + k]? := by simpa using (hocc k (by omega)).symm
    _ = txt[s + (t - s + k)]? := by congr 1; omega
    _ = pat[t - s + k]? := by simpa using hmatch (t - s + k) (by omega)
    _ = pat[n - (n - (t - s)) + k]? := by congr 1; omega

private lemma no_occurrence_between_full_match_and_fallback [BEq α] [LawfulBEq α]
    (pat txt : List α) (s l : Nat)
    (hfull : MatchAt pat txt s pat.length)
    (hlong : LongestPrefixSuffixOf pat pat.length l) :
    ∀ t, s < t → t < s + (pat.length - l) → pat.isPrefixOf (txt.drop t) = false := by
  intro t hst htl
  exact Bool.eq_false_iff.mpr fun ht =>
    absurd (hlong.2 _ (prefixSuffix_of_overlap pat txt s t _ le_rfl hfull
      ((isPrefixOf_drop_eq_true_iff_matchAt pat txt t).1 ht) hst (by omega))) (by omega)

private lemma no_occurrence_between_partial_and_fallback [BEq α] [LawfulBEq α]
    (pat txt : List α) (s j l : Nat)
    (hj : j < pat.length)
    (hmatch : MatchAt pat txt s j)
    (hlong : LongestPrefixSuffixOf pat j l)
    (hmis : pat[j]? ≠ txt[s + j]?) :
    ∀ t, s ≤ t → t < s + (j - l) → pat.isPrefixOf (txt.drop t) = false := by
  intro t hst htl
  apply Bool.eq_false_iff.mpr; intro ht
  have hocc := (isPrefixOf_drop_eq_true_iff_matchAt pat txt t).1 ht
  rcases eq_or_lt_of_le hst with rfl | hst'
  · exact hmis (hocc j hj).symm
  · exact absurd (hlong.2 _ (prefixSuffix_of_overlap pat txt s t j
      (Nat.le_of_lt hj) hmatch hocc hst' (by omega))) (by omega)

private lemma ico_filter_eq_nil_of_false
    (P : Nat → Bool) (s u : Nat)
    (hfalse : ∀ t, s ≤ t → t < u → P t = false) :
    (List.Ico s u).filter P = [] := by
  apply (List.filter_eq_nil_iff).2
  grind [List.Ico.mem]

private lemma acc_shift_no_matches
    (P : Nat → Bool) (acc : List Nat) (s u : Nat)
    (hacc : acc.reverse = (List.Ico 0 s).filter P)
    (hsu : s ≤ u)
    (hfalse : ∀ t, s ≤ t → t < u → P t = false) :
    acc.reverse = (List.Ico 0 u).filter P := by
  simp [hacc, ← List.Ico.append_consecutive (Nat.zero_le s) hsu, List.filter_append,
    ico_filter_eq_nil_of_false P s u hfalse]

private lemma acc_record_match
    (P : Nat → Bool) (acc : List Nat) (s u : Nat)
    (hacc : acc.reverse = (List.Ico 0 s).filter P)
    (hsu : s < u)
    (htrue : P s = true)
    (hfalse : ∀ t, s < t → t < u → P t = false) :
    (s :: acc).reverse = (List.Ico 0 u).filter P := by
  have htail := ico_filter_eq_nil_of_false P (s + 1) u (fun t ht htu => hfalse t (by omega) htu)
  simp only [List.reverse_cons, hacc,
    ← List.Ico.append_consecutive (Nat.zero_le s) (Nat.le_of_lt hsu),
    List.filter_append, List.Ico.eq_cons hsu, htrue, htail, List.filter_cons, ite_true]

private lemma kmpSearchLoop_exhausted [BEq α] [LawfulBEq α]
    (j : Nat) (pat txt : List α) (acc : List Nat)
    (hj : j < pat.length)
    (hacc : acc.reverse = (List.Ico 0 (txt.length - j)).filter fun s =>
      pat.isPrefixOf (txt.drop s)) :
    acc.reverse = (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) :=
  acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
    acc (txt.length - j) txt.length hacc (by omega)
    (fun t ht1 ht2 => no_occurrence_of_length pat txt t (by omega) (by omega))

private lemma kmpSearchLoop_correct [BEq α] [LawfulBEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat)
    (hpot : 2 * (txt.length - i) + j ≤ fuel)
    (hi : i ≤ txt.length)
    (hlen : lps.length = pat.length)
    (hlps :
      ∀ k (hk : k < pat.length),
        LongestPrefixSuffixOf pat (k + 1) (lps[k]'(by simpa [hlen] using hk)))
    (hj : j < pat.length)
    (hji : j ≤ i)
    (hmatch : MatchAt pat txt (i - j) j)
    (hacc :
      acc.reverse = (List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) :
    (kmpSearchLoop fuel i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) := by
  induction fuel generalizing i j acc with
  | zero =>
      have : i = txt.length := by omega
      subst this
      simpa [kmpSearchLoop] using kmpSearchLoop_exhausted j pat txt acc hj hacc
  | succ fuel ih =>
      by_cases hit : i < txt.length
      · by_cases hcmp : txt[i]'hit = pat[j]'hj
        · -- characters match
          have hmatch' : MatchAt pat txt (i - j) (j + 1) :=
            matchAt_succ pat txt (i - j) j hmatch (by
              simp [show (i - j) + j = i by omega, List.getElem?_eq_getElem hit,
                List.getElem?_eq_getElem hj, hcmp])
          by_cases hfull : j + 1 = pat.length
          · -- full match
            let l := lps[j]'(by simpa [hlen] using hj)
            have hlong : LongestPrefixSuffixOf pat pat.length l := by simpa [hfull] using hlps j hj
            have hfullMatch : MatchAt pat txt (i - j) pat.length := by simpa [hfull] using hmatch'
            have hlj : l ≤ j := by grind [hlong.1.1]
            have hstart : (i + 1) - (j + 1) = i - j := by omega
            have hshift : (i - j) + (pat.length - l) = (i + 1) - l := by omega
            have hrec := ih (i + 1) l (((i + 1) - (j + 1)) :: acc)
              (by omega) (by omega) hlong.1.1 (by omega)
              (by simpa [hshift] using
                matchAt_of_prefixSuffix pat txt (i - j) pat.length l hfullMatch hlong.1)
              (by
                simpa [hstart, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using
                  (acc_record_match
                    (P := fun s => pat.isPrefixOf (txt.drop s))
                    acc (i - j) ((i + 1) - l) hacc (by omega)
                    (occurrence_of_matchAt pat txt (i - j) hfullMatch)
                    (fun t ht1 ht2 =>
                      no_occurrence_between_full_match_and_fallback pat txt (i - j)
                        l hfullMatch hlong t ht1 (by simpa [hshift] using ht2))))
            have hjEq : j = pat.length - 1 := by omega
            have hlpsj : lps[j]? = some l := List.getElem?_eq_getElem (by simpa [hlen] using hj)
            simpa [kmpSearchLoop, hit, List.getElem?_eq_getElem hit,
              List.getElem?_eq_getElem hj, hcmp, hjEq, hfull,
              show pat.length - 1 + 1 = pat.length by omega,
              show (txt[i]'hit == pat[pat.length - 1]'(by omega)) = true by simp [hjEq, hcmp],
              List.getElem?_eq_getElem (l := pat) (i := pat.length - 1) (by omega),
              hlpsj, show lps[pat.length - 1]? = some l by simpa [hjEq] using hlpsj,
              Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrec
          · -- partial match, continue
            have hrec := ih (i + 1) (j + 1) acc
              (by omega) (by omega) (by omega) (by omega)
              (by simpa using hmatch') (by simpa using hacc)
            simpa [kmpSearchLoop, hit, List.getElem?_eq_getElem hit,
              List.getElem?_eq_getElem hj, hcmp, hfull] using hrec
        · -- characters don't match
          have hmis : pat[j]? ≠ txt[i]? := by
            grind [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hit]
          by_cases hzero : j = 0
          · subst hzero
            have hrec := ih (i + 1) 0 acc (by omega) (by omega)
              (by cases pat with | nil => cases hj | cons x xs => simp)
              (by omega) (matchAt_zero pat txt (i + 1))
              (acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
                acc i (i + 1) hacc (by omega) (fun t _ _ => by
                  simpa [show t = i by omega] using Bool.eq_false_iff.mpr fun h =>
                    hmis ((isPrefixOf_drop_eq_true_iff_matchAt pat txt i).1 h 0 (by omega)).symm))
            simpa [kmpSearchLoop, hit, List.getElem?_eq_getElem hit,
              List.getElem?_eq_getElem (by omega : 0 < pat.length), hcmp] using hrec
          · -- fallback via LPS table
            have hj1 : j - 1 < pat.length := by omega
            let l := lps[j - 1]'(by simpa [hlen] using hj1)
            have hlong : LongestPrefixSuffixOf pat j l := by
              simpa [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hlps (j - 1) hj1
            have hrec := ih i l acc (by have := hlong.1.1; omega) hi
              (lt_trans hlong.1.1 hj) (Nat.le_trans (Nat.le_of_lt hlong.1.1) hji)
              (by simpa [show (i - j) + (j - l) = i - l by have := hlong.1.1; omega] using
                matchAt_of_prefixSuffix pat txt (i - j) j l hmatch hlong.1)
              (acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
                acc (i - j) (i - l) hacc (Nat.sub_le_sub_left (Nat.le_of_lt hlong.1.1) i)
                (fun t ht1 ht2 => no_occurrence_between_partial_and_fallback pat txt (i - j) j l
                  hj hmatch hlong (by simpa [show (i - j) + j = i by omega] using hmis)
                  t ht1 (by omega)))
            simpa [kmpSearchLoop, hit, List.getElem?_eq_getElem hit,
              List.getElem?_eq_getElem hj, hcmp, hzero,
              show lps[j - 1]? = some l by simp [l]] using hrec
      · have : i = txt.length := by omega
        subst this
        simpa [kmpSearchLoop] using kmpSearchLoop_exhausted j pat txt acc hj hacc

/--
Correctness of KMP search: `kmpSearchPositions` finds exactly the occurrences returned by
`PatternSearchAll`.
-/
theorem kmpPatternSearch_eval [BEq α] [LawfulBEq α] (pat txt : List α) :
    (kmpSearchPositions pat txt).eval Comparison.natCost = PatternSearchAll pat txt := by
  cases pat with
  | nil =>
      simp [kmpSearchPositions, PatternSearchAll]
  | cons x xs =>
      rcases buildLPS_eval (x :: xs) with ⟨hlen, hlps⟩
      have hrec := kmpSearchLoop_correct
        (2 * txt.length) 0 0 (x :: xs) txt ((buildLPS (x :: xs)).eval Comparison.natCost) []
        (by omega)
        (by omega)
        hlen
        hlps
        (by simp)
        (by omega)
        (matchAt_zero (x :: xs) txt 0)
        (by simp)
      simpa [kmpSearchPositions, PatternSearchAll, List.Ico.zero_bot] using hrec

end Correctness

section TimeComplexity

private lemma buildLPSLoop_time_le_fuel [BEq α]
    (fuel pos len : Nat) (pat : List α) (lps : List Nat) :
    (buildLPSLoop fuel pos len pat lps).time Comparison.natCost ≤ fuel := by
  induction fuel generalizing pos len lps with
  | zero =>
      simp [buildLPSLoop]
  | succ fuel ih =>
      by_cases hpos : pos < pat.length
      · cases hlen : pat[len]? with
        | none =>
            simp [buildLPSLoop, hpos, hlen]
        | some q =>
            simp [buildLPSLoop, hpos, hlen]
            split_ifs with hsame hzero <;> grind
      · simp [buildLPSLoop, hpos]

private lemma kmpSearchLoop_time_le_fuel [BEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat) :
    (kmpSearchLoop fuel i j pat txt lps acc).time Comparison.natCost ≤ fuel := by
  induction fuel generalizing i j acc with
  | zero => by_cases hi : i < txt.length <;> simp [kmpSearchLoop, hi]
  | succ fuel ih =>
      by_cases hi : i < txt.length
      · cases hpat : pat[j]? with
        | none => simp [kmpSearchLoop, hi, hpat]
        | some p =>
            have hbranch : (if (txt[i] == p) = true then
                    if j + 1 = pat.length then
                      kmpSearchLoop fuel (i + 1) (lps[j]?.getD 0) pat txt lps ((i - j) :: acc)
                    else kmpSearchLoop fuel (i + 1) (j + 1) pat txt lps acc
                  else if j = 0 then kmpSearchLoop fuel (i + 1) 0 pat txt lps acc
                    else kmpSearchLoop fuel i (lps[j - 1]?.getD 0) pat txt lps acc
                ).time Comparison.natCost ≤ fuel := by
              split_ifs <;> apply ih
            simpa [kmpSearchLoop, hi, List.getElem?_eq_getElem hi, hpat, Prog.time_liftBind,
              Nat.add_comm] using
              Nat.add_le_add_left hbranch 1
      · simp [kmpSearchLoop, hi]

theorem buildLPS_time_complexity_upper_bound [BEq α] (pat : List α) :
    (buildLPS pat).time Comparison.natCost ≤ 2 * (pat.length - 1) := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      let lps0 := List.replicate (List.length (x :: xs)) 0
      simpa [buildLPS, lps0] using
        buildLPSLoop_time_le_fuel (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0

theorem kmpSearchPositions_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (kmpSearchPositions pat txt).time Comparison.natCost ≤ 2 * (txt.length + pat.length - 1) := by
  cases pat with
  | nil =>
      simp [kmpSearchPositions]
  | cons x xs =>
      simp only [kmpSearchPositions, Cslib.FreeM.bind_eq_bind, time_bind,
        List.length_cons, Nat.add_succ_sub_one]
      have hLps := by simpa using buildLPS_time_complexity_upper_bound (x :: xs)
      have hLoop := by
        simpa using
          (kmpSearchLoop_time_le_fuel (2 * txt.length) 0 0 (x :: xs)
            txt ((buildLPS (x :: xs)).eval Comparison.natCost) [])
      calc
        (buildLPS (x :: xs)).time Comparison.natCost +
            (kmpSearchLoop (2 * txt.length) 0 0 (x :: xs) txt
              ((buildLPS (x :: xs)).eval Comparison.natCost) []).time Comparison.natCost
            ≤ 2 * xs.length + 2 * txt.length := Nat.add_le_add hLps hLoop
        _ = 2 * (txt.length + xs.length) := by omega

end TimeComplexity

end Algorithms

end Algolean
