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
  `2 * pat.length - 3` comparisons.
- `buildLPS_time_complexity_lower_bound`: for every pattern length `n`, there exists a pattern
  on which `buildLPS` takes exactly `2 * n - 3` comparisons.
- `kmpSearchPositions_time_complexity_upper_bound`: `kmpSearchPositions` takes at most
  `2 * (txt.length + pat.length) - 3` comparisons.
- `kmpSearchPositions_time_complexity_lower_bound`: for every `m, n`, there exist a pattern of
  length `m + 1` and a text of length `n` on which `kmpSearchPositions` takes exactly
  `txt.length + (2 * pat.length - 3)` comparisons.


## References
1. [Knuth–Morris–Pratt algorithm](https://en.wikipedia.org/wiki/Knuth%E2%80%93Morris%E2%80%93Pratt_algorithm)
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
def buildLPSLoop
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
def buildLPS (pat : List α) : Prog (Comparison α) (List Nat) := do
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
def kmpSearchLoop
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
def kmpSearchPositions (pat txt : List α) : Prog (Comparison α) (List Nat) := do
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
  unfold PrefixSuffixOf; constructor
  · intro ⟨hlt, h⟩
    exact ⟨⟨by lia, fun j hj => by convert h j (by lia) using 2; lia⟩,
      by convert h l (by lia) using 2; lia⟩
  · rintro ⟨⟨hlt, h⟩, hlast⟩
    exact ⟨by lia, fun j hj => by
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hj'
      · convert hlast using 2; lia
      · convert h j hj' using 2; lia⟩

private lemma entriesCorrect_set
    (h : EntriesCorrect pat pos lps)
    (hi : pos < lps.length)
    (hlong : LongestPrefixSuffixOf pat (pos + 1) l) :
    EntriesCorrect pat (pos + 1) (lps.set pos l) := fun i hi' => by
  by_cases hEq : i = pos
  · simp_all
  · obtain ⟨x, _, hx'⟩ := h i (by lia)
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
      obtain rfl : pos = pat.length := by lia
      simpa [buildLPSLoop, hlen, EntriesCorrect] using hentries
  | succ fuel ih =>
      by_cases hpos' : pos < pat.length
      · have hlen' : len < pat.length := lt_trans hs.1.1 hpos'
        by_cases hcmp : pat[pos]'hpos' = pat[len]'hlen'
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = true := by simp [hcmp]
          have hmatch : pat[len]? = pat[pos]? := by simpa [hlen', hpos'] using hcmp.symm
          have hlong : LongestPrefixSuffixOf pat (pos + 1) (len + 1) := by
            refine ⟨prefixSuffix_succ_iff.2 ⟨hs.1, hmatch⟩, fun l' hl' => ?_⟩
            cases l' with
            | zero => lia
            | succ m =>
              rcases prefixSuffix_succ_iff.1 hl' with ⟨hm, hm'⟩
              by_cases hml : len < m
              · exact (hs.2 m hml hm.1 hm hm').elim
              · lia
          have hrec := ih (pos + 1) (len + 1) (lps.set pos (len + 1))
            (by lia) (by lia) (by simpa [List.length_set] using hlen)
            (entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong)
            ⟨hlong.1, fun m hm _ hm' _ => absurd (hlong.2 m hm') (by lia)⟩
          simpa [buildLPSLoop, hpos', getElem?_pos pat pos hpos', getElem?_pos pat len hlen', hcmp']
            using hrec
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = false := by simp [hcmp]
          by_cases hzero : len = 0
          · subst hzero
            have hmis : pat[0]? ≠ pat[pos]? := by grind
            have hlong : LongestPrefixSuffixOf pat (pos + 1) 0 := by
              refine ⟨⟨by lia, nofun⟩, fun l' hl' => ?_⟩
              cases l' with
              | zero => lia
              | succ m =>
                rcases prefixSuffix_succ_iff.1 hl' with ⟨hm, hm'⟩
                cases m with
                | zero => exact (hmis hm').elim
                | succ m => exact (hs.2 (m + 1) (by lia) hm.1 hm hm').elim
            have hrec := ih (pos + 1) 0 (lps.set pos 0)
              (by lia) (by lia) (by simpa [List.length_set] using hlen)
              (entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong)
              ⟨hlong.1, fun m hm _ hm' _ => absurd (hlong.2 m hm') (by lia)⟩
            simpa [buildLPSLoop, hpos', getElem?_pos pat pos hpos',
              getElem?_pos pat 0 (by lia : 0 < pat.length), hcmp'] using hrec
          · obtain ⟨len', hlen'', hlong⟩ := hentries (len - 1) (by have := hs.1.1; lia)
            have hlong' : LongestPrefixSuffixOf pat len len' := by
              simpa [Nat.sub_add_cancel (by lia : 1 ≤ len)] using hlong
            have hmis : pat[len]? ≠ pat[pos]? := by grind
            have hs' : SearchInvariant pat pos len' := by
              have hprefix : PrefixSuffixOf pat pos len' := by
                refine ⟨lt_trans hlong'.1.1 hs.1.1, fun j hj => ?_⟩
                calc pat[j]? = pat[len - len' + j]? := hlong'.1.2 j hj
                  _ = pat[pos - len + (len - len' + j)]? :=
                      hs.1.2 _ (by have := hlong'.1.1; lia)
                  _ = pat[pos - len' + j]? := by
                      congr 1; have := hlong'.1.1; have := hs.1.1; lia
              refine ⟨hprefix, fun m hm hmpos hm' => ?_⟩
              rcases lt_trichotomy m len with hml | rfl | hml
              · exact fun _ => absurd (hlong'.2 m (by
                    refine ⟨hml, fun j hj => ?_⟩
                    calc pat[j]? = pat[pos - m + j]? := hm'.2 j hj
                      _ = pat[pos - len + (len - m + j)]? := by congr 1; have := hs.1.1; lia
                      _ = pat[len - m + j]? := (hs.1.2 _ (by lia)).symm)) (by lia)
              · exact hmis
              · exact hs.2 m (by lia) hmpos hm'
            have hrec := ih pos len' lps
              (by have := hlong'.1.1; lia) hpos hlen hentries
              hs'
            simpa [buildLPSLoop, hpos', getElem?_pos pat pos hpos', getElem?_pos pat len hlen',
              hcmp', hzero,
              hlen''] using hrec
      · obtain rfl : pos = pat.length := by lia
        simpa [buildLPSLoop, hlen, EntriesCorrect] using hentries

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
  | nil => simp [buildLPS]
  | cons x xs =>
    let lps0 := List.replicate (List.length (x :: xs)) 0
    obtain ⟨hlen, hentries⟩ := buildLPSLoop_correct
      (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0
      (by simp) (by simp) (by simp [lps0])
      (by intro i hi
          have hi0 : i = 0 := by lia
          subst hi0
          exact ⟨0, by simp [lps0], ⟨by lia, nofun⟩, fun l hl => by have := hl.1; lia⟩)
      ⟨⟨by lia, nofun⟩, fun m hm _ hm' => by grind⟩
    refine ⟨by simpa [buildLPS, lps0] using hlen, fun i hi => ?_⟩
    obtain ⟨_, hlps, hlong⟩ := hentries i hi
    convert hlong using 1
    have hilen : i < ((buildLPSLoop _ 1 0 _ lps0).eval Comparison.natCost).length := hlen ▸ hi
    simp_all [buildLPS, lps0]

private def MatchAt (pat txt : List α) (start len : Nat) : Prop :=
  ∀ k, k < len → txt[start + k]? = pat[k]?

private lemma isPrefixOf_drop_eq_true_iff_matchAt [BEq α] [LawfulBEq α]
    (pat txt : List α) (start : Nat) :
    pat.isPrefixOf (txt.drop start) = true ↔ MatchAt pat txt start pat.length := by
  rw [← List.isSome_isPrefixOf?_eq_isPrefixOf]
  constructor
  · intro h
    obtain ⟨zs, hopt⟩ := Option.isSome_iff_exists.mp h
    intro k hk
    simpa [List.getElem?_drop, List.getElem?_eq_getElem hk] using
      List.prefix_iff_getElem?.1 ⟨zs, (List.isPrefixOf?_eq_some_iff_append_eq).1 hopt⟩ k hk
  · intro hmatch
    exact Option.isSome_iff_exists.mpr ⟨_, (List.isPrefixOf?_eq_some_iff_append_eq).2
      (List.prefix_iff_getElem?.2 fun k hk =>
        by simpa [List.getElem?_drop, List.getElem?_eq_getElem hk] using hmatch k hk).choose_spec⟩

private lemma matchAt_of_prefixSuffix
    (pat txt : List α) (start n l : Nat)
    (hmatch : MatchAt pat txt start n)
    (hps : PrefixSuffixOf pat n l) :
    MatchAt pat txt (start + (n - l)) l := by
  intro k hk
  calc txt[start + (n - l) + k]? = txt[start + (n - l + k)]? := by rw [Nat.add_assoc]
    _ = pat[n - l + k]? := by simpa using hmatch (n - l + k) (by have := hps.1; lia)
    _ = pat[k]? := (hps.2 k hk).symm

private lemma prefixSuffix_of_overlap
    (pat txt : List α) (s t n : Nat)
    (hnp : n ≤ pat.length)
    (hmatch : MatchAt pat txt s n)
    (hocc : MatchAt pat txt t pat.length)
    (hst : s < t)
    (ht : t ≤ s + n) :
    PrefixSuffixOf pat n (n - (t - s)) := by
  refine ⟨by lia, fun k hk => ?_⟩
  calc pat[k]? = txt[t + k]? := by simpa using (hocc k (by lia)).symm
    _ = txt[s + (t - s + k)]? := by lia
    _ = pat[t - s + k]? := by simpa using hmatch (t - s + k) (by lia)
    _ = pat[n - (n - (t - s)) + k]? := by lia

private lemma no_occurrence_between_full_match_and_fallback [BEq α] [LawfulBEq α]
    (pat txt : List α) (s l : Nat)
    (hfull : MatchAt pat txt s pat.length)
    (hlong : LongestPrefixSuffixOf pat pat.length l) :
    ∀ t, s < t → t < s + (pat.length - l) → pat.isPrefixOf (txt.drop t) = false := by
  intro t hst htl
  exact Bool.eq_false_iff.mpr fun ht =>
    absurd (hlong.2 _ (prefixSuffix_of_overlap pat txt s t _ le_rfl hfull
      ((isPrefixOf_drop_eq_true_iff_matchAt pat txt t).1 ht) hst (by lia))) (by lia)

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
      (Nat.le_of_lt hj) hmatch hocc hst' (by lia))) (by lia)

private lemma acc_shift_no_matches
    (P : Nat → Bool) (acc : List Nat) (s u : Nat)
    (hacc : acc.reverse = (List.Ico 0 s).filter P)
    (hsu : s ≤ u)
    (hfalse : ∀ t, s ≤ t → t < u → P t = false) :
    acc.reverse = (List.Ico 0 u).filter P := by
  simp_all [← List.Ico.append_consecutive (Nat.zero_le s) hsu]

private lemma kmpSearchLoop_exhausted [BEq α] [LawfulBEq α]
    (j : Nat) (pat txt : List α) (acc : List Nat)
    (hj : j < pat.length)
    (hacc : acc.reverse = (List.Ico 0 (txt.length - j)).filter fun s =>
      pat.isPrefixOf (txt.drop s)) :
    acc.reverse = (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) :=
  acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
    acc (txt.length - j) txt.length hacc (by lia)
    (fun t ht1 ht2 => by grind)

private abbrev KmpSearchLoopIH [BEq α] [LawfulBEq α]
    (fuel : Nat) (pat txt : List α) (lps : List Nat) :=
  ∀ i j acc,
    2 * (txt.length - i) + j ≤ fuel →
    i ≤ txt.length →
    j < pat.length →
    j ≤ i →
    MatchAt pat txt (i - j) j →
    acc.reverse = ((List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) →
    (kmpSearchLoop fuel i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s)

private lemma kmpSearchLoop_correct_match_full [BEq α] [LawfulBEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat)
    (hpot : 2 * (txt.length - i) + j ≤ fuel + 1)
    (hit : i < txt.length)
    (hlen : lps.length = pat.length)
    (hlps :
      ∀ k (hk : k < pat.length),
        LongestPrefixSuffixOf pat (k + 1) (lps[k]'(by simpa [hlen] using hk)))
    (ih : KmpSearchLoopIH fuel pat txt lps)
    (hj : j < pat.length)
    (hcmp : txt[i]'hit = pat[j]'hj)
    (hfull : j + 1 = pat.length)
    (hji : j ≤ i)
    (hmatch : MatchAt pat txt (i - j) j)
    (hacc :
      acc.reverse = (List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) :
    (kmpSearchLoop (fuel + 1) i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) := by
  have hlast : txt[(i - j) + j]? = pat[j]? := by simp_all
  have hmatch' : MatchAt pat txt (i - j) (j + 1) := by
    intro k hk
    obtain hk' | rfl := lt_or_eq_of_le (Nat.le_of_lt_succ hk)
    · exact hmatch k hk'
    · exact hlast
  let l := lps[j]'(by simpa [hlen] using hj)
  have hlong : LongestPrefixSuffixOf pat pat.length l := by simpa [hfull] using hlps j hj
  have hfullMatch : MatchAt pat txt (i - j) pat.length := by simpa [hfull] using hmatch'
  have hlj : l ≤ j := by grind [hlong.1.1]
  have hstart : (i + 1) - (j + 1) = i - j := by lia
  have hshift : (i - j) + (pat.length - l) = (i + 1) - l := by lia
  have hsu : i - j < (i + 1) - l := by lia
  have htrue : pat.isPrefixOf (txt.drop (i - j)) = true :=
    (isPrefixOf_drop_eq_true_iff_matchAt pat txt (i - j)).2 hfullMatch
  have hfalse : ∀ t, i - j < t → t < (i + 1) - l → pat.isPrefixOf (txt.drop t) = false := by
    intro t ht1 ht2
    exact no_occurrence_between_full_match_and_fallback pat txt (i - j)
      l hfullMatch hlong t ht1 (by simpa [hshift] using ht2)
  have hacc' : (((i + 1) - (j + 1)) :: acc).reverse =
        (List.Ico 0 ((i + 1) - l)).filter fun s => pat.isPrefixOf (txt.drop s) := by
    simp_all [← List.Ico.append_consecutive (Nat.zero_le (i - j)) (Nat.le_of_lt hsu),
      List.Ico.eq_cons hsu, Nat.add_comm]
  have hrec := ih (i + 1) l (((i + 1) - (j + 1)) :: acc)
    (by lia) (by lia) hlong.1.1 (by lia)
    (by simpa [hshift] using
      matchAt_of_prefixSuffix pat txt (i - j) pat.length l hfullMatch hlong.1)
    hacc'
  have hjEq : j = pat.length - 1 := by lia
  have hfull' : pat.length - 1 + 1 = pat.length := by lia
  have hcmp' : (txt[i]'hit == pat[pat.length - 1]'(by lia)) = true := by simp [hjEq, hcmp]
  have hpat' : pat[pat.length - 1]? = some (pat[pat.length - 1]'(by lia)) :=
    getElem?_pos pat (pat.length - 1) (by lia)
  have hlpsj : lps[j]? = some l := getElem?_pos lps j (by simpa [hlen] using hj)
  have hlpsj' : lps[pat.length - 1]? = some l := by simpa [hjEq] using hlpsj
  simpa [kmpSearchLoop, hit, hjEq, hfull', hcmp', hpat', hlpsj'] using hrec

private lemma kmpSearchLoop_correct_match_partial [BEq α] [LawfulBEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat)
    (hpot : 2 * (txt.length - i) + j ≤ fuel + 1)
    (hit : i < txt.length)
    (ih : KmpSearchLoopIH fuel pat txt lps)
    (hj : j < pat.length)
    (hcmp : txt[i]'hit = pat[j]'hj)
    (hfull : j + 1 ≠ pat.length)
    (hji : j ≤ i)
    (hmatch : MatchAt pat txt (i - j) j)
    (hacc :
      acc.reverse = (List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) :
    (kmpSearchLoop (fuel + 1) i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) := by
  have hlast : txt[(i - j) + j]? = pat[j]? := by simp_all
  have hmatch' : MatchAt pat txt (i - j) (j + 1) := by
    intro k hk
    obtain hk' | rfl := lt_or_eq_of_le (Nat.le_of_lt_succ hk)
    · exact hmatch k hk'
    · exact hlast
  have hrec := ih (i + 1) (j + 1) acc
    (by lia) (by lia) (by lia) (by lia)
    (by simpa using hmatch') (by simpa using hacc)
  simpa [kmpSearchLoop, hit, getElem?_pos txt i hit, getElem?_pos pat j hj, hcmp, hfull]
    using hrec

private lemma kmpSearchLoop_correct_mismatch_zero [BEq α] [LawfulBEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat)
    (hpot : 2 * (txt.length - i) + j ≤ fuel + 1)
    (hit : i < txt.length)
    (ih : KmpSearchLoopIH fuel pat txt lps)
    (hj : j < pat.length)
    (hcmp : txt[i]'hit ≠ pat[j]'hj)
    (hzero : j = 0)
    (hacc :
      acc.reverse = (List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) :
    (kmpSearchLoop (fuel + 1) i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) := by
  have hmis : pat[j]? ≠ txt[i]? := by aesop
  subst hzero
  have hiFalse : pat.isPrefixOf (txt.drop i) = false := Bool.eq_false_iff.mpr fun h =>
      hmis ((isPrefixOf_drop_eq_true_iff_matchAt pat txt i).1 h 0 (by lia)).symm
  have hacc' : acc.reverse = (List.Ico 0 (i + 1)).filter fun s => pat.isPrefixOf (txt.drop s) :=
    acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
      acc i (i + 1) hacc (by lia)
      (fun t _ _ => by grind)
  have hrec := ih (i + 1) 0 acc (by lia) (by lia) (by simpa using hj) (by lia) nofun hacc'
  simpa [kmpSearchLoop, hit, getElem?_pos txt i hit,
    getElem?_pos pat 0 (by lia : 0 < pat.length), hcmp] using hrec

private lemma kmpSearchLoop_correct_mismatch_fallback [BEq α] [LawfulBEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat)
    (hpot : 2 * (txt.length - i) + j ≤ fuel + 1)
    (hi : i ≤ txt.length)
    (hit : i < txt.length)
    (hlen : lps.length = pat.length)
    (hlps :
      ∀ k (hk : k < pat.length),
        LongestPrefixSuffixOf pat (k + 1) (lps[k]'(by simpa [hlen] using hk)))
    (ih : KmpSearchLoopIH fuel pat txt lps)
    (hj : j < pat.length)
    (hcmp : txt[i]'hit ≠ pat[j]'hj)
    (hzero : j ≠ 0)
    (hji : j ≤ i)
    (hmatch : MatchAt pat txt (i - j) j)
    (hacc :
      acc.reverse = (List.Ico 0 (i - j)).filter fun s => pat.isPrefixOf (txt.drop s)) :
    (kmpSearchLoop (fuel + 1) i j pat txt lps acc).eval Comparison.natCost =
      (List.Ico 0 txt.length).filter fun s => pat.isPrefixOf (txt.drop s) := by
  have hmis : pat[j]? ≠ txt[i]? := by aesop
  have hj1 : j - 1 < pat.length := by lia
  let l := lps[j - 1]'(by simpa [hlen] using hj1)
  have hlong : LongestPrefixSuffixOf pat j l := by
    simpa [Nat.sub_add_cancel (by lia : 1 ≤ j)] using hlps (j - 1) hj1
  have hmis' : pat[j]? ≠ txt[(i - j) + j]? := by grind
  have hacc' : acc.reverse = (List.Ico 0 (i - l)).filter fun s => pat.isPrefixOf (txt.drop s) :=
    acc_shift_no_matches (P := fun s => pat.isPrefixOf (txt.drop s))
      acc (i - j) (i - l) hacc
      (Nat.sub_le_sub_left (Nat.le_of_lt hlong.1.1) i)
      (fun t ht1 ht2 =>
        no_occurrence_between_partial_and_fallback pat txt (i - j) j l
          hj hmatch hlong hmis' t ht1 (by lia))
  have hrec := ih i l acc (by grind [hlong.1.1]) hi
    (lt_trans hlong.1.1 hj) (Nat.le_trans (Nat.le_of_lt hlong.1.1) hji)
    (by grind [matchAt_of_prefixSuffix pat txt (i - j) j l hmatch hlong.1, hlong.1.1])
    hacc'
  simp_all [kmpSearchLoop, l]

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
      obtain rfl : i = txt.length := by lia
      simpa [kmpSearchLoop] using kmpSearchLoop_exhausted j pat txt acc hj hacc
  | succ fuel ih =>
      by_cases hit : i < txt.length
      · by_cases hcmp : txt[i]'hit = pat[j]'hj
        · by_cases hfull : j + 1 = pat.length
          · exact kmpSearchLoop_correct_match_full _ _ _ _ _ _ _ hpot hit hlen hlps
              ih hj hcmp hfull hji hmatch hacc
          · exact kmpSearchLoop_correct_match_partial _ _ _ _ _ _ _ hpot hit ih hj hcmp
              hfull hji hmatch hacc
        · by_cases hzero : j = 0
          · exact kmpSearchLoop_correct_mismatch_zero _ _ _ _ _ _ _ hpot hit ih hj hcmp hzero hacc
          · exact kmpSearchLoop_correct_mismatch_fallback _ _ _ _ _ _ _ hpot hi hit
              hlen hlps ih hj hcmp hzero hji hmatch hacc
      · obtain rfl : i = txt.length := by lia
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
        (by lia) (by lia) hlen hlps (by simp) (by lia) nofun (by simp)
      simpa [kmpSearchPositions, PatternSearchAll, List.Ico.zero_bot] using hrec

end Correctness

section TimeComplexity

private lemma buildLPSLoop_time_le_bound [BEq α]
    (fuel pos len : Nat) (pat : List α) (lps : List Nat)
    (hlength : lps.length = pat.length)
    (hpos : pos ≤ pat.length)
    (hlen : len < pos)
    (hlps : ∀ i, i < pos → (lps[i]?).getD 0 < i + 1) :
    (buildLPSLoop fuel pos len pat lps).time Comparison.natCost ≤
      if pos < pat.length then 2 * (pat.length - pos) + len - 1 else 0 := by
  induction fuel generalizing pos len lps with
  | zero =>
      simp [buildLPSLoop]
  | succ fuel ih =>
      by_cases hlt : pos < pat.length
      · have hlenPat : len < pat.length := lt_of_lt_of_le hlen hpos
        rw [buildLPSLoop, if_pos hlt, getElem?_pos pat pos hlt, getElem?_pos pat len hlenPat]
        simp
        by_cases hcmp : (pat[pos]'hlt == pat[len]'hlenPat) = true
        · have hlps' : ∀ i, i < pos + 1 → ((lps.set pos (len + 1))[i]?).getD 0 < i + 1 := by grind
          grind
        · have hlps' : ∀ i, i < pos + 1 → ((lps.set pos 0)[i]?).getD 0 < i + 1 := by grind
          grind
      · simp [buildLPSLoop, hlt]

private lemma kmpSearchLoop_time_le_fuel [BEq α]
    (fuel i j : Nat) (pat txt : List α) (lps acc : List Nat) :
    (kmpSearchLoop fuel i j pat txt lps acc).time Comparison.natCost ≤ fuel := by
  induction fuel generalizing i j acc with
  | zero => simp [kmpSearchLoop]
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
                ).time Comparison.natCost ≤ fuel := by grind
            simpa [kmpSearchLoop, hi, getElem?_pos txt i hi, hpat, Prog.time_liftBind, Nat.add_comm]
              using Nat.add_le_add_left hbranch 1
      · simp [kmpSearchLoop, hi]

private lemma kmpSearchLoop_singleton_time [BEq α]
    (fuel i : Nat) (x : α) (txt : List α) (acc : List Nat)
    (hfuel : txt.length - i ≤ fuel) :
    (kmpSearchLoop fuel i 0 [x] txt [0] acc).time Comparison.natCost = txt.length - i := by
  induction fuel generalizing i acc <;>
    by_cases hi : i < txt.length <;>
      simp [kmpSearchLoop, hi] <;>
      grind

private lemma kmpSearchLoop_head_mismatch_replicate_time [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    ∀ fuel i (patTail : List α) (txtLen : Nat) (lps acc : List Nat),
      txtLen - i ≤ fuel →
      (kmpSearchLoop fuel i 0 (y :: patTail) (List.replicate txtLen x) lps acc).time
        Comparison.natCost = txtLen - i := by
  intro fuel i patTail txtLen lps acc hfuel
  induction fuel generalizing i patTail txtLen lps acc with
  | zero =>
      have hi : txtLen ≤ i := by lia
      simp [kmpSearchLoop, hi]
  | succ fuel ih =>
      by_cases hi : i < txtLen
      · have hrec := ih (i + 1) patTail txtLen lps acc (by lia)
        have hstep :
            (kmpSearchLoop (fuel + 1) i 0 (y :: patTail) (List.replicate txtLen x) lps acc).time
              Comparison.natCost = 1 + (txtLen - (i + 1)) := by
          simp [kmpSearchLoop, hi, hxy, hrec]
        rw [hstep]
        lia
      · have hi' : txtLen ≤ i := by lia
        simp [kmpSearchLoop, hi']

theorem buildLPS_time_complexity_upper_bound [BEq α] (pat : List α) :
    (buildLPS pat).time Comparison.natCost ≤ 2 * pat.length - 3 := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [buildLPS, buildLPSLoop]
      | cons y ys =>
          have hlps0 :
              ∀ i, i < 1 →
                ((List.replicate (x :: y :: ys).length 0)[i]?).getD 0 < i + 1 := by simp
          simpa [buildLPS] using
            buildLPSLoop_time_le_bound (fuel := 2 * ((x :: y :: ys).length - 1)) (pos := 1)
              (len := 0) (pat := x :: y :: ys)
              (lps := List.replicate (x :: y :: ys).length 0) (by simp) (by simp) (by simp) hlps0

private lemma buildLPSLoop_final_fallback_time [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    ∀ extra {r k}, k < r →
      (buildLPSLoop (extra + k + 1) r k
          (List.replicate r y ++ [x])
          (List.range r ++ [0])).time Comparison.natCost = k + 1 := by
  intro _ _ k hk
  induction k with
  | zero =>
      simp_all [buildLPSLoop, buildLPSLoop.eq_def]
  | succ k ih =>
      simp_all [lt_trans (Nat.lt_succ_self k) hk, List.getElem?_append_left,
        buildLPSLoop, Nat.add_left_comm, Nat.add_comm]

private lemma buildLPSLoop_replicate_append_singleton_time
    [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    ∀ extra k m,
      (buildLPSLoop (extra + k + 2 * m + 1) (k + 1) k
          (List.replicate (k + m + 1) y ++ [x])
          (List.range (k + 1) ++ List.replicate (m + 1) 0)).time Comparison.natCost
        = k + 2 * m + 1 := by
  intro extra k m
  induction m generalizing extra k with
  | zero =>
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        buildLPSLoop_final_fallback_time (x := x) (y := y) hxy extra (r := k + 1) (k := k)
          (by simp)
  | succ m ih =>
      have htail :
          (List.replicate (m + 2) 0).set 0 (k + 1) = (k + 1) :: List.replicate (m + 1) 0 := by
        simp [List.replicate]
      have hstate :
          List.range (k + 1) ++ (k + 1) :: List.replicate (m + 1) 0 =
            List.range (k + 2) ++ List.replicate (m + 1) 0 := by
        simp [List.range_succ, List.append_assoc]
      have hpatPos : (List.replicate (k + (m + 1) + 1) y ++ [x])[k + 1]? = some y := by
        grind
      have hpatLen : (List.replicate (k + (m + 1) + 1) y ++ [x])[k]? = some y := by
        grind
      rw [buildLPSLoop, if_pos (by simp), hpatPos, hpatLen]
      simpa [htail, hstate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, two_mul] using
        congrArg Nat.succ (ih extra (k + 1))

private lemma buildLPS_replicate_append_singleton_time [DecidableEq α] {x y : α} (hxy : x ≠ y) :
    ∀ n,
      (buildLPS (List.replicate n y ++ [x])).time Comparison.natCost = 2 * n - 1 := by
  intro n
  cases n with
  | zero =>
      simp [buildLPS, buildLPSLoop]
  | succ n =>
      simpa [buildLPS, List.range, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        buildLPSLoop_replicate_append_singleton_time (x := x) (y := y) hxy 1 0 n

theorem buildLPS_time_complexity_lower_bound [DecidableEq α] [Nontrivial α] (n : ℕ) :
    ∃ pat : List α, pat.length = n ∧
      (buildLPS pat).time Comparison.natCost = 2 * n - 3 := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  cases n with
  | zero =>
      simp [buildLPS]
  | succ n =>
      refine ⟨List.replicate n y ++ [x], by simp, ?_⟩
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        buildLPS_replicate_append_singleton_time (x := x) (y := y) hxy n

theorem kmpSearchPositions_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (kmpSearchPositions pat txt).time Comparison.natCost ≤
      2 * (txt.length + pat.length) - 3 := by
  cases pat with
  | nil =>
      simp [kmpSearchPositions]
  | cons x xs =>
      cases xs with
      | nil =>
          have hsingle :
              (kmpSearchLoop (2 * txt.length) 0 0 [x] txt [0] []).time Comparison.natCost ≤
                txt.length := by
            simpa using le_of_eq <|
              kmpSearchLoop_singleton_time (fuel := 2 * txt.length) (i := 0) x txt [] (by lia)
          simp [kmpSearchPositions, buildLPS, buildLPSLoop, Cslib.FreeM.bind_eq_bind]
          grind
      | cons y ys =>
          simp only [kmpSearchPositions, Cslib.FreeM.bind_eq_bind, time_bind, List.length_cons]
          have := by simpa using buildLPS_time_complexity_upper_bound (x :: y :: ys)
          have := by simpa using (kmpSearchLoop_time_le_fuel (2 * txt.length) 0 0 (x :: y :: ys)
                txt ((buildLPS (x :: y :: ys)).eval Comparison.natCost) [])
          lia

theorem kmpSearchPositions_time_complexity_lower_bound [DecidableEq α] [Nontrivial α]
    (m n : ℕ) :
    ∃ (pat : List α) (txt : List α), pat.length = m + 1 ∧ txt.length = n ∧
      (kmpSearchPositions pat txt).time Comparison.natCost = txt.length + (2 * pat.length - 3) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  cases m with
  | zero =>
      refine ⟨[x], List.replicate n y, by simp, by simp, ?_⟩
      have hsearch :
          (kmpSearchLoop (2 * n) 0 0 [x] (List.replicate n y) [0] []).time
          Comparison.natCost = n := by
        simpa using
          kmpSearchLoop_head_mismatch_replicate_time (x := y) (y := x) hxy.symm
            (fuel := 2 * n) (i := 0) (patTail := []) (txtLen := n) (lps := [0]) (acc := []) (by lia)
      simp [kmpSearchPositions, buildLPS, buildLPSLoop, Cslib.FreeM.bind_eq_bind, hsearch]
  | succ m =>
      refine ⟨List.replicate (m + 1) y ++ [x], List.replicate n x, by simp, by simp, ?_⟩
      have hbuild :
          (buildLPS (List.replicate (m + 1) y ++ [x])).time Comparison.natCost =
          2 * (m + 1) - 1 := by
        simpa using buildLPS_replicate_append_singleton_time (x := x) (y := y) hxy (m + 1)
      have hsearch :=
        kmpSearchLoop_head_mismatch_replicate_time (x := x) (y := y) hxy
          (fuel := 2 * n) (i := 0) (patTail := List.replicate m y ++ [x]) (txtLen := n)
          (lps := (buildLPS (List.replicate (m + 1) y ++ [x])).eval Comparison.natCost)
          (acc := []) (by lia)
      simp [kmpSearchPositions, Cslib.FreeM.bind_eq_bind, time_bind]
      grind

end TimeComplexity

end Algorithms

end Algolean
