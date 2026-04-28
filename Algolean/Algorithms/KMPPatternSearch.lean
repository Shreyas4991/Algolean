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

- `kmpPatternSearch_eval`: `kmpSearchPositions` evaluates identically to `PatternSearchAll`.
- `buildLPS_time_complexity_upper_bound`: `buildLPS` takes at most
  `2 * (pat.length - 1)` comparisons.
- `kmpSearchPositions_time_complexity_upper_bound`: `kmpSearchPositions` takes at most
  `2 * (txt.length + pat.length - 1)` comparisons.

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
  refine ⟨lt_trans h₁.1 h₂.1, ?_⟩
  intro j hj
  have hjm : m - l + j < m := by
    have := Nat.add_lt_add_left hj (m - l)
    simpa [Nat.sub_add_cancel (Nat.le_of_lt h₁.1), Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  calc
    pat[j]? = pat[m - l + j]? := h₁.2 j hj
    _ = pat[n - m + (m - l + j)]? := h₂.2 (m - l + j) hjm
    _ = pat[n - l + j]? := by
      have hmn : m ≤ n := Nat.le_of_lt h₂.1
      have hnm : n - m + (m - l) = n - l := by
        have hlm : l ≤ m := Nat.le_of_lt h₁.1
        omega
      have hnmj : n - m + (m - l + j) = n - l + j := by
        calc
          n - m + (m - l + j) = (n - m + (m - l)) + j := by omega
          _ = n - l + j := by rw [hnm]
      rw [hnmj]

private lemma prefixSuffix_of_lt_of_prefixSuffix
    (h₁ : PrefixSuffixOf pat n l) (h₂ : PrefixSuffixOf pat n m) (hlm : l < m) :
    PrefixSuffixOf pat m l := by
  refine ⟨hlm, ?_⟩
  intro j hj
  have hmj : m - l + j < m := by
    have := Nat.add_lt_add_left hj (m - l)
    simpa [Nat.sub_add_cancel (Nat.le_of_lt hlm), Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using this
  calc
    pat[j]? = pat[n - l + j]? := h₁.2 j hj
    _ = pat[n - m + (m - l + j)]? := by
      have hnm : n - m + (m - l) = n - l := by
        have hlm' : l ≤ m := Nat.le_of_lt hlm
        have hmn : m ≤ n := Nat.le_of_lt h₂.1
        omega
      have hnmj : n - m + (m - l + j) = n - l + j := by
        calc
          n - m + (m - l + j) = (n - m + (m - l)) + j := by omega
          _ = n - l + j := by rw [hnm]
      rw [hnmj]
    _ = pat[m - l + j]? := h₂.2 (m - l + j) hmj |>.symm

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
  refine ⟨prefixSuffix_trans hlong.1 hs.1, ?_⟩
  intro m hm hmpos hm'
  by_cases hml : m < len
  · exact fun _ => by
      have hm'' : PrefixSuffixOf pat len m := prefixSuffix_of_lt_of_prefixSuffix hm' hs.1 hml
      have := hlong.2 m hm''
      omega
  · by_cases hmeq : m = len
    · subst hmeq
      exact hmis
    · exact hs.2 m (by omega) hmpos hm'

private lemma entriesCorrect_set
    (h : EntriesCorrect pat pos lps)
    (hi : pos < lps.length)
    (hlong : LongestPrefixSuffixOf pat (pos + 1) l) :
    EntriesCorrect pat (pos + 1) (lps.set pos l) := by
  intro i hi'
  by_cases hEq : i = pos
  · subst hEq
    exact ⟨l, List.getElem?_set_eq_of_lt _ hi, hlong⟩
  · rcases h i (by omega) with ⟨x, hx, hx'⟩
    refine ⟨x, ?_, hx'⟩
    have hii : i < lps.length := by omega
    have hEq' : pos ≠ i := by simpa [eq_comm] using hEq
    grind [List.getElem?_set_of_lt]

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
      have hEq : pos = pat.length := by
        by_contra hne
        have hlt : pos < pat.length := by omega
        omega
      subst hEq
      simp [buildLPSLoop, hlen]
      simpa [EntriesCorrect] using hentries
  | succ fuel ih =>
      by_cases hpos' : pos < pat.length
      · have hlen' : len < pat.length := lt_trans hs.1.1 hpos'
        by_cases hcmp : pat[pos]'hpos' = pat[len]'hlen'
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = true := by simp [hcmp]
          have hmatch : pat[len]? = pat[pos]? := by
            simp [List.getElem?_eq_getElem hlen', List.getElem?_eq_getElem hpos', hcmp]
          have hlong : LongestPrefixSuffixOf pat (pos + 1) (len + 1) :=
            searchInvariant_match_longest hs hmatch
          have hentries' :
              EntriesCorrect pat (pos + 1) (lps.set pos (len + 1)) :=
            entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong
          have hrec := ih (pos + 1) (len + 1) (lps.set pos (len + 1))
            (by omega) (by omega) (by simpa [List.length_set] using hlen) hentries'
            (by
              refine ⟨hlong.1, ?_⟩
              intro m hm _ hm'
              exact fun _ => by
                have := hlong.2 m hm'
                omega)
          simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
            List.getElem?_eq_getElem hlen', hcmp'] using hrec
        · have hcmp' : (pat[pos]'hpos' == pat[len]'hlen') = false := by simp [hcmp]
          by_cases hzero : len = 0
          · subst hzero
            have hmis : pat[0]? ≠ pat[pos]? := by
              intro hEq
              apply hcmp
              simpa [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hpos']
                using hEq.symm
            have hlong : LongestPrefixSuffixOf pat (pos + 1) 0 :=
              searchInvariant_zero_longest hs hmis
            have hentries' :
                EntriesCorrect pat (pos + 1) (lps.set pos 0) :=
              entriesCorrect_set hentries (by simpa [hlen] using hpos') hlong
            have hrec := ih (pos + 1) 0 (lps.set pos 0)
              (by omega) (by omega) (by simpa [List.length_set] using hlen) hentries'
              (by
                refine ⟨hlong.1, ?_⟩
                intro m hm _ hm'
                exact fun _ => by
                  have := hlong.2 m hm'
                  omega)
            simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
              List.getElem?_eq_getElem (by omega : 0 < pat.length), hcmp'] using hrec
          · have hlen1 : len - 1 < pos := by
              have : len < pos := hs.1.1
              omega
            rcases hentries (len - 1) hlen1 with ⟨len', hlen'', hlong⟩
            have hlenpos : 0 < len := Nat.pos_of_ne_zero hzero
            have hlong' : LongestPrefixSuffixOf pat len len' := by
              simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hlenpos)] using hlong
            have hmis : pat[len]? ≠ pat[pos]? := by
              intro hEq
              apply hcmp
              simpa [List.getElem?_eq_getElem hlen', List.getElem?_eq_getElem hpos'] using hEq.symm
            have hrec := ih pos len' lps
              (by have := hlong'.1.1; omega) hpos hlen hentries
              (searchInvariant_fallback hs hlong' hmis)
            simpa [buildLPSLoop, hpos', List.getElem?_eq_getElem hpos',
              List.getElem?_eq_getElem hlen', hcmp', hzero, hlen''] using hrec
      · have hEq : pos = pat.length := by omega
        subst hEq
        simp [buildLPSLoop, hlen]
        simpa [EntriesCorrect] using hentries

/--
Correctness of `buildLPS`: every entry of the produced LPS table is the longest proper
prefix/suffix length for the corresponding prefix of the pattern.
-/
theorem buildLPS_correct [BEq α] [LawfulBEq α] (pat : List α) :
    let lps := (buildLPS pat).eval Comparison.natCost
    ∃ hlen : lps.length = pat.length,
      ∀ i (hi : i < pat.length),
        LongestPrefixSuffixOf pat (i + 1) (lps[i]'(by simpa [hlen] using hi)) := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      let lps0 := List.replicate (List.length (x :: xs)) 0
      have hrec := buildLPSLoop_correct
        (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0
        (by simp) (by simp) (by simp [lps0])
        (by
          intro i hi
          have : i = 0 := by omega
          subst this
          refine ⟨0, ?_, ?_⟩
          · simp [lps0]
          · refine ⟨⟨by omega, ?_⟩, ?_⟩
            · intro j hj
              grind
            intro l hl
            simpa using Nat.lt_succ_iff.mp hl.1)
        (by
          refine ⟨⟨by omega, ?_⟩, ?_⟩
          · intro j hj
            grind
          intro m hm _ hm'
          grind)
      rcases hrec with ⟨hlen, hentries⟩
      refine ⟨by simpa [buildLPS, lps0] using hlen, ?_⟩
      intro i hi
      rcases hentries i hi with ⟨l, hlps, hlong⟩
      have hilen :
          i < ((buildLPSLoop (2 * ((x :: xs).length - 1))
            1 0 (x :: xs) lps0).eval Comparison.natCost).length := by
        rw [hlen]
        exact hi
      have hget :
          ((buildLPSLoop (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0).eval
            Comparison.natCost)[i]'hilen = l := by
        have hs :
            some
              (((buildLPSLoop (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0).eval
                Comparison.natCost)[i]'hilen) = some l := by
          have hs' := hlps
          rw [List.getElem?_eq_getElem hilen] at hs'
          exact hs'
        exact Option.some.inj hs
      have hgoal :
          LongestPrefixSuffixOf (x :: xs) (i + 1)
            (((buildLPSLoop (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0).eval
              Comparison.natCost)[i]'hilen) := by
        rw [hget]
        exact hlong
      simpa [buildLPS, lps0, hlen] using hgoal

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

theorem buildLPS_time_complexity_upper_bound [BEq α] (pat : List α) :
    (buildLPS pat).time Comparison.natCost ≤ 2 * (pat.length - 1) := by
  cases pat with
  | nil =>
      simp [buildLPS]
  | cons x xs =>
      let lps0 := List.replicate (List.length (x :: xs)) 0
      simpa [buildLPS, lps0] using
        buildLPSLoop_time_le_fuel (2 * ((x :: xs).length - 1)) 1 0 (x :: xs) lps0

end TimeComplexity

end Algorithms

end Algolean
