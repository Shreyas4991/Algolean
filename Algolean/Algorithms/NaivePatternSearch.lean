/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.Models.Comparison
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Range

@[expose] public section

/-!
# Naive pattern search

In this file we define naive pattern search on lists. We further prove the correctness as well as an
upper bound for comparisons in the `Comparison` query model.
--

## Main definitions

- `prefixMatch`: checks whether a pattern is a prefix of some text.
- `naivePatternSearch`: returns all start indices of contiguous matches.
- `PatternSearchAll`: Pattern searching definition for finding all matches.

## Main results

- `prefixMatch_eval`: `prefixMatch` evaluates identically to `List.isPrefixOf`.
- `naivePatternSearch_eval`: `naivePatternSearch` evaluates identically to `PatternSearchAll`.
- `prefixMatch_time_complexity_upper_bound`: `prefixMatch` takes at most
  `min pat.length txt.length` comparisons.
- `prefixMatch_time_complexity_lower_bound`: for any pattern and text lengths, there are inputs
  on which `prefixMatch` takes exactly `min pat.length txt.length` comparisons.
- `naivePatternSearch_time_complexity_upper_bound`: `naivePatternSearch` takes at most
  `pat.length * (txt.length + 1 - pat.length)` comparisons.
- `naivePatternSearch_time_complexity_lower_bound`: for any pattern and text lengths, there are
  inputs on which `naivePatternSearch` takes exactly
  `pat.length * (txt.length + 1 - pat.length)` comparisons.
-/

namespace Algolean

namespace Algorithms

open Prog

/--
`PatternSearchAll pat txt` returns all starting positions in `txt` such that
`pat` is a prefix of `txt` starting there, in increasing order.

For the empty pattern, this returns every position inside the text
`0, 1, ..., txt.length - 1`.
-/
def PatternSearchAll [BEq α] (pat txt : List α) : List Nat :=
  (List.range txt.length).filter fun i => pat.isPrefixOf (txt.drop i)

open Comparison in
/--
`prefixMatch pat txt` returns true iff `pat` is a prefix of `txt`.
-/
def prefixMatch (pat txt : List α) : Prog (Comparison α) Bool := do
  match pat, txt with
  | [], _ =>
    return true
  | _ :: _, [] =>
    return false
  | p :: ps, t :: ts =>
    let cmp : Bool ← compare p t
    if cmp then
      prefixMatch ps ts
    else
      return false

open Comparison in
/--
`naivePatternSearchFrom pat txt i` returns all indices `j >= i` such that `pat`
is a prefix of the suffix of the original text starting at `j`.

The indices are returned in increasing order.
-/
def naivePatternSearchFrom (pat txt : List α) (i : Nat) : Prog (Comparison α) (List Nat) := do
  match pat with
  | [] =>
      match txt with
      | [] =>
          return []
      | _ :: ts =>
          let rest ← naivePatternSearchFrom pat ts (i + 1)
          return i :: rest
  | _ :: _ =>
      if pat.length ≤ txt.length then
        match txt with
        | [] =>
            return []
        | _ :: ts =>
            let found ← prefixMatch pat txt
            let rest ← naivePatternSearchFrom pat ts (i + 1)
            if found then
              return i :: rest
            else
              return rest
      else
        return []

open Comparison in
/--
`naivePatternSearch pat txt` returns the 0-based start indices of all contiguous matches of
`pat` in `txt`.
-/
def naivePatternSearch (pat txt : List α) : Prog (Comparison α) (List Nat) :=
  naivePatternSearchFrom pat txt 0

section Correctness

theorem prefixMatch_eval [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).eval Comparison.natCost = pat.isPrefixOf txt := by
  induction pat generalizing txt with
  | nil => simp [prefixMatch]
  | cons p ps ih =>
      cases txt <;>
      simp [prefixMatch]
      grind

private lemma isPrefixOf_eq_false_of_length_lt [BEq α] :
    ∀ {pat txt : List α}, txt.length < pat.length → pat.isPrefixOf txt = false
  | [], _, _
  | _ :: _, [], _
  | _ :: ps, _ :: ts, h => by
      simp_all [List.isPrefixOf, isPrefixOf_eq_false_of_length_lt]

private lemma patternSearchAll_cons [BEq α] (pat : List α) (t : α) (ts : List α) :
    PatternSearchAll pat (t :: ts) =
      if pat.isPrefixOf (t :: ts) then
        0 :: (PatternSearchAll pat ts).map Nat.succ
      else
        (PatternSearchAll pat ts).map Nat.succ := by
  simp only [PatternSearchAll, List.length_cons, List.range_succ_eq_map, List.filter_cons]
  have : List.filter (fun i => pat.isPrefixOf (List.drop i (t :: ts)))
        (List.map Nat.succ (List.range ts.length)) = List.map Nat.succ
        (List.filter (fun i => pat.isPrefixOf (List.drop i ts)) (List.range ts.length)) := by
    induction List.range ts.length <;> grind
  grind

private lemma patternSearchAll_eq_nil_of_length_lt [BEq α] :
    ∀ {pat txt : List α}, txt.length < pat.length → PatternSearchAll pat txt = []
  | [], _, h
  | _ :: _, [], _ => by simp_all [PatternSearchAll]
  | p :: ps, t :: ts, h => by simp [patternSearchAll_cons, isPrefixOf_eq_false_of_length_lt h,
      patternSearchAll_eq_nil_of_length_lt (lt_trans (Nat.lt_succ_self _) h)]

theorem naivePatternSearch_eval [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).eval Comparison.natCost = PatternSearchAll pat txt := by
  have hfrom : ∀ i, (naivePatternSearchFrom pat txt i).eval Comparison.natCost =
      (PatternSearchAll pat txt).map (fun j => i + j) := by
    intro i
    induction txt generalizing i with
    | nil =>
        cases pat <;> simp [naivePatternSearchFrom, PatternSearchAll]
    | cons t ts ih =>
        cases pat with
        | nil =>
            simp [naivePatternSearchFrom, patternSearchAll_cons,
              ih, Nat.add_left_comm, Nat.add_comm]
        | cons p ps =>
            by_cases hlen : (p :: ps).length ≤ (t :: ts).length
            · have hlen' : ps.length ≤ ts.length := by simpa using hlen
              by_cases h : (p :: ps).isPrefixOf (t :: ts) = true <;>
                simp [naivePatternSearchFrom, prefixMatch_eval, patternSearchAll_cons,
                  ih, hlen', h, Nat.add_left_comm, Nat.add_comm]
            · have hlen' : ¬ ps.length ≤ ts.length := by simpa using hlen
              simp [naivePatternSearchFrom, hlen',
                patternSearchAll_eq_nil_of_length_lt (Nat.not_le.mp hlen)]
  simpa [naivePatternSearch] using hfrom 0

end Correctness

section TimeComplexity

theorem prefixMatch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).time Comparison.natCost ≤ Nat.min pat.length txt.length := by
  induction txt generalizing pat <;>
    cases pat <;>
      simp_all [prefixMatch];
      grind

theorem prefixMatch_time_complexity_lower_bound [BEq α] [LawfulBEq α] [Nonempty α]
    (m n : ℕ) : ∃ pat txt : List α, pat.length = m ∧ txt.length = n ∧
    (prefixMatch pat txt).time Comparison.natCost = Nat.min pat.length txt.length := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have hrep : (prefixMatch (List.replicate m x) (List.replicate n x)).time Comparison.natCost =
      Nat.min m n := by
    induction n generalizing m <;>
      cases m <;>
        simp_all [List.replicate, prefixMatch, Nat.add_comm]
  use List.replicate m x, List.replicate n x
  split_ands <;>
    simp_all

theorem naivePatternSearch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).time Comparison.natCost ≤
      pat.length * (txt.length + 1 - pat.length) := by
  have hfrom : ∀ i, (naivePatternSearchFrom pat txt i).time Comparison.natCost ≤
      pat.length * (txt.length + 1 - pat.length) := by
    intro i
    induction txt generalizing i with
    | nil =>
        cases pat <;> simp [naivePatternSearchFrom]
    | cons t ts ih =>
        cases pat with
        | nil =>
            simpa [naivePatternSearchFrom, Prog.time_bind] using ih (i + 1)
        | cons p ps =>
            by_cases hlen : (p :: ps).length ≤ (t :: ts).length
            · have hlen' : ps.length ≤ ts.length := by simpa using hlen
              have htime : (naivePatternSearchFrom (p :: ps) (t :: ts) i).time Comparison.natCost =
                  (prefixMatch (p :: ps) (t :: ts)).time Comparison.natCost +
                  (naivePatternSearchFrom (p :: ps) ts (i + 1)).time Comparison.natCost := by
                simp [naivePatternSearchFrom, Prog.time_bind, hlen']
                split_ifs <;> simp
              have hsucc : (t :: ts).length + 1 - (p :: ps).length =
                  (ts.length + 1 - (p :: ps).length) + 1 := by
                simpa using Nat.succ_sub hlen
              rw [htime]
              convert Nat.add_le_add
                  ((prefixMatch_time_complexity_upper_bound (p :: ps) (t :: ts)).trans
                  (Nat.min_le_left _ _)) (ih (i + 1)) using 1
              rw [hsucc, Nat.mul_succ, Nat.add_comm]
            · have hlen' : ¬ ps.length ≤ ts.length := by
                simpa using hlen
              simp [naivePatternSearchFrom, hlen']
  simpa [naivePatternSearch] using hfrom 0

theorem naivePatternSearch_time_complexity_lower_bound [BEq α] [LawfulBEq α] [Nonempty α]
    (m n : ℕ) : ∃ pat txt : List α, pat.length = m ∧ txt.length = n ∧
    (naivePatternSearch pat txt).time Comparison.natCost =
    pat.length * (txt.length + 1 - pat.length) := by
  obtain ⟨x⟩ := ‹Nonempty α›
  have hprefix :
      ∀ m n,
        let pat := List.replicate m x
        let txt := List.replicate n x
        (prefixMatch pat txt).time Comparison.natCost = Nat.min m n := by
    intro m n
    simp only
    induction n generalizing m <;>
      cases m <;>
        simp_all [List.replicate, prefixMatch, Nat.add_comm]
  have hfrom :
      ∀ i m n,
        let pat := List.replicate m x
        let txt := List.replicate n x
        (naivePatternSearchFrom pat txt i).time Comparison.natCost = m * (n + 1 - m) := by
    intro i m n
    simp only
    induction n generalizing i m with
    | zero =>
        cases m <;>
          simp [naivePatternSearchFrom, List.replicate]
    | succ n ih =>
        cases m with
        | zero =>
            simpa [naivePatternSearchFrom, List.replicate, Prog.time_bind] using ih (i + 1) 0
        | succ m =>
            by_cases hlen : m ≤ n
            · have hlen' : (m + 1) ≤ (n + 1) := by simpa using Nat.succ_le_succ hlen
              let pat' := List.replicate (m + 1) x
              let txt'' := List.replicate n x
              let txt' := x :: txt''
              have htime :
                  (naivePatternSearchFrom pat' txt' i).time Comparison.natCost =
                  (prefixMatch pat' txt').time Comparison.natCost +
                  (naivePatternSearchFrom pat' txt'' (i + 1)).time Comparison.natCost := by
                simp [pat', txt', txt'', naivePatternSearchFrom, List.replicate, hlen]
                split_ifs <;> simp
              have hsucc : (n + 1) + 1 - (m + 1) = (n + 1 - (m + 1)) + 1 := by
                simpa using Nat.succ_sub hlen'
              have hprefix' :
                  (prefixMatch pat' txt').time Comparison.natCost = Nat.min (m + 1) (n + 1) := by
                simpa [pat', txt', txt''] using hprefix (m + 1) (n + 1)
              have hih' :
                  (naivePatternSearchFrom pat' txt'' (i + 1)).time Comparison.natCost =
                    (m + 1) * (n + 1 - (m + 1)) := by
                simpa [pat', txt''] using ih (i + 1) (m + 1)
              have htime' :
                  (naivePatternSearchFrom pat' txt' i).time Comparison.natCost =
                    (prefixMatch pat' txt').time Comparison.natCost +
                    (naivePatternSearchFrom pat' txt'' (i + 1)).time Comparison.natCost := by
                simpa using htime
              simp_all [pat', txt', txt'', List.replicate, Nat.mul_succ, Nat.add_comm]
            · simp [naivePatternSearchFrom, List.replicate, hlen,
                Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt (Nat.not_le.mp hlen))]
  let pat := List.replicate m x
  let txt := List.replicate n x
  use pat, txt
  split_ands <;>
    simp_all [pat, txt, naivePatternSearch]

end TimeComplexity

end Algorithms

end Algolean
