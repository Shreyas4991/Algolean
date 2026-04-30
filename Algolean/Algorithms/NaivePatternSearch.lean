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
- `naivePatternSearch_time_complexity_upper_bound`: `naivePatternSearch` takes at most
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

TODO: move definition
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
  | _ :: _, [], _ => by simp_all
  | _ :: ps, _ :: ts, h => by
      simp_all [List.isPrefixOf, isPrefixOf_eq_false_of_length_lt (Nat.lt_of_succ_lt_succ h)]

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
  | [], _, h => by simp at h
  | _ :: _, [], _ => by simp [PatternSearchAll]
  | p :: ps, t :: ts, h => by simp [patternSearchAll_cons, isPrefixOf_eq_false_of_length_lt h,
      patternSearchAll_eq_nil_of_length_lt (lt_trans (Nat.lt_succ_self _) h)]

theorem naivePatternSearch_eval [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).eval Comparison.natCost = PatternSearchAll pat txt := by
  simpa [naivePatternSearch] using
    ((show ∀ i,
        (naivePatternSearchFrom pat txt i).eval Comparison.natCost =
          (PatternSearchAll pat txt).map (fun j => i + j) from by
      intro i
      cases pat with
      | nil =>
          induction txt generalizing i with
          | nil => simp [naivePatternSearchFrom, PatternSearchAll]
          | cons t ts ih =>
              simp [naivePatternSearchFrom, Prog.eval_bind, patternSearchAll_cons, ih,
                Nat.add_left_comm, Nat.add_comm]
      | cons p ps =>
          induction txt generalizing i with
          | nil => simp [naivePatternSearchFrom, PatternSearchAll]
          | cons t ts ih =>
              by_cases hlen : (p :: ps).length ≤ (t :: ts).length
              · by_cases h : (p :: ps).isPrefixOf (t :: ts) = true <;>
                  simp [naivePatternSearchFrom, prefixMatch_eval, patternSearchAll_cons,
                    ih, (show ps.length ≤ ts.length from by simpa using hlen),
                    h, Nat.add_left_comm, Nat.add_comm]
              · simp [naivePatternSearchFrom,
                (show ¬ ps.length ≤ ts.length from by simpa using hlen),
                  patternSearchAll_eq_nil_of_length_lt (Nat.not_le.mp hlen)]
    ) 0)

end Correctness

section TimeComplexity

theorem prefixMatch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (prefixMatch pat txt).time Comparison.natCost ≤ Nat.min pat.length txt.length := by
  induction pat generalizing txt with
  | nil => simp [prefixMatch]
  | cons p ps ih =>
    cases txt with
    | nil => simp [prefixMatch]
    | cons t ts =>
      by_cases h : p == t
      · have hih := ih ts; simp [prefixMatch, h] at hih ⊢; omega
      · simp [prefixMatch, h]

theorem naivePatternSearch_time_complexity_upper_bound [BEq α] (pat txt : List α) :
    (naivePatternSearch pat txt).time Comparison.natCost ≤
      pat.length * (txt.length + 1 - pat.length) := by
  simpa [naivePatternSearch] using
    ((show ∀ i,
        (naivePatternSearchFrom pat txt i).time Comparison.natCost ≤
          pat.length * (txt.length + 1 - pat.length) from by
      intro i
      cases pat with
      | nil =>
          induction txt generalizing i with
          | nil => simp [naivePatternSearchFrom]
          | cons t ts ih => simpa [naivePatternSearchFrom, Prog.time_bind] using ih (i + 1)
      | cons p ps =>
          induction txt generalizing i with
          | nil => simp [naivePatternSearchFrom]
          | cons t ts ih =>
              by_cases hlen : (p :: ps).length ≤ (t :: ts).length
              · rw [show (naivePatternSearchFrom (p :: ps) (t :: ts) i).time Comparison.natCost =
                    (prefixMatch (p :: ps) (t :: ts)).time Comparison.natCost +
                      (naivePatternSearchFrom (p :: ps) ts (i + 1)).time
                        Comparison.natCost from by
                      simp [naivePatternSearchFrom, Prog.time_bind,
                        (show ps.length ≤ ts.length from by simpa using hlen)]; split <;> simp]
                exact (Nat.add_le_add
                  ((prefixMatch_time_complexity_upper_bound _ _).trans (Nat.min_le_left _ _))
                  (ih (i + 1))).trans_eq (by
                    rw [show (t :: ts).length + 1 - (p :: ps).length =
                        (ts.length + 1 - (p :: ps).length) + 1 from by
                          simpa using Nat.succ_sub hlen,
                      Nat.mul_succ, Nat.add_comm])
              · simp [naivePatternSearchFrom,
                  (show ¬ ps.length ≤ ts.length from by simpa using hlen)]
    ) 0)

end TimeComplexity

end Algorithms

end Algolean
