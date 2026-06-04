/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.Algorithms.NaivePatternSearch

/-!
# Examples for Naive Pattern Search

This file contains some examples of `naivePatternSearch`.
-/

@[expose] public section

namespace AlgoleanTests

open Algolean Algorithms

section NaivePatternSearchExamples

lemma empty_pattern_naive [BEq α] (txt : List α) :
    let pat := []
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = List.range txt.length := by
  simpa [PatternSearchAll] using (naivePatternSearch_eval ([] : List α) txt)

lemma empty_text_naive [BEq α] (pat : List α) :
    let txt := []
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [] := by
  simpa [PatternSearchAll] using (naivePatternSearch_eval pat ([] : List α))

lemma single_character_naive [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    let pat := [x]
    let txt := List.replicate n x
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = List.range n := by
  dsimp
  rw [naivePatternSearch_eval]
  have hdrop : ∀ a < n, 1 ≤ n - a := by
    intro a ha
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt ha)
  simpa [PatternSearchAll] using hdrop

lemma single_match_naive :
    let pat := [1, 0]
    let txt := [0, 1, 1, 2, 3, 0, 0, 1, 0]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [7] := by
  rfl

lemma double_match_naive :
    let pat := [1, 0]
    let txt := [0, 1, 0, 2, 3, 0, 0, 1, 0]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [1, 7] := by
  rfl

lemma overlapping_naive :
    let pat := [1, 1, 1]
    let txt := [1, 1, 1, 1, 1, 1, 1]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [0, 1, 2, 3, 4] := by
  rfl

lemma overlapping_naive2 :
    let pat := [1, 0, 1, 0]
    let txt := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [0, 2, 4, 6] := by
  rfl

lemma overlapping_naive3 :
    let pat := [1, 2, 3, 4, 7, 1, 2]
    let txt := [3, 6, 1, 2, 3, 4, 7, 1, 2, 3, 4, 7, 1, 2]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [2, 7] := by
  rfl

lemma overlapping_naive4 :
    let pat := [1, 0, 1]
    let txt := [3, 1, 0, 1, 0, 1, 0, 3, 4]
    let matchesFound := (naivePatternSearch pat txt).eval Comparison.natCost
    matchesFound = [1, 3] := by
  rfl

end NaivePatternSearchExamples

end AlgoleanTests
