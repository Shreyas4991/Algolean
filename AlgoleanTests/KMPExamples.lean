/-
Copyright (c) 2026 Ethan Ermovick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Ermovick
-/

module

public import Algolean.Algorithms.KMPPatternSearch

/-!
# Examples for LPS and KMP

This file contains some examples of KMP, including examples for `buildLPS` and `kmpPatternSearch`.
-/

@[expose] public section

namespace AlgoleanTests

open Algolean Algorithms

section LPSExamples

lemma empty_LPS [BEq α] :
    let pat : List α := []
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =               [] := by
  rfl

lemma singleton_LPS [BEq α] (x : α) :
    let pat := [x]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0] := by
  rfl

lemma repeated_LPS [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    let pat := List.replicate n x
    let lps := (buildLPS pat).eval Comparison.natCost
    lps = List.range n := by
  obtain ⟨hlen, hlps⟩ := buildLPS_eval (List.replicate n x)
  refine List.ext_getElem (by simpa using hlen) fun i hi hi' => ?_
  have hrep : LongestPrefixSuffixOf (List.replicate n x) (i + 1) i := by
    refine ⟨⟨by lia, ?_⟩, fun l hl => Nat.le_of_lt_succ hl.1⟩
    intro j hj
    rw [List.getElem?_eq_getElem (by lia), List.getElem?_eq_getElem (by lia)]
    simp
  simpa using Nat.le_antisymm
    (hrep.2 _ (hlps i (by simpa using hi')).1)
    ((hlps i (by simpa using hi')).2 _ hrep.1)

lemma nonoverlapping_LPS :
    let pat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rfl

lemma alternating_LPS :
    let pat := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 2, 3, 4, 5, 6, 7, 8] := by
  rfl

lemma random_LPS1 :
    let pat := [1, 0, 1, 0, 1, 0, 1, 1, 1, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 2, 3, 4, 5, 1, 1, 1] := by
  rfl

lemma random_LPS2 :
    let pat := [1, 0, 1, 1, 1, 0, 0, 0, 0, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 0, 1, 1, 1, 2, 0, 0, 0, 1] := by
  rfl

lemma random_LPS3 :
    let pat := [0, 0, 1, 0, 0, 1, 0, 1, 1, 1]
    let lps := (buildLPS pat).eval Comparison.natCost
    lps =      [0, 1, 0, 1, 2, 3, 4, 0, 0, 0] := by
  rfl

end LPSExamples

section KMPExamples

lemma empty_pattern_KMP [BEq α] (txt : List α) :
    let pat := []
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = List.range txt.length := by
  rfl

lemma empty_text_KMP [BEq α] (pat : List α) :
    let txt := []
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [] := by
  cases pat with
  | nil => rfl
  | cons x xs => simp [kmpPatternSearch, kmpSearchLoop]

lemma single_character_KMP [BEq α] [LawfulBEq α] (x : α) (n : Nat) :
    let pat := [x]
    let txt := List.replicate n x
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = List.range n := by
  dsimp
  rw [kmpPatternSearch_eval]
  have hdrop : ∀ a < n, 1 ≤ n - a := by
    intro a ha
    exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt ha)
  simpa [PatternSearchAll] using hdrop

lemma single_match_KMP :
    let pat := [1, 0]
    let txt := [0, 1, 1, 2, 3, 0, 0, 1, 0]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [7] := by
  rfl

lemma double_match_KMP :
    let pat := [1, 0]
    let txt := [0, 1, 0, 2, 3, 0, 0, 1, 0]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [1, 7] := by
  rfl

lemma overlapping_KMP1 :
    let pat := [1, 1, 1]
    let txt := [1, 1, 1, 1, 1, 1, 1]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [0, 1, 2, 3, 4] := by
  rfl

lemma overlapping_KMP2 :
    let pat := [1, 0, 1, 0]
    let txt := [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [0, 2, 4, 6] := by
  rfl

lemma overlapping_KMP3 :
    let pat := [1, 2, 3, 4, 7, 1, 2]
    let txt := [3, 6, 1, 2, 3, 4, 7, 1, 2, 3, 4, 7, 1, 2]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [2, 7] := by
  rfl

lemma overlapping_KMP4 :
    let pat := [1, 0, 1]
    let txt := [3, 1, 0, 1, 0, 1, 0, 3, 4]
    let matchesFound := (kmpPatternSearch pat txt).eval Comparison.natCost
    matchesFound = [1, 3] := by
  rfl

end KMPExamples

end AlgoleanTests
