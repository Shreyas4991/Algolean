/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Formula
import Mathlib.Tactic.GCongr

/-!
# The length of the constructed SAT word

The proof bounds the number of clauses, the number of literals in each clause, and the length
of each binary variable name. The TMSAT encoding bounds the machine's number of states, the
input length, and both unary bounds by the encoded input length. Together these estimates give
one polynomial bound for the output length, for each fixed alphabet.

This file proves a length bound. It does not prove the running time of a machine that writes
the formula.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT

open Computability Problems Problems.SAT Problems.TMSAT

variable {Γ : Type}

open Formula

private noncomputable def alphabetCodeBound [Fintype Γ] [Encodable Γ] : Nat :=
  max ((Finset.univ : Finset Γ).sup fun symbol => (Encodable.encode symbol).size)
    ((Finset.univ : Finset (Option (TapeSymbol Γ))).sup
      fun symbol => (Encodable.encode symbol).size)

private theorem variableName_length_le [Fintype Γ] [Encodable Γ] {problem : Instance Γ}
    (entry : Variable problem) :
    (Variable.name entry).length ≤ 2 * (problem.certificateLength + problem.time +
      width problem + problem.verifier.states + alphabetCodeBound (Γ := Γ) + 2) := by
  classical
  have hsize (n : Nat) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hsymbol (symbol : Γ) : (Encodable.encode symbol).size ≤ alphabetCodeBound (Γ := Γ) :=
    (Finset.le_sup (f := fun value : Γ => (Encodable.encode value).size)
      (Finset.mem_univ symbol)).trans (le_max_left _ _)
  have hcell (symbol : Option (TapeSymbol Γ)) :
      (Encodable.encode symbol).size ≤ alphabetCodeBound (Γ := Γ) :=
    (Finset.le_sup (f := fun value : Option (TapeSymbol Γ) => (Encodable.encode value).size)
      (Finset.mem_univ symbol)).trans (le_max_right _ _)
  have hstate (state : Option (Fin (problem.verifier.states + 1))) :
      (Encodable.encode state).size ≤ problem.verifier.states + 1 := by
    apply (hsize _).trans
    cases state with
    | none => simp
    | some state =>
      change state.val + 1 ≤ problem.verifier.states + 1
      exact state.isLt
  cases entry with
  | certificate position symbol =>
    rw [Variable.length_name_certificate]
    have hp := position.isLt
    have hs := hsymbol symbol
    have hn := hsize position.val
    lia
  | tape time position symbol =>
    rw [Variable.length_name_tape]
    have ht := time.isLt
    have hp := position.isLt
    have hs := hcell symbol
    have hn := hsize time.val
    have hm := hsize position.val
    lia
  | head time control =>
    obtain ⟨position, state⟩ := control
    rw [Variable.length_name_head]
    have ht := time.isLt
    have hp := position.isLt
    have hs := hstate state
    have hn := hsize time.val
    have hm := hsize position.val
    lia

private def clauseCountExpression {R : Type} [Semiring R]
    (alphabet m time cells states : R) : R :=
  let heads := cells * (states + 2)
  let symbols := alphabet + 2
  let choices := symbols + heads
  (m + (time + 1) * (cells + 1)) * (choices ^ 2 + 1) +
    ((1 + cells * (alphabet + 1)) +
      (time * heads * symbols * (1 + heads + cells) + (2 * cells + 1)))

private def lengthExpression {R : Type} [Semiring R]
    (alphabet code m time cells states : R) : R :=
  let literals := alphabet + 2 + cells * (states + 2) + cells + 3
  let digits := 2 * (m + time + cells + states + code + 2)
  clauseCountExpression alphabet m time cells states * (literals * (digits + 2) + 2) + 1

section Indexed

variable [Fintype Γ] [DecidableEq Γ]

private theorem indexedFormula_bounds (problem : Instance Γ) (yes : Γ) :
    let literals := Fintype.card Γ + 2 + width problem * (problem.verifier.states + 2) +
      width problem + 3
    (indexedFormula problem yes).length ≤ clauseCountExpression (Fintype.card Γ)
      problem.certificateLength problem.time (width problem) problem.verifier.states ∧
      ∀ clause ∈ indexedFormula problem yes, clause.length ≤ literals := by
  obtain ⟨hc, hcl⟩ := choiceClauses_bounds problem
  obtain ⟨hi, hil⟩ := initialClauses_bounds problem
  obtain ⟨hs, hsl⟩ := stepClauses_bounds problem
  have hf : (finalClauses problem yes).length = 2 * width problem + 1 := by
    simp [finalClauses, List.length_flatMap, Nat.mul_comm]
  have hfl : ∀ clause ∈ finalClauses problem yes, clause.length ≤ width problem + 2 := by
    simp only [finalClauses, List.forall_mem_cons, Clause.length_atLeastOne,
      List.length_map, List.length_finRange, List.forall_mem_flatMap, Clause.length_implies,
      List.length_cons, List.length_nil]
    simp
  constructor
  · simpa only [indexedFormula, List.length_append, clauseCountExpression] using
      Nat.add_le_add hc (Nat.add_le_add hi (Nat.add_le_add hs hf.le))
  · simp only [indexedFormula, List.forall_mem_append]
    exact ⟨fun clause h => (hcl clause h).trans (by lia),
      fun clause h => (hil clause h).trans (by lia),
      fun clause h => (hsl clause h).trans (by lia),
      fun clause h => (hfl clause h).trans (by lia)⟩

private theorem indexedFormula_encoded_length [Encodable Γ] (problem : Instance Γ) (yes : Γ) :
    (SAT.encoding.encode ((indexedFormula problem yes).rename Variable.name)).length ≤
      lengthExpression (Fintype.card Γ) (alphabetCodeBound (Γ := Γ))
        problem.certificateLength problem.time (width problem) problem.verifier.states := by
  let literals := Fintype.card Γ + 2 + width problem * (problem.verifier.states + 2) +
    width problem + 3
  let digits := 2 * (problem.certificateLength + problem.time + width problem +
    problem.verifier.states + alphabetCodeBound (Γ := Γ) + 2)
  obtain ⟨hc, hl⟩ := indexedFormula_bounds problem yes
  have hclause : ∀ clause ∈ (indexedFormula problem yes).rename Variable.name,
      clause.length ≤ literals := by
    intro clause h
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp h
    simpa [Clause.rename] using hl original ho
  have hname : ∀ literal ∈ ((indexedFormula problem yes).rename Variable.name).flatten,
      literal.name.length ≤ digits := by
    intro literal h
    obtain ⟨clause, hc, hl⟩ := List.mem_flatten.mp h
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hc
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hl
    cases entry <;> exact variableName_length_le _
  have he := SAT.length_encoding_le _ literals digits hclause hname
  have hm := Nat.mul_le_mul_right (literals * (digits + 2) + 2)
    (show ((indexedFormula problem yes).rename Variable.name).length ≤ _ from by
      simpa only [CNF.rename, List.length_map] using hc)
  exact he.trans (Nat.add_le_add_right hm 1)

end Indexed

variable [Fintype Γ]

namespace Size

/-- This polynomial bounds the length of every converted word over the fixed alphabet. -/
noncomputable def lengthBound : Polynomial Nat := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let b : Polynomial Nat := Polynomial.X + 1
  exact 24 + 8 * lengthExpression (Polynomial.C (Fintype.card Γ))
    (Polynomial.C (alphabetCodeBound (Γ := Γ))) b b (2 * b) b

/-- The explicit length bound holds for every input word, including incorrectly encoded ones. -/
theorem reduceWord_length_le [Nontrivial Γ] (yes : Γ) (word : List Γ) :
    (reduceWord yes word).length ≤ (lengthBound (Γ := Γ)).eval word.length := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let code := alphabetCodeBound (Γ := Γ)
  let size := word.length + 1
  have heval : (lengthBound (Γ := Γ)).eval word.length =
      24 + 8 * lengthExpression (Fintype.card Γ) code size size (2 * size) size := by
    simp [lengthBound, code, size, lengthExpression, clauseCountExpression]
  rw [heval]
  cases h : TMSAT.encodingOver.decode word with
  | none =>
    have hlength : (reduceWord yes word).length = 24 := by simp [reduceWord, h]
    rw [hlength]
    exact Nat.le_add_right _ _
  | some problem =>
    have hd := TMSAT.states_add_input_length_add_bounds_le_length_of_decodeOver h
    have hm : problem.certificateLength ≤ size := by dsimp [size]; lia
    have ht : problem.time ≤ size := by dsimp [size]; lia
    have hw : width problem ≤ 2 * size := by dsimp [width, size]; lia
    have hq : problem.verifier.states ≤ size := by dsimp [size]; lia
    have hraw : (SAT.encoding.encode (formula problem yes)).length ≤
        lengthExpression (Fintype.card Γ) code problem.certificateLength problem.time
          (width problem) problem.verifier.states := indexedFormula_encoded_length problem yes
    have hmono : lengthExpression (Fintype.card Γ) code problem.certificateLength problem.time
        (width problem) problem.verifier.states ≤
        lengthExpression (Fintype.card Γ) code size size (2 * size) size := by
      dsimp [lengthExpression, clauseCountExpression]
      gcongr
    calc
      (reduceWord yes word).length = (SAT.encoding.encode (formula problem yes)).length * 8 := by
        simp [reduceWord, h]
      _ ≤ lengthExpression (Fintype.card Γ) code problem.certificateLength problem.time
          (width problem) problem.verifier.states * 8 := Nat.mul_le_mul_right 8 hraw
      _ ≤ lengthExpression (Fintype.card Γ) code size size (2 * size) size * 8 :=
        Nat.mul_le_mul_right 8 hmono
      _ ≤ 24 + 8 * lengthExpression (Fintype.card Γ) code size size (2 * size) size := by
        rw [Nat.mul_comm]
        exact Nat.le_add_left _ _

end Size

end Algolean.Algorithms.TMSATToSAT
