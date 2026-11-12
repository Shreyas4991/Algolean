/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Formula
import Mathlib.Tactic.GCongr

/-!
# The length of a fixed verifier's SAT formula

The bounds count clauses, literals, and binary variable names. For a fixed verifier and
polynomial certificate and time bounds, the encoded formula has polynomial length in the
original input length. The alphabet and verifier contribute fixed constants.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

attribute [local instance 100] Fintype.toEncodable

namespace Algolean.Algorithms.NPToSAT.Computation

open Computability Problems Problems.SAT

variable {Γ : Type}

open Formula

private noncomputable def alphabetCodeBound [Fintype Γ] [Encodable Γ] : Nat :=
  max ((Finset.univ : Finset Γ).sup fun symbol => (Encodable.encode symbol).size)
    ((Finset.univ : Finset (Option (TapeSymbol Γ))).sup
      fun symbol => (Encodable.encode symbol).size)

private theorem variableName_length_le [Fintype Γ] [Encodable Γ] {problem : BoundedVerification Γ}
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

private theorem indexedFormula_bounds (problem : BoundedVerification Γ) (yes : Γ) :
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

private theorem indexedFormula_encoded_length [Encodable Γ]
    (problem : BoundedVerification Γ) (yes : Γ) :
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

/--
This polynomial bounds the encoded formula for a fixed verifier. The certificate and time
bounds are evaluated at the original input length, and the verifier's state count is constant.
-/
noncomputable def fixedVerifierLengthBound (states : Nat) (certificate time : Polynomial Nat) :
    Polynomial Nat :=
  8 * lengthExpression (Polynomial.C (Fintype.card Γ))
    (Polynomial.C (alphabetCodeBound (Γ := Γ))) certificate time
    (Polynomial.X + certificate + 2 * time + 1) (Polynomial.C states)

/-- The formula for a fixed verifier has polynomial length in the original input word. -/
theorem fixedVerifier_length_le [Nontrivial Γ]
    (verifier : Cslib.Turing.SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    ((SAT.encodingOver (Γ := Γ)).encode (formula
      (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
        BoundedVerification Γ)
      yes)).length ≤
        (fixedVerifierLengthBound (Γ := Γ) verifier.states certificate time).eval input.length := by
  classical
  have h := indexedFormula_encoded_length
    (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
      BoundedVerification Γ) yes
  rw [SAT.length_encodingOver]
  have heval :
      (fixedVerifierLengthBound (Γ := Γ) verifier.states certificate time).eval input.length =
        8 * lengthExpression (Fintype.card Γ) (alphabetCodeBound (Γ := Γ))
          (certificate.eval input.length) (time.eval input.length)
          (input.length + certificate.eval input.length + 2 * time.eval input.length + 1)
          verifier.states := by
    simp only [fixedVerifierLengthBound, lengthExpression, clauseCountExpression,
      Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_one]
  rw [heval, Nat.mul_comm 8]
  exact Nat.mul_le_mul_right 8 h

end Size

end Algolean.Algorithms.NPToSAT.Computation
