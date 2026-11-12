/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Classes.NP.Verification
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Formula
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Size
import Mathlib.Data.List.Perm.Basic

/-!
# SAT formulas for a fixed NP verifier

* `formula` describes the bounded computation of one fixed verifier on the given input and
  an unknown certificate. Its satisfying assignments describe accepting computations.
* `encode` writes that formula in the existing SAT encoding over the input alphabet.
* `NP.exists_sat_formulas` chooses a verifier and polynomial bounds for an NP language.
  The encoded formula is satisfiable exactly when the original input belongs to that language.

The verifier and both polynomials are fixed for the language. The construction reuses the
existing computation clauses and their correctness proof. The output is a SAT instance over
the same finite alphabet as the input.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

attribute [local instance 100] Fintype.toEncodable

namespace Algolean.Algorithms.NPToSAT

open Cslib.Turing Computability Problems

variable {Γ : Type} [Fintype Γ]

open Classical in
/--
These clauses exclude forbidden next heads. The next head is chosen before the scanned symbol,
so the machine can write all fixed symbol cases during one visit to a pair of head choices.
-/
@[expose] noncomputable def controlClauses (problem : BoundedVerification Γ) :
    SAT.CNF (NPToSAT.Computation.Variable problem) :=
  (List.finRange problem.time).flatMap fun time =>
    (NPToSAT.Computation.controlChoices problem).flatMap fun first =>
      (NPToSAT.Computation.controlChoices problem).flatMap fun second =>
        (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.flatMap fun symbol =>
          if NPToSAT.Computation.controlAllowed problem first symbol second then
          ([] : SAT.CNF (NPToSAT.Computation.Variable problem)) else
            [SAT.Clause.forbid [.head time.castSucc first, .tape time.castSucc first.1 symbol,
              .head time.succ second]]

private theorem flatMap_comm_perm {α β γ : Type*} (first : List α) (second : List β)
    (part : α → β → List γ) :
    (first.flatMap fun a => second.flatMap (part a)).Perm
      (second.flatMap fun b => first.flatMap fun a => part a b) := by
  induction first with
  | nil => simp
  | cons a first ih =>
    simp only [List.flatMap_cons]
    exact (ih.append_left _).trans (List.flatMap_append_perm second (part a) _)

private theorem controlClauses_perm (problem : BoundedVerification Γ) :
    (controlClauses problem).Perm (NPToSAT.Computation.controlClauses problem) := by
  classical
  apply List.Perm.flatMap_left (List.finRange problem.time)
  intro time _
  apply List.Perm.flatMap_left (NPToSAT.Computation.controlChoices problem)
  intro first _
  refine (flatMap_comm_perm (NPToSAT.Computation.controlChoices problem)
    (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
    (fun second symbol => if NPToSAT.Computation.controlAllowed problem first symbol second then
          ([] : SAT.CNF (NPToSAT.Computation.Variable problem)) else
      [SAT.Clause.forbid [.head time.castSucc first, .tape time.castSucc first.1 symbol,
        .head time.succ second]])).trans ?_
  apply List.Perm.flatMap_left (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
  intro symbol _
  apply List.Perm.of_eq
  rw [← List.filterMap_eq_filter, List.map_filterMap]
  simp only [List.filterMap_eq_flatMap_toList]
  congr 1
  funext second
  by_cases h : NPToSAT.Computation.controlAllowed problem first symbol second <;> simp [h]

/--
These clauses require successive recorded configurations to follow the fixed verifier's
transition rule. They describe the written symbol, the next head, and the unchanged cells.
-/
@[expose] noncomputable def stepClauses (problem : BoundedVerification Γ) :
    SAT.CNF (NPToSAT.Computation.Variable problem) :=
  NPToSAT.Computation.writeClauses problem ++ controlClauses problem ++
    NPToSAT.Computation.unchangedClauses problem

/--
This joins the certificate, head, tape, initial, transition, and acceptance clauses in the
order written by the direct reduction machine.
-/
@[expose] noncomputable def indexedFormula [DecidableEq Γ]
    (problem : BoundedVerification Γ) (yes : Γ) :
    SAT.CNF (NPToSAT.Computation.Variable problem) :=
  NPToSAT.Computation.choiceClauses problem ++ NPToSAT.Computation.initialClauses problem ++
    stepClauses problem ++ NPToSAT.Computation.Formula.finalClauses problem yes

private theorem indexedFormula_perm [DecidableEq Γ] (problem : BoundedVerification Γ) (yes : Γ) :
    (indexedFormula problem yes).Perm (NPToSAT.Computation.Formula.indexedFormula problem yes) := by
  classical
  have h := (controlClauses_perm problem).append_right
    (NPToSAT.Computation.unchangedClauses problem ++
      NPToSAT.Computation.Formula.finalClauses problem yes)
  simpa [indexedFormula, stepClauses,
    NPToSAT.Computation.Formula.indexedFormula, NPToSAT.Computation.stepClauses,
    List.append_assoc] using ((h.append_left (NPToSAT.Computation.writeClauses problem)).append_left
      (NPToSAT.Computation.initialClauses problem)).append_left
        (NPToSAT.Computation.choiceClauses problem)

open Classical in
/-- This describes the accepting computations of the fixed verifier on one input word. -/
@[expose] noncomputable def formula (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) : SAT.CNF SAT.Variable :=
  (indexedFormula
    (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
      BoundedVerification Γ)
      yes).rename
      NPToSAT.Computation.Variable.name

private theorem formula_perm (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    (formula verifier certificate time yes input).Perm (NPToSAT.Computation.formula
      (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
        BoundedVerification Γ)
        yes) := by
  classical
  simpa only [formula, NPToSAT.Computation.formula, SAT.CNF.rename] using
    (indexedFormula_perm
      (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
        BoundedVerification Γ)
        yes).map
        (fun clause => clause.rename NPToSAT.Computation.Variable.name)

private theorem satisfiable_iff_of_perm {α : Type*} {first second : SAT.CNF α}
    (h : first.Perm second) : first ∈ SAT.CNF.satisfiable ↔ second ∈ SAT.CNF.satisfiable := by
  apply exists_congr
  intro assignment
  simp only [SAT.CNF.satisfiedBy_iff_forall_clause]
  constructor
  · intro hs clause hc
    exact hs clause (h.mem_iff.mpr hc)
  · intro hs clause hc
    exact hs clause (h.mem_iff.mp hc)

private theorem encoding_length_eq_of_perm {first second : SAT.CNF SAT.Variable}
    (h : first.Perm second) : (SAT.encoding.encode first).length =
      (SAT.encoding.encode second).length := by
  have hp := ((h.flatMap_right fun clause =>
    SAT.certificateEncoding.encode clause ++ [(.inr 4 : SAT.CodeSymbol)]).append_right
      [.inr 5]).length_eq
  simpa only [SAT.encoding_encode_eq_formulaPrefix, SAT.formulaPrefix] using hp

/-- This writes the fixed verifier's computation formula using the existing SAT encoding. -/
@[expose] noncomputable def encode [Nontrivial Γ]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) : List Γ :=
  SAT.encodingOver.encode (formula verifier certificate time yes input)

/-- Encoding the computation formula preserves whether the fixed verifier accepts a certificate. -/
theorem encode_mem_languageOver [Nontrivial Γ]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    encode verifier certificate time yes input ∈ SAT.languageOver ↔
      (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
        BoundedVerification Γ) ∈
        accepted yes := by
  rw [encode, SAT.encode_mem_languageOver]
  exact (satisfiable_iff_of_perm (formula_perm verifier certificate time yes input)).trans
    (NPToSAT.Computation.formula_satisfiable_iff _ yes)

/-- The length of the encoded formula is bounded by a polynomial in the input length. -/
theorem encode_length_le [Nontrivial Γ]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    (encode verifier certificate time yes input).length ≤
      (NPToSAT.Computation.Size.fixedVerifierLengthBound (Γ := Γ)
        verifier.states certificate time).eval
        input.length := by
  have hlength := encoding_length_eq_of_perm (formula_perm verifier certificate time yes input)
  simpa only [encode, SAT.length_encodingOver, hlength] using
    NPToSAT.Computation.Size.fixedVerifier_length_le verifier certificate time yes input

end Algolean.Algorithms.NPToSAT

namespace Algolean.Algorithms

open Cslib.Turing Problems

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
Every NP language has one fixed verifier and polynomial bounds whose computation formulas
are satisfiable exactly on the language's inputs. Their encodings have polynomial length.
-/
theorem NP.exists_sat_formulas {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (verifier : SingleTapeTM.Description (TapeSymbol Γ))
      (certificate time bound : Polynomial Nat),
      (∀ input, input ∈ L ↔
        NPToSAT.encode verifier certificate time yes input ∈ SAT.languageOver) ∧
      ∀ input, (NPToSAT.encode verifier certificate time yes input).length ≤
        bound.eval input.length := by
  obtain ⟨verifier, certificate, time, hcorrect⟩ := NP.exists_bounded_verifier h yes
  exact ⟨verifier, certificate, time,
    NPToSAT.Computation.Size.fixedVerifierLengthBound (Γ := Γ) verifier.states certificate time,
    fun input => (hcorrect input).trans (NPToSAT.encode_mem_languageOver _ _ _ _ input).symm,
    NPToSAT.encode_length_le verifier certificate time yes⟩

end Algolean.Algorithms
