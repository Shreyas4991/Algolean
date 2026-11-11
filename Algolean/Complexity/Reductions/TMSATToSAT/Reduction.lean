/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Formula
public import Algolean.Complexity.Reductions.TMSATToSAT.Size

/-!
# Converting TMSAT instances to SAT formulas

* `formula_satisfiable_iff` proves that the constructed CNF formula is satisfiable exactly
  when the TMSAT instance has an accepting certificate.
* `reduceWord_correct` proves that the conversion of encoded words preserves both yes and
  no answers, including rejection of incorrectly encoded inputs.
* `reduceWord_length_polynomial` bounds the output length by a polynomial in the input length.

The construction and supporting proofs are in `Formula`. The length estimates are in `Size`.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT

open Computability Problems Problems.SAT Problems.TMSAT Formula

variable {Γ : Type} [Fintype Γ]

/-- The constructed formula is satisfiable exactly when the machine instance is satisfiable. -/
theorem formula_satisfiable_iff (problem : Instance Γ) (yes : Γ) :
    formula problem yes ∈ CNF.satisfiable ↔ problem ∈ satisfiable yes := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact (CNF.rename_mem_satisfiable_iff _ _ Variable.name_injective).trans
    (indexedFormula_satisfiable_iff problem yes)

/-- The conversion preserves both yes and no answers, including rejection of malformed words. -/
theorem reduceWord_correct [Nontrivial Γ] (yes : Γ) (word : List Γ) :
    word ∈ TMSAT.languageOver yes ↔ reduceWord yes word ∈ SAT.languageOver := by
  classical
  cases h : TMSAT.encodingOver.decode word with
  | none =>
    simp [reduceWord, h, TMSAT.languageOver, encodedLanguage, CNF.satisfiable,
      CNF.SatisfiedBy, CNF.eval, Clause.eval]
  | some problem =>
    simpa only [reduceWord, h, SAT.encode_mem_languageOver, formula_satisfiable_iff,
      TMSAT.languageOver] using
      mem_encodedLanguage_iff_of_decode_eq_some (satisfiable yes) TMSAT.encodingOver h

/--
The converted SAT word has polynomially bounded length in the original TMSAT word's length.
The polynomial is fixed for the alphabet. This bounds the output length; the writing machine
still needs a separate running-time proof.
-/
theorem reduceWord_length_polynomial [Nontrivial Γ] :
    ∃ bound : Polynomial Nat, ∀ (yes : Γ) (word : List Γ),
      (reduceWord yes word).length ≤ bound.eval word.length :=
  ⟨Size.lengthBound, Size.reduceWord_length_le⟩

end Algolean.Algorithms.TMSATToSAT
