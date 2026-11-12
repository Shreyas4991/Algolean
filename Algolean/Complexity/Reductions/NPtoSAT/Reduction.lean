/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computer
public import Algolean.Models.SingleTapeTM.Composition.KarpReduction

/-!
# Every NP language reduces directly to SAT

* `NP.satReduction` constructs a polynomial-time Karp reduction from any language in NP to SAT.
* `NP.karpReducible_sat` states that such a reduction exists over the original finite alphabet.

The reduction fixes a verifier for the source language and writes a formula describing its
accepting computations. One finite single-tape Query program performs this conversion on
every input length. Its input is the original word, and its output is the encoded SAT formula.
-/

public section

namespace Algolean.Algorithms

open Cslib.Turing Problems

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
This fixed polynomial-time program converts a word to a SAT instance with the same answer.
The input, output, and reduction machine use the original finite alphabet.
-/
noncomputable def NP.satReduction {L : Language Γ} (h : L ∈ NP) :
    KarpReduction L SAT.languageOver := by
  classical
  choose verifier certificate time bound hcorrect hlength using
    NP.exists_sat_formulas h (default : Γ)
  exact {
    transform := NPToSAT.encode verifier certificate time default
    computer := NPToSAT.computer verifier certificate time default
    correct := fun input => by simpa using hcorrect input }

/-- Every language in NP has a polynomial-time Karp reduction to SAT over the same alphabet. -/
theorem NP.karpReducible_sat {L : Language Γ} (h : L ∈ NP) :
    KarpReducible L SAT.languageOver := ⟨NP.satReduction h⟩

end Algolean.Algorithms
