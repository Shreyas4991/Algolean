/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Instances
public import Algolean.Algorithms.SingleTapeTuringMachines.TMSAT.Serialization
public import Algolean.Models.SingleTapeTM.Composition.KarpReduction

/-!
# Every NP language reduces to TMSAT

For each language in NP, one fixed verifier and two fixed polynomials determine its TMSAT
instances. The serializer writes those instances in polynomial time, using the same finite
alphabet as the source language. The constructed instance is satisfiable exactly when the
original input belongs to the source language.

The alphabet has at least two symbols. The verifier, polynomials, symbol codes, and serializer
are all fixed for the language, independently of the input and its length.
-/

public section

namespace Algolean.Algorithms

open Cslib.Turing Problems.TMSAT SingleTapeTuringMachines

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
This reduction writes the input's TMSAT instance using one fixed verifier and two fixed
polynomials. The verifier, polynomials, and writing program are chosen once for the language.
The same finite program handles every input length and uses the original alphabet.
-/
noncomputable def NP.tmsatReduction {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    KarpReduction L (languageOver yes) := by
  classical
  choose verifier m t hcorrect using NP.exists_tmsat_instances h yes
  exact {
    transform := fun input => encodingOver.encode
      (⟨verifier, input, m.eval input.length, t.eval input.length⟩ : Instance Γ)
    computer := tmsatSerializer verifier m t
    correct := fun input => by simpa using hcorrect input }

/-- Every language in NP has a polynomial-time Karp reduction to TMSAT over the same alphabet. -/
theorem NP.karpReducible_tmsat {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    KarpReducible L (languageOver yes) := ⟨NP.tmsatReduction h yes⟩

end Algolean.Algorithms
