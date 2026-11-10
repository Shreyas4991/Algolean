/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Instances
public import Algolean.Algorithms.SingleTapeTuringMachines.TMSAT
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
Every language in NP has a polynomial-time Karp reduction to TMSAT over the same finite
alphabet. The reduction writes one fixed verifier description, the original input, and unary
polynomial bounds. The serializer's machine and its finite program are fixed for the language
and work on every input length.
-/
theorem NP.karpReducible_tmsat {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    Nonempty (KarpReduction L (languageOver yes)) := by
  classical
  obtain ⟨verifier, m, t, hcorrect⟩ := NP.exists_tmsat_instances h yes
  refine ⟨{
    transform := fun input => encodingOver.encode
      (⟨verifier, input, m.eval input.length, t.eval input.length⟩ : Instance Γ)
    computer := tmsatSerializer verifier m t
    correct := ?_ }⟩
  intro input
  simpa using hcorrect input

/-- This chooses one verified polynomial-time reduction to TMSAT for the given NP language. -/
noncomputable def NP.tmsatReduction {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    KarpReduction L (languageOver yes) := Classical.choice (NP.karpReducible_tmsat h yes)

end Algolean.Algorithms
