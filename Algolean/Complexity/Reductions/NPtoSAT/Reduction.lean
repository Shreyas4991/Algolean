/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computer
public import Algolean.Complexity.Classes.NP.Verification
public import Algolean.Models.SingleTapeTM.Composition.KarpReduction

/-!
# Every NP language reduces directly to SAT

* `NP.satReduction` constructs a polynomial-time Karp reduction from any language in NP to SAT.
* `NP.karpReducible_sat` states that such a reduction exists over the original finite alphabet.
* `NP.satReductionToSAT` writes SAT's original formula encoding when the source uses that
  alphabet. `NP.karpReducible_SAT` states the corresponding reduction result.

The reduction fixes a verifier for the source language and writes a formula describing its
accepting computations. One finite single-tape Query program performs this conversion on
every input length. Its input is the original word, and its output is the encoded SAT formula.
The construction uses classical choice to select a verifier whose existence follows from
membership in NP.
-/

public section

namespace Algolean.Algorithms

open Cslib.Turing Problems

section

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
This constructs a polynomial-time reduction to SAT over the input alphabet. The output formula
is satisfiable exactly when the input belongs to the original language.
-/
noncomputable def NP.satReduction {L : Language Γ} (h : L ∈ NP) :
    KarpReduction L SAT.languageOver :=
  let ⟨verifier, hv⟩ := Classical.indefiniteDescription _
    (NP.exists_bounded_verifier h (default : Γ))
  let ⟨certificate, hc⟩ := Classical.indefiniteDescription _ hv
  let ⟨time, hcorrect⟩ := Classical.indefiniteDescription _ hc
  {
    transform := NPToSAT.encode verifier certificate time default
    computer := NPToSAT.computer verifier certificate time default
    correct := fun input => by
      simpa using (hcorrect input).trans
        (NPToSAT.encode_mem_languageOver verifier certificate time default input).symm }

/-- Every language in NP has a polynomial-time Karp reduction to SAT over the same alphabet. -/
theorem NP.karpReducible_sat {L : Language Γ} (h : L ∈ NP) :
    KarpReducible L SAT.languageOver := ⟨NP.satReduction h⟩

end

/--
This constructs a polynomial-time reduction from an NP language to SAT in its original encoding.
-/
noncomputable def NP.satReductionToSAT {L : Language SAT.CodeSymbol} (h : L ∈ NP) :
    KarpReduction L SAT :=
  let ⟨verifier, hv⟩ := Classical.indefiniteDescription _
    (NP.exists_bounded_verifier h (default : SAT.CodeSymbol))
  let ⟨certificate, hc⟩ := Classical.indefiniteDescription _ hv
  let ⟨time, hcorrect⟩ := Classical.indefiniteDescription _ hc
  {
    transform := fun input => SAT.encoding.encode
      (NPToSAT.formula verifier certificate time default input)
    computer := NPToSAT.formulaComputer verifier certificate time default
    correct := fun input => by
      simpa [NPToSAT.encode] using (hcorrect input).trans
        (NPToSAT.encode_mem_languageOver verifier certificate time default input).symm }

/-- Every NP language over the formula alphabet has a polynomial-time Karp reduction to SAT. -/
theorem NP.karpReducible_SAT {L : Language SAT.CodeSymbol} (h : L ∈ NP) :
    KarpReducible L SAT := ⟨NP.satReductionToSAT h⟩

end Algolean.Algorithms
