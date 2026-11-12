/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Verifier
public import Algolean.Models.SingleTapeTM.BoundedVerificationCompiler

/-!
# Fixed bounded verifiers for NP languages

`NP.exists_bounded_verifier` chooses one transition-table verifier and polynomial certificate
and time bounds for an NP language. The original word belongs to the language exactly when
that verifier accepts a certificate of the specified length within the time bound.

The description is compiled once from a fixed Query program. The compiler adds a constant
factor and a constant term to its time bound. Both resulting polynomials depend only on the
original input length.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing Polynomial Alphabet SingleTapeTM.BoundedVerification

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
Every NP language has a fixed verifier and polynomial certificate and time bounds. Membership
means that the verifier accepts some certificate of exactly that length within the time bound.
-/
theorem NP.exists_bounded_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (certificate time : Polynomial ℕ),
      ∀ input, input ∈ L ↔
        (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
          SingleTapeTM.BoundedVerification Γ) ∈ accepted yes := by
  classical
  obtain ⟨f, certificate, ⟨computer⟩, _, hcorrect⟩ := NP.exists_exact_length_verifier h yes
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  let C := TMQuery.Compiler.transitionFactor computer.program
  let time := Polynomial.C C * computer.poly.comp (X + certificate + 1) + Polynomial.C C
  refine ⟨TMQuery.Compiler.compile computer.program, certificate, time, fun input => ?_⟩
  have heq : (⟨TMQuery.Compiler.compile computer.program, input, certificate.eval input.length,
      time.eval input.length⟩ : SingleTapeTM.BoundedVerification Γ) =
      ofQueryVerifier computer.polynomialBound input (certificate.eval input.length) := by
    simp [ofQueryVerifier, TMQuery.PolyTimeComputable.polynomialBound, time, C]
    constructor <;> rfl
  rw [heq, mem_accepted_ofQueryVerifier_iff]
  exact hcorrect input

end Algolean.Algorithms
