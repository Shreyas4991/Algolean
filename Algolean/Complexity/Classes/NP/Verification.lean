/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CertificatePadding
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Comparison
public import Algolean.Complexity.Classes.NP
public import Algolean.Problems.SingleTapeTM.Encodings.Certificates
public import Algolean.Models.SingleTapeTM.BoundedVerificationCompiler
import Mathlib.Logic.Equiv.List

/-!
# Fixed verifiers for languages in NP

* `NP.exists_single_symbol_verifier` gives a polynomial-time verifier that leaves one answer
  symbol on an otherwise blank tape.
  It compares the original verifier's whole output with its acceptance word.
* `NP.exists_exact_length_verifier` constructs a polynomial-time verifier with exact certificate
  lengths and one-symbol answers.
* `NP.fixed_length_certificates` replaces certificates of bounded length with certificates of
  exactly `2 * q(n) + 1` symbols. Decoding removes the added symbols before verification.
* `NP.exists_bounded_verifier` compiles the fixed verifier and gives polynomial certificate
  and transition bounds that depend only on the original input length.

The input and certificate alphabet is `Γ`. As in the definition of NP, a separate symbol marks
where the input ends and the certificate begins on the verifier's tape. Certificate padding
uses two distinct symbols of `Γ`; it does not add another certificate symbol.

The decoder reports failure with the empty word. Every recovered pair contains a separator, so
an empty result is rejected before running the original verifier. This remains necessary when
the original verifier accepts the empty word.
-/

@[expose] public section

attribute [local instance 100] Fintype.toEncodable Encodable.decidableEqOfEncodable

namespace Algolean.Algorithms

open Cslib.Turing Alphabet Polynomial SingleTapeTM.BoundedVerification

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
An NP language has a polynomial-time verifier whose output is a single symbol. That symbol is
`yes` exactly on accepted pairs; rejection produces the separator symbol instead. The verifier
first runs the original computation, then compares its entire output with the acceptance word.
The certificate length is still bounded above by a polynomial in the original input length.
-/
theorem NP.exists_single_symbol_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ certificate : List Γ,
        certificate.length ≤ q.eval input.length ∧
          f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
  obtain ⟨A, q, ⟨g, accepted, ⟨computer⟩, hg⟩, hL⟩ := h
  let f := fun word => [if g word = accepted then (.inl yes : Extended Γ 1) else .inr 0]
  refine ⟨f, q, ⟨computer.compareOutput accepted (.inl yes) (.inr 0)⟩, ?_, ?_⟩
  · intro word
    by_cases hword : g word = accepted <;> simp [f, hword]
  intro input
  rw [hL input]
  apply exists_congr
  intro certificate
  apply and_congr_right
  intro _
  simpa [f] using (hg ((wordPair Γ).encode (input, certificate))).symm

/--
Every bounded certificate can be replaced by a certificate of exactly `2 * q(n) + 1` symbols.
The fixed-length word records the original certificate and unused padding. Conversely, every
successfully decoded word of that length gives a certificate within the original bound.
The decoder used in `NP.exists_exact_length_verifier` implements this certificate representation.
-/
theorem NP.fixed_length_certificates {L : Language Γ} (h : L ∈ NP)
    [DecidableEq Γ] (next stop : Γ) (hne : next ≠ stop) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ word : List Γ, word.length = 2 * q.eval input.length + 1 ∧
        ∃ certificate, Problems.CertificatePadding.decode next stop word = some certificate ∧
          f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
  obtain ⟨f, q, computer, answers, hcorrect⟩ := NP.exists_single_symbol_verifier h yes
  refine ⟨f, q, computer, answers, fun input => ?_⟩
  exact (hcorrect input).trans
    (Problems.CertificatePadding.exists_fixed_length_iff next stop hne _ _)

/--
An input belongs to an NP language exactly when some certificate of the stated polynomial
length makes this verifier produce exactly the one-symbol acceptance word. The length condition
restricts the certificates considered in this theorem. The fixed program removes the added
certificate symbols, rejects failed decoding, runs the original verifier, and compares its
whole output with the acceptance word. Its time bound includes all these operations.
-/
theorem NP.exists_exact_length_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ certificate : List Γ,
        certificate.length = q.eval input.length ∧
          f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
  obtain ⟨stop, hstop⟩ := exists_ne yes
  have hne : yes ≠ stop := Ne.symm hstop
  obtain ⟨f, q, ⟨computer⟩, answers, hcorrect⟩ :=
    NP.fixed_length_certificates h yes stop hne yes
  let prepare := SingleTapeTuringMachines.CertificatePadding.result yes stop
  let normalized := fun word => if (prepare word).isEmpty then [.inr 0] else f (prepare word)
  have hcomputer : Nonempty (TMQuery.PolyTimeComputable normalized) :=
    ⟨(SingleTapeTuringMachines.CertificatePadding.computer yes stop hne).comp
      (computer.onNonempty (.inr 0))⟩
  have hword (input word : List Γ) :
      normalized ((wordPair Γ).encode (input, word)) = [.inl yes] ↔
        ∃ certificate, Problems.CertificatePadding.decode yes stop word = some certificate ∧
          f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
    dsimp only [normalized, prepare]
    simp only [SingleTapeTuringMachines.CertificatePadding.result_wordPair]
    cases hd : Problems.CertificatePadding.decode yes stop word <;>
      simp [wordPair_encode]
  refine ⟨normalized, 2 * q + 1, hcomputer, ?_, fun input => ?_⟩
  · intro word
    dsimp only [normalized]
    split
    · exact Or.inr rfl
    · exact answers (prepare word)
  rw [hcorrect input]
  simp only [eval_add, eval_mul, eval_ofNat, eval_one]
  exact exists_congr fun word => and_congr_right fun _ => (hword input word).symm

/--
Every NP language has a fixed verifier and polynomial certificate and time bounds. Membership
means that the verifier accepts some certificate of exactly that length within the time bound.
-/
theorem NP.exists_bounded_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (certificate time : Polynomial ℕ),
      ∀ input, input ∈ L ↔
        (⟨verifier, input, certificate.eval input.length, time.eval input.length⟩ :
          SingleTapeTM.BoundedVerification Γ) ∈ accepted yes := by
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
