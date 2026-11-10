/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Comparison
public import Algolean.Algorithms.SingleTapeTuringMachines.CertificatePadding
public import Algolean.Problems.Certificates

/-!
# Preparing NP verifiers for TMSAT

* `NP.exists_head_verifier` supplies a polynomial-time verifier that returns one answer symbol.
  It compares the original verifier's whole output with its acceptance word.
* `NP.exists_exact_head_verifier` constructs a polynomial-time verifier with exact certificate
  lengths and one-symbol answers.
* `NP.fixed_length_certificates` replaces certificates of bounded length with certificates of
  exactly `2 * q(n) + 1` symbols. Decoding removes the added symbols before verification.

The input and certificate alphabet is `Γ`. As in the definition of NP, a separate symbol marks
where the input ends and the certificate begins on the verifier's tape. Certificate padding
uses two distinct symbols of `Γ`; it does not add another certificate symbol.

The decoder reports failure with the empty word. Every recovered pair contains a separator, so
an empty result is rejected before running the original verifier. This remains necessary when
the original verifier accepts the empty word.
-/

@[expose] public section

namespace Algolean.Algorithms

open Alphabet Polynomial

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
An NP language has a polynomial-time verifier whose output is a single symbol. That symbol is
`yes` exactly on accepted pairs; rejection produces the separator symbol instead. The verifier
first runs the original computation, then compares its entire output with the acceptance word.
The certificate length is still bounded above by a polynomial in the original input length.
-/
theorem NP.exists_head_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ certificate : List Γ,
        certificate.length ≤ q.eval input.length ∧
          (f ((wordPair Γ).encode (input, certificate))).head? = some (.inl yes) := by
  classical
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
This theorem describes the certificates; a machine must still perform the decoding.
-/
theorem NP.fixed_length_certificates {L : Language Γ} (h : L ∈ NP)
    [DecidableEq Γ] (next stop : Γ) (hne : next ≠ stop) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ word : List Γ, word.length = 2 * q.eval input.length + 1 ∧
        ∃ certificate, Problems.CertificatePadding.decode next stop word = some certificate ∧
          (f ((wordPair Γ).encode (input, certificate))).head? = some (.inl yes) := by
  obtain ⟨f, q, computer, answers, hcorrect⟩ := NP.exists_head_verifier h yes
  refine ⟨f, q, computer, answers, fun input => ?_⟩
  exact (hcorrect input).trans
    (Problems.CertificatePadding.exists_fixed_length_iff next stop hne _ _)

/--
An NP language has a polynomial-time verifier that accepts certificates of exactly a polynomial
length and leaves the chosen accepting symbol under its head. The fixed program removes the
certificate padding, rejects failed decoding, runs the original verifier, and compares its whole
output with the acceptance word. Its time bound includes the preprocessing and comparison.
-/
theorem NP.exists_exact_head_verifier {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (f : List (Extended Γ 1) → List (Extended Γ 1)) (q : Polynomial ℕ),
      Nonempty (TMQuery.PolyTimeComputable f) ∧
      (∀ word, f word = [.inl yes] ∨ f word = [.inr 0]) ∧
      ∀ input, input ∈ L ↔ ∃ certificate : List Γ,
        certificate.length = q.eval input.length ∧
          (f ((wordPair Γ).encode (input, certificate))).head? = some (.inl yes) := by
  classical
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
      (normalized ((wordPair Γ).encode (input, word))).head? = some (.inl yes) ↔
        ∃ certificate, Problems.CertificatePadding.decode yes stop word = some certificate ∧
          (f ((wordPair Γ).encode (input, certificate))).head? = some (.inl yes) := by
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

end Algolean.Algorithms
