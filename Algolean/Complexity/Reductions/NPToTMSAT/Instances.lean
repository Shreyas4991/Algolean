/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Normalization
public import Algolean.Problems.Encodings.TMSAT

/-!
# Turning an NP verifier into TMSAT instances

* `NP.exists_tmsat_instances` provides one finite transition table and two polynomials for an
  NP language. On input `x`, the resulting instance contains that table, `x`, the certificate
  length, and the transition bound.
* The instance is satisfiable exactly when `x` belongs to the original language.
* `NP.exists_tmsat_instances_with_size` also bounds the length of its encoding over `Γ` by a
  polynomial in the original input length.

The machine description is fixed for the language, independently of the input. The query compiler
adds a constant factor and a constant term to the verifier's time bound. The verifier's polynomial
is evaluated at the length of the input and certificate together, including their separator.
The resulting certificate and transition bounds depend only on the original input length.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing Polynomial Alphabet Problems.TMSAT

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

private noncomputable local instance : Encodable Γ :=
  Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)

/--
Every NP language has one fixed Turing machine description and polynomial certificate and time
bounds that give equivalent TMSAT instances. Both bounds depend only on the original input length.
The description is compiled once from the prepared verifier; it does not depend on the input.
This statement gives the instances and proves their correctness. The serializer in
`Algorithms/SingleTapeTuringMachines/TMSAT/Serialization.lean` writes their encoded words for
the final Karp reduction.
-/
theorem NP.exists_tmsat_instances {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (m t : Polynomial ℕ),
      ∀ input, input ∈ L ↔
        (⟨verifier, input, m.eval input.length, t.eval input.length⟩ : Instance Γ) ∈
          satisfiable yes :=
  NP.exists_bounded_verifier h yes

/--
The equivalent TMSAT instances can be encoded over the original alphabet with polynomially
bounded length. The fixed machine description contributes a constant; the input contributes
linearly, and the two unary fields contribute their polynomial values. The serializer's
polynomial running time is proved in the TMSAT serializer's file.
-/
theorem NP.exists_tmsat_instances_with_size {L : Language Γ} (h : L ∈ NP) (yes : Γ) :
    ∃ (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (m t p : Polynomial ℕ),
      (∀ input, input ∈ L ↔
        encodingOver.encode (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
          Instance Γ) ∈ languageOver yes) ∧
      ∀ input, (encodingOver.encode (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
        Instance Γ)).length ≤ p.eval input.length := by
  classical
  obtain ⟨verifier, m, t, hcorrect⟩ := NP.exists_tmsat_instances h yes
  obtain ⟨factor, hfactor⟩ :=
    SingleTapeTM.Description.exists_wordEncoding_length_bound (Symbol := Γ)
  let size := C ((SingleTapeTM.Description.encoding.encode verifier).length + 4) +
    C factor * X + m + t
  refine ⟨verifier, m, t, C (Fintype.card CodeSymbol) * size, ?_, ?_⟩
  · intro input
    simpa using hcorrect input
  · intro input
    let problem : Instance Γ := ⟨verifier, input, m.eval input.length, t.eval input.length⟩
    have hraw : (encoding.encode problem).length ≤ size.eval input.length := by
      have hi := hfactor input
      simp only [length_encoding, problem]
      dsimp only [size]
      simp only [eval_add, eval_C, eval_mul, eval_X]
      lia
    have hencoded := Nat.mul_le_mul_right (Fintype.card CodeSymbol) hraw
    simpa [length_encodingOver, Nat.mul_comm] using hencoded

end Algolean.Algorithms
