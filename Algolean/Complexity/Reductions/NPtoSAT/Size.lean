/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Formula

/-!
# A common size bound for the direct reduction

The verified clause writers use bounds on the lengths of their source words and accumulated
output. `sizeBound` bounds the unary certificate and time words, both copies of the position
and state words, the original input, and the complete encoded SAT formula.

The extra constant covers the extra symbols before the input and output, together with the
small constants in the writer bounds. The polynomial is fixed with the verifier and its
certificate and time bounds.
-/

public section

namespace Algolean.Algorithms.NPToSAT

open Cslib.Turing Problems Problems.TMSAT Polynomial

variable {Γ : Type} [Fintype Γ]

/-- This polynomial bounds all source-word lengths and the final encoded formula together. -/
@[expose] noncomputable def sizeBound (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) : Polynomial Nat :=
  certificate + time + 2 * (X + certificate + 2 * time + 1) +
    2 * C (verifier.states + 2) + X +
      NPToTMSAT.Size.fixedVerifierLengthBound (Γ := Γ) verifier.states certificate time + 128

/-- The polynomial bounds the unary source words, original input, and complete encoded output. -/
theorem source_size_le [Nontrivial Γ] (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    let problem : Instance Γ :=
      ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
    problem.certificateLength + problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (encode verifier certificate time yes input).length + 128 ≤
          (sizeBound verifier certificate time).eval input.length := by
  have hlength := encode_length_le verifier certificate time yes input
  dsimp only
  simp only [sizeBound, NPToTMSAT.width, eval_add, eval_mul, eval_X, eval_C, eval_ofNat, eval_one]
  lia


end Algolean.Algorithms.NPToSAT
