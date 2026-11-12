/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Formula

/-!
# Bounding the lengths used by the direct reduction

* `sizeBound` bounds the total lengths of the certificate and time bounds, both copies of the
  position and state bounds, the original input, and the complete encoded SAT formula.
* `source_size_le` proves this bound for the chosen encoding. `source_size_le_code` also covers
  any representation using at most eight tape cells for each formula symbol.

The clause writers use this bound for the words they read and the output they append.
The polynomial is fixed with the verifier and its certificate and time bounds. Its extra
constant accounts for the temporary symbols before the input and output and the writers' constants.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT

open Cslib.Turing Problems Polynomial

variable {Γ : Type} [Fintype Γ]

/--
This polynomial bounds the total lengths of the bound words, input, and final encoded formula.
-/
@[expose] noncomputable def sizeBound (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) : Polynomial Nat :=
  certificate + time + 2 * (X + certificate + 2 * time + 1) +
    2 * C (verifier.states + 2) + X +
      NPToSAT.Computation.Size.fixedVerifierLengthBound (Γ := Γ)
        verifier.states certificate time + 128

/-- The polynomial bounds the bound words, original input, and complete encoded output together. -/
theorem source_size_le [Nontrivial Γ] (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    let problem : BoundedVerification Γ :=
      ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
    problem.certificateLength + problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (encode verifier certificate time yes input).length + 128 ≤
          (sizeBound verifier certificate time).eval input.length := by
  have hlength := encode_length_le verifier certificate time yes input
  dsimp only
  simp only [sizeBound, NPToSAT.Computation.width,
    eval_add, eval_mul, eval_X, eval_C, eval_ofNat, eval_one]
  lia

/--
The same bound covers a representation using at most eight tape cells for each formula symbol.
-/
theorem source_size_le_code [Nontrivial Γ]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ)
    (code : SAT.CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (hsmall : width ≤ 8) :
    let problem : BoundedVerification Γ :=
      ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
    problem.certificateLength + problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        ((SAT.encoding.encode (formula verifier certificate time yes input)).flatMap code).length +
          128 ≤ (sizeBound verifier certificate time).eval input.length := by
  have hs := source_size_le verifier certificate time yes input
  have hl : ((SAT.encoding.encode (formula verifier certificate time yes input)).flatMap
      code).length ≤ (encode verifier certificate time yes input).length := by
    rw [encode, SAT.length_encodingOver, List.length_flatMap]
    simpa using (List.sum_le_sum (l := SAT.encoding.encode
      (formula verifier certificate time yes input)) (g := fun _ => 8)
        (fun symbol _ => (hwidth symbol).le.trans hsmall))
  dsimp only at *
  lia


end Algolean.Algorithms.NPToSAT
