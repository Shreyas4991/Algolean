/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler
public import Algolean.Models.SingleTapeTM.BoundedVerification

/-!
# Compiling bounded verifiers

* `ofQueryVerifier` converts a fixed Query verifier to a transition table and records its
  time bound.
* `mem_accepted_ofQueryVerifier_iff` proves that compilation preserves exactly which
  certificates make the verifier return its one-symbol acceptance word.

The machine reads the input, one separator, and the certificate. For input length `n` and
certificate length `m`, a Query time bound `T(n + m + 1)` becomes `C * T(n + m + 1) + C`
transitions. The constant depends only on the fixed verifier program.
-/

@[expose] public section

namespace Cslib.Turing.SingleTapeTM.BoundedVerification

open Algolean.Algorithms Algolean.Algorithms.Alphabet

variable {Γ : Type} [Fintype Γ]
variable {f : List (TapeSymbol Γ) → List (TapeSymbol Γ)}

/-- This records the compiled verifier and its transition bound for the specified input. -/
noncomputable def ofQueryVerifier (computer : TMQuery.TimeComputable f)
    (input : List Γ) (certificateLength : ℕ) : BoundedVerification Γ :=
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  let C := TMQuery.Compiler.transitionFactor computer.program
  { verifier := TMQuery.Compiler.compile computer.program
    input := input
    certificateLength := certificateLength
    time := C * computer.timeBound (input.length + certificateLength + 1) + C }

/-- The compiled verifier accepts exactly the certificates accepted by the Query verifier. -/
theorem mem_accepted_ofQueryVerifier_iff (yes : Γ)
    (computer : TMQuery.TimeComputable f) (input : List Γ) (certificateLength : ℕ) :
    ofQueryVerifier computer input certificateLength ∈ accepted yes ↔
      ∃ certificate : List Γ, certificate.length = certificateLength ∧
        f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  have hcertificate (certificate : List Γ) (hlen : certificate.length = certificateLength) :
      AcceptsWithin yes (ofQueryVerifier computer input certificateLength).verifier
          ((wordPair Γ).encode (input, certificate))
          (ofQueryVerifier computer input certificateLength).time ↔
        f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
    apply acceptsWithin_iff_of_outputsWithinTime
    have hlength : ((wordPair Γ).encode (input, certificate)).length =
        input.length + certificateLength + 1 := by simp [hlen, Nat.add_assoc]
    simpa only [ofQueryVerifier, hlength] using
      TMQuery.Compiler.time_bound computer.program
        (computer.outputsFunInTime ((wordPair Γ).encode (input, certificate)))
  simp only [accepted, Set.mem_ofPred_eq]
  exact exists_congr fun certificate => and_congr_right fun hlen => hcertificate certificate hlen

end Cslib.Turing.SingleTapeTM.BoundedVerification
