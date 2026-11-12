/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.BoundedVerificationCompiler
public import Algolean.Problems.Encodings.TMSAT

/-!
# Building TMSAT instances from query verifiers

* `Instance.ofQueryVerifier` compiles a query verifier and provides its transition bound.
* A compiled instance is satisfiable exactly when some certificate of the specified length
  makes the query verifier produce exactly the one-symbol acceptance word.
* The same equivalence holds for the encoded TMSAT language.

The query verifier runs over `TapeSymbol` and receives the separator encoding of the input and
certificate. For input length `n` and certificate length `m`, this word has length `n + m + 1`.
A query time bound `T(n + m + 1)` becomes `C * T(n + m + 1) + C` machine transitions.
The query program and source machine fix `C`, independently of both lengths.
-/

@[expose] public section

namespace Algolean.Problems.TMSAT

open Algorithms Algorithms.Alphabet Cslib.Turing

variable {Γ : Type} [Fintype Γ]
variable {f : List (TapeSymbol Γ) → List (TapeSymbol Γ)}

/--
This instance uses the compiled query verifier and its proved transition bound. The certificate
length stays fixed, and the time bound uses the length of the full input-certificate word.
-/
noncomputable def Instance.ofQueryVerifier (computer : TMQuery.TimeComputable f)
    (input : List Γ) (certificateLength : ℕ) : Instance Γ :=
  SingleTapeTM.BoundedVerification.ofQueryVerifier computer input certificateLength

/--
Compiling the query verifier preserves exactly which certificates make its output equal the
one-symbol acceptance word. The specified certificate length is unchanged, and the transition
bound is sufficient for every certificate of that length.
-/
theorem mem_satisfiable_ofQueryVerifier_iff (yes : Γ)
    (computer : TMQuery.TimeComputable f)
    (input : List Γ) (certificateLength : ℕ) :
    Instance.ofQueryVerifier computer input certificateLength ∈ satisfiable yes ↔
      ∃ certificate : List Γ, certificate.length = certificateLength ∧
        f ((wordPair Γ).encode (input, certificate)) = [.inl yes] :=
  SingleTapeTM.BoundedVerification.mem_accepted_ofQueryVerifier_iff
    yes computer input certificateLength

/--
Encoding the compiled instance gives a word in the TMSAT language exactly when a certificate
of the specified length makes the query verifier produce exactly the one-symbol acceptance word.
-/
theorem encode_ofQueryVerifier_mem_language_iff [Encodable Γ] (yes : Γ)
    (computer : TMQuery.TimeComputable f)
    (input : List Γ) (certificateLength : ℕ) :
    encoding.encode (Instance.ofQueryVerifier computer input certificateLength) ∈
      language yes ↔
      ∃ certificate : List Γ, certificate.length = certificateLength ∧
        f ((wordPair Γ).encode (input, certificate)) = [.inl yes] := by
  rw [encode_mem_language]
  exact mem_satisfiable_ofQueryVerifier_iff yes computer input certificateLength

end Algolean.Problems.TMSAT
