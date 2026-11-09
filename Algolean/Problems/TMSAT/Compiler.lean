/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler
public import Algolean.Problems.TMSAT.Encoding

/-!
# Building TMSAT instances from query verifiers

* `Instance.ofQueryVerifier` compiles a query verifier and supplies its transition bound.
* A compiled instance is satisfiable exactly when some certificate of the specified length
  makes the query verifier produce an output starting with a true bit.
* The same equivalence holds for the encoded TMSAT language.

The query verifier runs over `TapeSymbol` and receives the separator encoding of the input and
certificate. For input length `n` and certificate length `m`, this word has length `n + m + 1`.
A query time bound `T(n + m + 1)` becomes `C * T(n + m + 1) + C` machine transitions.
The query program and source machine fix `C`, independently of both lengths.
-/

@[expose] public section

namespace Algolean.Problems.TMSAT

open Algorithms Algorithms.Alphabet Cslib.Turing

variable {f : List TapeSymbol → List TapeSymbol}

/--
This instance uses the compiled query verifier and its affine transition bound. The certificate
length stays fixed, and the time bound uses the length of the full input-certificate word.
-/
noncomputable def Instance.ofQueryVerifier (computer : TMQuery.TimeComputable f)
    (input : List Bool) (certificateLength : ℕ) : Instance := by
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  let C := TMQuery.Compiler.transitionFactor computer.program
  exact {
    verifier := TMQuery.Compiler.compile computer.program
    input := input
    certificateLength := certificateLength
    time := C * computer.timeBound (input.length + certificateLength + 1) + C }

/--
Compiling the query verifier preserves exactly which certificates make its output start with
a true bit. The specified certificate length is unchanged, and the transition bound is sufficient
for every certificate of that length.
-/
theorem mem_satisfiable_ofQueryVerifier_iff (computer : TMQuery.TimeComputable f)
    (input : List Bool) (certificateLength : ℕ) :
    Instance.ofQueryVerifier computer input certificateLength ∈ satisfiable ↔
      ∃ certificate : List Bool, certificate.length = certificateLength ∧
        (f ((wordPair Bool).encode (input, certificate))).head? = some (.inl true) := by
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  have hcertificate (certificate : List Bool) (hlen : certificate.length = certificateLength) :
      AcceptsWithin (Instance.ofQueryVerifier computer input certificateLength).verifier
          ((wordPair Bool).encode (input, certificate))
          (Instance.ofQueryVerifier computer input certificateLength).time ↔
        (f ((wordPair Bool).encode (input, certificate))).head? = some (.inl true) := by
    apply acceptsWithin_iff_of_outputsWithinTime
    have hlength : ((wordPair Bool).encode (input, certificate)).length =
        input.length + certificateLength + 1 := by simp [hlen, Nat.add_assoc]
    simpa only [Instance.ofQueryVerifier, hlength] using
      TMQuery.Compiler.time_bound computer.program
        (computer.outputsFunInTime ((wordPair Bool).encode (input, certificate)))
  change (∃ certificate : List Bool, certificate.length = certificateLength ∧ _) ↔ _
  exact exists_congr fun certificate => and_congr_right fun hlen => hcertificate certificate hlen

/--
Encoding the compiled instance gives a word in the TMSAT language exactly when a certificate
of the specified length makes the query verifier produce an output starting with a true bit.
-/
theorem encode_ofQueryVerifier_mem_language_iff (computer : TMQuery.TimeComputable f)
    (input : List Bool) (certificateLength : ℕ) :
    encoding.encode (Instance.ofQueryVerifier computer input certificateLength) ∈ language ↔
      ∃ certificate : List Bool, certificate.length = certificateLength ∧
        (f ((wordPair Bool).encode (input, certificate))).head? = some (.inl true) := by
  rw [encode_mem_language]
  exact mem_satisfiable_ofQueryVerifier_iff computer input certificateLength

end Algolean.Problems.TMSAT
