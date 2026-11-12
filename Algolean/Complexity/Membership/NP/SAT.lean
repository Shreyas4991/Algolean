/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier
public import Algolean.Complexity.Classes.NP
public import Algolean.Problems.SingleTapeTM.SAT.Verification

/-!
# SAT belongs to NP

* `CNF.satisfiable` is the set of formulas whose clauses are all true under some assignment.
* `encoding` writes these formulas as words with binary variable names. The SAT language is
  named `SAT`; it contains exactly the encodings of satisfiable formulas.
* `SAT_mem_NP` states `SAT ∈ NP`.
  Incorrectly written formula words have no accepted certificate.
* `Verifier.acceptedPairs_mem_P` proves that one fixed polynomial-time Turing machine checks the
  formula-certificate pairs. Every satisfiable formula has an accepted certificate no longer than
  its encoding, so the certificate-length polynomial is `X`.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

/--
The SAT certificate checker recognizes this language in polynomial time. Its fixed program
returns the one-symbol word containing true exactly on the words in the language, and returns
false on every other word.
-/
theorem acceptedPairs_mem_P : acceptedPairs ∈ P := by
  refine ⟨(fun word => [digit (result word)]), [digit true], ⟨computer⟩, ?_⟩
  intro word
  simp [acceptedPairs, digit]

end Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

namespace Algolean.Problems

open Algorithms Polynomial SingleTapeTuringMachines.SAT

/--
The language of encoded satisfiable formulas belongs to NP. A satisfiable formula has a certificate
whose encoding is no longer than its own, and the fixed polynomial-time verifier accepts exactly
when the certificate's values satisfy the formula. Incorrectly encoded formulas have no accepted
certificate.
-/
theorem SAT_mem_NP : SAT ∈ NP := by
  refine ⟨Verifier.acceptedPairs, X, Verifier.acceptedPairs_mem_P, ?_⟩
  intro word
  simpa only [Verifier.acceptedPairs, Set.mem_ofPred_eq,
    Verifier.result_wordPair, eval_X] using
      SAT.certificate_characterization word

end Algolean.Problems
