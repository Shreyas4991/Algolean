/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Verification
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

/-!
# SAT belongs to NP

* `Verifier.language_mem_P` proves that the SAT certificate checker recognizes a language in `P`.
  One fixed Turing machine checks the complete input, including incorrectly written words.
* `language_mem_NP` proves that the language of encoded satisfiable formulas belongs to `NP`.
  Every yes instance has an accepted certificate no longer than the encoded formula, so the
  certificate-length polynomial is `X`.

The verifier receives the formula word and certificate word with the separator required by `NP`.
Its query program takes at most `27 * (n + 1) ^ 4` head moves on a combined input of length `n`.
The existing compiler also supplies a transition-table machine with a polynomial transition bound.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

/--
This language contains the correctly encoded formula-certificate pairs whose listed values make
all clauses true. Incorrectly written words are excluded. Missing values mean false, and a
repeated variable uses its first listed value.
-/
def language : Language Symbol := {word | result word = true}

/--
The SAT certificate checker recognizes this language in polynomial time. Its fixed program
returns the one-symbol word containing true exactly on the words in the language, and returns
false on every other word.
-/
theorem language_mem_P : language ∈ P := by
  refine ⟨(fun word => [digit (result word)]), [digit true], ⟨computer⟩, ?_⟩
  intro word
  simp [language, digit]

end Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

namespace Algolean.Problems.SAT

open Algorithms Polynomial SingleTapeTuringMachines.SAT

/--
The language of encoded satisfiable formulas belongs to NP. A satisfiable formula has a certificate
whose encoding is no longer than its own, and the fixed polynomial-time verifier accepts exactly
when the certificate's values satisfy the formula. Incorrectly encoded formulas have no accepted
certificate.
-/
theorem language_mem_NP : language ∈ NP := by
  refine ⟨Verifier.language, X, Verifier.language_mem_P, ?_⟩
  intro word
  simpa only [Verifier.language, Set.mem_ofPred_eq, Verifier.result_wordPair, eval_X] using
      certificate_characterization word

end Algolean.Problems.SAT
