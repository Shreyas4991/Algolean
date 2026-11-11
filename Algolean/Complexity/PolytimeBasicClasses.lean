/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Problems.Basic

/-!
# The language classes P and NP

`P` contains the languages decided by one fixed Query program in polynomial time. The program
computes a word-valued function and produces a chosen acceptance word exactly on yes inputs.
`NP` contains languages whose yes answers have polynomially bounded certificates checked by a
language in `P`.

Both classes require at least two ordinary symbols. Certificates use the input alphabet, and
the verifier reads the input and certificate separated by one added symbol. Its running time
is measured in that complete word's length. The machine execution and function computation
records are defined in `Models/SingleTapeTM/Computability`, independently of these classes.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A problem belongs to this class when one fixed program computes a function in polynomial time
and produces a chosen acceptance word exactly on inputs whose answer is yes. Polynomial time is
specified by [PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable).
The alphabet must contain at least two distinct symbols.
-/
def P [_symbols : Nontrivial Symbol] : Set (Language Symbol) :=
  {L | ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    Nonempty (TMQuery.PolyTimeComputable f) ∧ ∀ x, f x = yes ↔ x ∈ L}

/--
A language belongs to `NP` when a language in `P` checks encoded input-certificate pairs and a
polynomial in the original input length bounds the certificate length. The pair encoding uses
`Alphabet.Extended Symbol 1` and preserves the boundary with a dedicated separator, while the
original language and certificates remain over `Symbol`.
The alphabet must contain at least two distinct symbols so that a certificate can carry
information through its symbols as well as its length.

The verifier receives `(Alphabet.wordPair Symbol).encode (input, certificate)`. Its polynomial
runtime is measured in that encoded word's length, which is the two word lengths plus one.
The proof that every language in `P` belongs to `NP` is in `Algolean.Complexity.NP`.
-/
def NP [_symbols : Nontrivial Symbol] : Set (Language Symbol) :=
  {L | ∃ (A : Language (Alphabet.Extended Symbol 1)) (q : Polynomial ℕ), A ∈ P ∧
    ∀ input, input ∈ L ↔ ∃ certificate : List Symbol,
      certificate.length ≤ q.eval input.length ∧
        (Alphabet.wordPair Symbol).encode (input, certificate) ∈ A}

end Algorithms

end Algolean
