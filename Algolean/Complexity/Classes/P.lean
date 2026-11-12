/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Problems.Basic

/-!
# Polynomial-time decision problems

* `P` contains the languages decided by one fixed Query program in polynomial time.
  The program produces a chosen word exactly when the input belongs to the language.

The tape alphabet is finite and contains at least two distinct symbols. The computation
records use CSLib's output convention: only the output word remains on the tape, starting at
the original input position, where the head also finishes.
-/

@[expose] public section

namespace Algolean.Algorithms

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

end Algolean.Algorithms
