/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Problems.Basic

/-!
# Deterministic single-tape time classes

`DTIME time` consists of languages decided in time `C * time(n) + C` by one fixed program,
for some constant `C`. Time counts Query move instructions, including stationary moves.
The existing compiler translates these to transition-table machines with affine overhead.

The input and tape use the same fixed finite alphabet. The output must be a clean word,
equal to a fixed acceptance word exactly on members of the language. This is the convention
already used by `P`, `TMSolves`, and `TMQuery.DecidesWithin`.
-/

@[expose] public section

namespace Algolean.Algorithms

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Languages decided by a fixed deterministic single-tape program in affine `time(n)`. -/
def DTIME [_symbols : Nontrivial Symbol] (time : ℕ → ℕ) : Set (Language Symbol) :=
  {L | ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    TMQuery.TimeComputableIn f time ∧ ∀ input, f input = yes ↔ input ∈ L}

/-- Increasing the time bound enlarges the class. -/
theorem DTIME.mono [Nontrivial Symbol] {time time' : ℕ → ℕ} (hle : ∀ n, time n ≤ time' n) :
    DTIME (Symbol := Symbol) time ⊆ DTIME time' := by
  rintro _ ⟨f, yes, hcomputer, hcorrect⟩
  exact ⟨f, yes, hcomputer.mono hle, hcorrect⟩

end Algolean.Algorithms
