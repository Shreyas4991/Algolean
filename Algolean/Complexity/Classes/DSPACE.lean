/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Classes.DTIME

/-!
# Deterministic single-tape space classes

`DSPACE space` consists of languages decided by one fixed terminating program using at most
`C * space(n) + C` total tape cells, for some constant `C`. There is no running-time restriction.
The input and tape use the same finite alphabet and the output convention is that of `DTIME`.

Space includes every input cell, the initial head cell, and every cell reached during the run.
Erasing cells does not recover space. Consequently these classes use total space on an
input-bearing tape, rather than the work-space convention with a separate read-only input tape.
-/

@[expose] public section

namespace Algolean.Algorithms

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Languages decided by a terminating deterministic single-tape program in affine total space. -/
def DSPACE [_symbols : Nontrivial Symbol] (space : ℕ → ℕ) : Set (Language Symbol) :=
  {L | ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    TMQuery.SpaceComputableIn f space ∧ ∀ input, f input = yes ↔ input ∈ L}

/-- A program that fits within a space bound also fits within any larger bound. -/
theorem DSPACE.mono [Nontrivial Symbol] {space space' : ℕ → ℕ} (hle : ∀ n, space n ≤ space' n) :
    DSPACE (Symbol := Symbol) space ⊆ DSPACE space' := by
  rintro _ ⟨f, yes, hcomputer, hcorrect⟩
  exact ⟨f, yes, hcomputer.mono hle, hcorrect⟩

/-- Time bounds total space after including the cells occupied by the initial input. -/
theorem DTIME_subset_DSPACE [Nontrivial Symbol] (time : ℕ → ℕ) :
    DTIME (Symbol := Symbol) time ⊆ DSPACE (fun n => max 1 n + time n) := by
  rintro _ ⟨f, yes, hcomputer, hcorrect⟩
  exact ⟨f, yes, hcomputer.spaceComputableIn, hcorrect⟩

end Algolean.Algorithms
