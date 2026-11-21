/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Models.SingleTapeTM.Alphabet.Encoding

/-!
# Constructible single-tape resource bounds

A resource bound is computed from the unary input `List.replicate n true`. One fixed program
must produce the existing binary encoding of `bound n` for every `n`. The output is clean and
the head finishes at its first cell, as in `TimeComputable`. No behavior is required on words
containing `false`.

`TimeConstructible bound` requires affine `bound(n)` time. `SpaceConstructible bound` requires
affine `bound(n)` total space and termination, with no time restriction. Both are restricted
to bounds satisfying `n ≤ bound(n)`. Space includes the unary input and every cell reached.

These are computational constructibility predicates: they require computing the binary value.
They do not assert an exact running time or an exact number of allocated cells.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing

/--
A bound at least `n` whose binary value is computed from `List.replicate n true` in affine
`bound(n)` time by one fixed program. Only unary inputs are constrained.
-/
def TimeConstructible (bound : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ bound n) ∧
    ∃ (tm : SingleTapeTM Bool) (_stateDecidableEq : DecidableEq tm.State)
      (program : Prog (TMQuery tm) Unit) (C : ℕ), ∀ n,
      TMQuery.OutputsWithinTime program (List.replicate n true)
        (Computability.encodingNatBool.encode (bound n)) (C * bound n + C)

/--
A bound at least `n` whose binary value is computed from `List.replicate n true` in affine
`bound(n)` total space by one fixed program. It must terminate on every unary input, without
a prescribed time bound. Only unary inputs are constrained.
-/
def SpaceConstructible (bound : ℕ → ℕ) : Prop :=
  (∀ n, n ≤ bound n) ∧
    ∃ (tm : SingleTapeTM Bool) (_stateDecidableEq : DecidableEq tm.State)
      (program : Prog (TMQuery tm) Unit) (C : ℕ), ∀ n,
      ∃ cost final, TMQuery.Completes program (TMState.init tm (List.replicate n true))
        cost final ∧
        final.config.BiTape = BiTape.mk₁ (Computability.encodingNatBool.encode (bound n)) ∧
        final.spaceUsed ≤ C * bound n + C

/-- Time constructibility supplies space constructibility with the same asymptotic bound. -/
theorem TimeConstructible.spaceConstructible {bound : ℕ → ℕ} (h : TimeConstructible bound) :
    SpaceConstructible bound := by
  refine ⟨h.1, ?_⟩
  obtain ⟨tm, stateDecidableEq, program, C, hbound⟩ := h.2
  let := stateDecidableEq
  refine ⟨tm, stateDecidableEq, program, C + 1, ?_⟩
  intro n
  obtain ⟨cost, final, hc, ho, ht⟩ := TMQuery.OutputsWithinTime.iff_completes.mp (hbound n)
  refine ⟨cost, final, hc, ho, ?_⟩
  change final.cellsAllocated.card ≤ _
  rw [hc.space_eq]
  change (TMState.init tm (List.replicate n true)).spaceUsed + cost.cellsAllocated ≤ _
  rw [TMState.spaceUsed_init, List.length_replicate]
  have hspace := hc.space_le_time.trans ht
  have : max 1 n ≤ bound n + 1 :=
    max_le (Nat.succ_le_succ (Nat.zero_le _)) ((h.1 n).trans (Nat.le_succ _))
  simp only [Nat.add_mul, Nat.one_mul]
  lia

end Algolean.Algorithms
