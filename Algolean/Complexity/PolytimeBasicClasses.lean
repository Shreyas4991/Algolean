/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

/-!
# Basic Complexity Classes on Single Tape Turing Machines

We define basic complexity classes `P` and `NP` on single tape Turing
machines represented by `SingleTapeTM`.
-/

namespace Algolean

namespace Algorithms

open Turing SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A language over alphabet `Symbol`. -/
abbrev Language (Symbol : Type) := List Symbol → Prop

/-- A language `L` is in `P` if there is a polynomial-time computable
function `f : List Symbol → List Symbol` and a fixed accept string
`yes` such that `f x = yes` holds exactly when `L x` holds. -/
def P (L : Language Symbol) : Prop :=
  ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    Nonempty (PolyTimeComputable f) ∧ ∀ x, f x = yes ↔ L x

/-- A language `L` is in `NP` if there is a polynomial-time computable
verifier `V : List Symbol → List Symbol`, a fixed accept string `yes`,
and a polynomial certificate-length bound `q` such that `L x` iff some
certificate `c` of length at most `q(|x|)` makes `V (x ++ c) = yes`.
The verifier receives input and certificate concatenated on a single
tape; the boundary is handled per-language by the verifier. -/
def NP (L : Language Symbol) : Prop :=
  ∃ (V : List Symbol → List Symbol) (yes : List Symbol) (q : Polynomial ℕ),
    Nonempty (PolyTimeComputable V) ∧
    ∀ x, L x ↔ ∃ c : List Symbol,
      c.length ≤ q.eval x.length ∧ V (x ++ c) = yes

/-- `P ⊆ NP`: every language in `P` is in `NP` with the empty certificate. -/
theorem NP.ofP {L : Language Symbol} (hP : P L) : NP L := by
  obtain ⟨f, yes, hPTC, hEq⟩ := hP
  refine ⟨f, yes, 0, hPTC, ?_⟩
  intro x
  refine ⟨fun hL => ⟨[], by simp, ?_⟩, ?_⟩
  · simpa using (hEq x).mpr hL
  · rintro ⟨c, hlen, hV⟩
    have hc : c = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (by simpa using hlen))
    subst hc
    exact (hEq x).mp (by simpa using hV)

end Algorithms

end Algolean
