/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Basic
public import Cslib.Computability.Machines.SingleTapeTuring.Basic
public import Algolean.Models.SingleTapeTM

@[expose] public section

/-!
# Basic Complexity Classes on Single Tape Turing Machines

We define basic complexity classes `P`, `NP`, `NP-Hard` and `NP-Complete`
on single tape Turing machines represented by `SingleTapeTM`

--
## Definitions

- `Dir` : A type for directions in which a TM can move.
-/

namespace Algolean

namespace Algorithms

open Cslib Prog Turing

/-! ## Complexity Classes -/

open SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A language over alphabet `Symbol`. -/
abbrev Language (Symbol : Type) := List Symbol → Prop

/-- The decision problem for language `L` on input `x`, viewed as a
`QueryProblem` over `TMQuery tm`. The spec ignores the model
(there is only one meaningful model per TM). -/
def TMDecisionProblem (L : Language Symbol) (x : List Symbol)
    (tm : SingleTapeTM Symbol) : QueryProblem (TMQuery tm) TMCost Bool where
  spec _ b := (b = true ↔ L x)

/-- A language is in P if there exists a TM, a uniform family of
programs, and a polynomial such that each program correctly decides
`L` on input `x` within `p(|x|)` steps under `TMModel tm`. -/
def P (L : Language Symbol) : Prop :=
  ∃ (tm : SingleTapeTM Symbol)
    (prog : List Symbol → Prog (TMQuery tm) Bool)
    (p : Polynomial ℕ),
    ∀ x, ((prog x).eval (TMModel tm) = true ↔ L x) ∧
      ((prog x).time (TMModel tm)).steps ≤ p.eval x.length

/-- A language is in NP if there exists a TM, a uniform verifier
taking input and certificate separately, and polynomials `p` (time
bound) and `q` (certificate bound) such that: the verifier runs in
poly time on all valid-length certificates, and `L x` iff there
exists a short certificate that the verifier accepts. -/
def NP (L : Language Symbol) : Prop :=
  ∃ (tm : SingleTapeTM Symbol)
    (V : List Symbol → List Symbol → Prog (TMQuery tm) Bool)
    (p q : Polynomial ℕ),
    (∀ x c, c.length ≤ q.eval x.length →
      ((V x c).time (TMModel tm)).steps ≤ p.eval x.length) ∧
    ∀ x, L x ↔ ∃ c : List Symbol, c.length ≤ q.eval x.length ∧
      (V x c).eval (TMModel tm) = true



/-- P is closed under composition via bind. If `P₁` runs within
`p₁(|x|)` steps and `P₂` runs within `p₂(|x|)` steps on the
result of `P₁`, then `P₁ >>= P₂` runs within
`(p₁ + p₂)(|x|)` steps. -/
theorem P.bind
    {tm : SingleTapeTM Symbol}
    {P₁ : List Symbol → Prog (TMQuery tm) α}
    {P₂ : α → List Symbol → Prog (TMQuery tm) β}
    {spec₁ : List Symbol → α → Prop}
    {spec₂ : α → List Symbol → β → Prop}
    {p₁ p₂ : Polynomial ℕ}
    (h₁ : ∀ x, spec₁ x ((P₁ x).eval (TMModel tm)) ∧
      ((P₁ x).time (TMModel tm)).steps ≤ p₁.eval x.length)
    (h₂ : ∀ x a, spec₁ x a →
      spec₂ a x ((P₂ a x).eval (TMModel tm)) ∧
        ((P₂ a x).time (TMModel tm)).steps ≤ p₂.eval x.length) :
    ∀ x, spec₂ ((P₁ x).eval (TMModel tm)) x
        (Prog.eval ((P₁ x).bind (P₂ · x)) (TMModel tm)) ∧
      (Prog.time ((P₁ x).bind (P₂ · x)) (TMModel tm)).steps
        ≤ (p₁ + p₂).eval x.length := by
  intro x
  obtain ⟨hspec₁, htime₁⟩ := h₁ x
  obtain ⟨hspec₂, htime₂⟩ := h₂ x _ hspec₁
  simp only [Prog.eval_bind, Prog.time_bind, eval_add]
  exact ⟨hspec₂, Nat.add_le_add htime₁ htime₂⟩

/-- P ⊆ NP: every language in P is in NP (with trivial certificates).
The verifier ignores the certificate and runs the decider. -/
theorem NP.ofP {L : Language Symbol} (hP : P L) : NP L := by
  obtain ⟨tm, P, p, hP⟩ := hP
  refine ⟨tm, fun x _ => P x, p, 0, ?_, ?_⟩
  · intro x _ _
    exact (hP x).2
  · intro x
    constructor
    · intro hLx
      exact ⟨[], by simp, (hP x).1.mpr hLx⟩
    · intro ⟨_, _, hVc⟩
      exact (hP x).1.mp hVc

end Algorithms

end Algolean
