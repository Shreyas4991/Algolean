/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.ModelM
public import Mathlib.Probability.Distributions.Uniform

/-!
# Expected query costs

Nonnegative expectations over `PMF` and their sequencing rule for `Prog.expectedCost`.
The proof uses the joint `Prog.runM` semantics to preserve the dependence between results and costs.
Expectations take values in `ℝ≥0∞`, so the rules do not require finiteness assumptions.
-/

@[expose] public section

open scoped ENNReal

namespace PMF

universe u

variable {α β : Type u}

/-- The nonnegative expectation of `f` under `p`. -/
noncomputable def expectation (p : PMF α) (f : α → ℝ≥0∞) : ℝ≥0∞ := ∑' a, p a * f a

@[simp] theorem expectation_pure (a : α) (f : α → ℝ≥0∞) :
    expectation (Pure.pure a) f = f a := by
  classical
  change expectation (PMF.pure a) f = f a
  simp [expectation, pure_apply]

/-- Expectation after sampling in sequence. -/
theorem expectation_bind (p : PMF α) (g : α → PMF β) (f : β → ℝ≥0∞) :
    expectation (p >>= g) f = expectation p (fun a => expectation (g a) f) := by
  change expectation (p.bind g) f = expectation p (fun a => expectation (g a) f)
  simp only [expectation, bind_apply, ENNReal.tsum_mul_right.symm,
    ENNReal.tsum_mul_left.symm, mul_assoc]
  exact ENNReal.tsum_comm

@[simp] theorem expectation_map (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    expectation (g <$> p) f = expectation p (fun a => f (g a)) := by
  have h : g <$> p = p >>= fun a => Pure.pure (g a) := rfl
  rw [h, expectation_bind]
  simp

@[simp] theorem expectation_const (p : PMF α) (c : ℝ≥0∞) :
    expectation p (fun _ => c) = c := by
  simp [expectation, ENNReal.tsum_mul_right]

/-- Nonnegative expectation is additive, even for infinite expectations. -/
theorem expectation_add (p : PMF α) (f g : α → ℝ≥0∞) :
    expectation p (fun a => f a + g a) = expectation p f + expectation p g := by
  simp [expectation, mul_add, ENNReal.tsum_add]

/-- Pointwise bounds on the support give bounds on expectations. -/
theorem expectation_mono (p : PMF α) {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ p.support, f a ≤ g a) : expectation p f ≤ expectation p g := by
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_right (h a ha) _

/-- Uniform finite expectation is an arithmetic mean. -/
theorem expectation_uniformOfFintype [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    expectation (uniformOfFintype α) f = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a := by
  simp [expectation, uniformOfFintype_apply, tsum_fintype, Finset.mul_sum]

end PMF

namespace Algolean.Algorithms.Prog

open Cslib

variable {Q : Type → Type} {α β : Type}

/-- Expected accumulated query cost under a probabilistic model. -/
noncomputable def expectedCost (P : Prog Q α) (M : ModelM Q PMF ℕ) : ℝ≥0∞ :=
  (P.costM M).expectation fun n => n

@[simp] theorem expectedCost_pure (a : α) (M : ModelM Q PMF ℕ) :
    expectedCost (pure a) M = 0 := by simp [expectedCost]

/-- Expected cost is the expectation of the cost projection of the joint semantics. -/
theorem expectedCost_eq_runM (P : Prog Q α) (M : ModelM Q PMF ℕ) :
    expectedCost P M = (P.runM M).run.expectation fun a => a.tell := by
  simp [expectedCost, costM, AddWriterT.cost]

/-- Sequencing adds the initial expected cost and the expected continuation cost. -/
theorem expectedCost_bind (P : Prog Q α) (f : α → Prog Q β) (M : ModelM Q PMF ℕ) :
    expectedCost (P >>= f) M = expectedCost P M +
      (P.evalM M).expectation (fun a => expectedCost (f a) M) := by
  simp only [expectedCost_eq_runM, runM_bind, AddWriterT.run_bind, PMF.expectation_bind,
    PMF.expectation_pure, Nat.cast_add, PMF.expectation_add, PMF.expectation_const]
  rw [← runM_value]
  simp [AddWriterT.value]

@[simp] theorem expectedCost_map (g : α → β) (P : Prog Q α) (M : ModelM Q PMF ℕ) :
    expectedCost (g <$> P) M = expectedCost P M := by simp [expectedCost]

end Algolean.Algorithms.Prog
