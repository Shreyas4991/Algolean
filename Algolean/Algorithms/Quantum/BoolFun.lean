/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fintype.Pi

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# Boolean functions on quantum registers

Counting facts about Boolean functions on bitstrings for Deutsch–Jozsa.

## Main definitions

- `markedCount f`: the number of inputs with `f x = true`.
- `IsConstant f`, `IsBalanced f`: the Deutsch–Jozsa promise.

## Main results

- `isBalanced_iff`: balance is equivalent to `2 * markedCount f = 2 ^ n`.
- `not_isConstant_and_isBalanced`: the two promises are disjoint.
-/

@[expose] public section

namespace Algolean.Algorithms

/-- The number of marked inputs, those `x` with `f x = true`. -/
def markedCount {n : ℕ} (f : (Fin n → Fin 2) → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- `f` takes the same value on every input. -/
def IsConstant {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Prop :=
  ∃ b : Bool, ∀ x, f x = b

/-- `f` is `true` on exactly as many inputs as it is `false` on. -/
def IsBalanced {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Prop :=
  (Finset.univ.filter fun x : Fin n → Fin 2 => f x).card =
    (Finset.univ.filter fun x : Fin n → Fin 2 => ¬ f x).card

/-- Constancy of `f` is decidable: it quantifies over the two values of `Bool` and the finitely
many inputs. -/
instance {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Decidable (IsConstant f) :=
  inferInstanceAs (Decidable (∃ b : Bool, ∀ x, f x = b))

/-- Balance of `f` is decidable by comparing the two finite counts. -/
instance {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Decidable (IsBalanced f) :=
  inferInstanceAs (Decidable
    ((Finset.univ.filter fun x : Fin n → Fin 2 => f x).card =
      (Finset.univ.filter fun x : Fin n → Fin 2 => ¬ f x).card))

/-- A Boolean function is balanced exactly when twice its marked count is the register size. -/
theorem isBalanced_iff {n : ℕ} {f : (Fin n → Fin 2) → Bool} :
    IsBalanced f ↔ 2 * markedCount f = 2 ^ n := by
  have h := Finset.card_filter_add_card_filter_not
    (p := fun x : Fin n → Fin 2 => f x = true) (s := Finset.univ)
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h
  unfold IsBalanced markedCount
  omega

/-- Summing `a` over the marked inputs and `b` over the unmarked ones gives `t·a + (2^n − t)·b`. -/
theorem sum_ite_marked {R : Type*} [CommRing R] {n : ℕ}
    (f : (Fin n → Fin 2) → Bool) (a b : R) :
    (∑ x, if f x then a else b) =
      (markedCount f : R) * a + ((2 ^ n : R) - markedCount f) * b := by
  have hcard : (markedCount f : R) +
      ((Finset.univ.filter fun x : Fin n → Fin 2 => ¬ f x).card : R) = 2 ^ n := by
    have h := Finset.card_filter_add_card_filter_not
      (p := fun x : Fin n → Fin 2 => f x = true) (s := Finset.univ)
    have hc : Fintype.card (Fin n → Fin 2) = 2 ^ n := by simp
    rw [Finset.card_univ, hc] at h
    simpa only [markedCount, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun m : ℕ => (m : R)) h
  simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  rw [← markedCount]
  rw [show ((Finset.univ.filter fun x : Fin n → Fin 2 => ¬ f x).card : R) =
    2 ^ n - markedCount f by linear_combination hcard]

/-- No function is both constant and balanced. -/
theorem not_isConstant_and_isBalanced {n : ℕ} (f : (Fin n → Fin 2) → Bool) :
    ¬ (IsConstant f ∧ IsBalanced f) := by
  rintro ⟨⟨b, hb⟩, h⟩
  have hpos : (0 : ℕ) < 2 ^ n := pow_pos (by decide) n
  cases b <;> simp [IsBalanced, hb, hpos.ne] at h

end Algolean.Algorithms
