/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

import Mathlib.Data.Matrix.Reflection
public import Mathlib.Data.Matrix.Block

variable {n : ℕ} {R : Type}

def Matrix.toPreBlockForm (M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R) :
    Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) R :=
  .of fun i j =>
    match i, j with
    | .inl i, .inl j => M ⟨i.1, by lia⟩ ⟨j.1, by lia⟩
    | .inl i, .inr j => M ⟨i.1, by lia⟩ ⟨j.1 + 2 ^ n, by lia⟩
    | .inr i, .inl j => M ⟨i.1 + 2 ^ n, by lia⟩ ⟨j.1, by lia⟩
    | .inr i, .inr j => M ⟨i.1 + 2 ^ n, by lia⟩ ⟨j.1 + 2 ^ n, by lia⟩

@[simp, grind =]
lemma Matrix.toPreBlockForm_inl_inr {M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R}
  {i j : Fin (2 ^ n)} :
    M.toPreBlockForm (.inl i) (.inr j) = M ⟨i.1, by lia⟩ ⟨j.1 + 2 ^ n, by lia⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inr_inl {M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R}
  {i j : Fin (2 ^ n)} :
    M.toPreBlockForm (.inr i) (.inl j) = M ⟨i.1 + 2 ^ n, by lia⟩ ⟨j.1, by lia⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inr_inr {M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R}
  {i j : Fin (2 ^ n)} :
    M.toPreBlockForm (.inr i) (.inr j) = M ⟨i.1 + 2 ^ n, by lia⟩ ⟨j.1 + 2 ^ n, by lia⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inl_inl {M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R}
  {i j : Fin (2 ^ n)} :
    M.toPreBlockForm (.inl i) (.inl j) = M ⟨i.1, by lia⟩ ⟨j.1, by lia⟩ := by rfl

def Matrix.ofPostBlockForm (M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) R) :
    Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R :=
  .of fun i j =>
    if hi : i.1 < 2^n
    then
      if hj : j.1 < 2^n
      then M (.inl ⟨i.1, hi⟩) (.inl ⟨j.1, hj⟩)
      else M (.inl ⟨i.1, hi⟩) (.inr ⟨j.1 - 2^n, by lia⟩)
    else
      if hj : j.1 < 2^n
      then M (.inr ⟨i.1 - 2^n, by lia⟩) (.inl ⟨j.1, hj⟩)
      else M (.inr ⟨i.1 - 2^n, by lia⟩) (.inr ⟨j.1 - 2^n, by lia⟩)

lemma Matrix.transformationHelper1
  {M : Matrix (Fin (2 ^ n) ⊕ Fin (2 ^ n)) (Fin (2 ^ n) ⊕ Fin (2 ^ n)) R}
  {N : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R} :
    M.ofPostBlockForm = N ↔ M = N.toPreBlockForm := by
  simp only [Nat.succ_eq_add_one, ofPostBlockForm, toPreBlockForm]
  constructor
  · intro h
    simp [← h, ← ext_iff]
  · intro h
    simp [h, ← ext_iff]
    grind

lemma sum_helper (f : Fin (2 ^ (n + 1)) → R) [Ring R] :
    ∑ (x : Fin (2 ^ n)), f ⟨x.1, by lia⟩ + ∑ (x : Fin (2 ^ n)), f ⟨x.1 + 2 ^ n, by lia⟩
      = ∑ x, f x:= by
  let e₁ : Function.Embedding (Fin (2 ^ n)) (Fin (2 ^ (n + 1))) := {
    toFun := fun x => ⟨x.1, by lia⟩
    inj' := by simp [Function.Injective, Fin.val_inj]
  }
  let e₂ : Function.Embedding (Fin (2 ^ n)) (Fin (2 ^ (n + 1))) := {
    toFun := fun x => ⟨x.1 + 2 ^ n, by lia⟩
    inj' := by simp [Function.Injective, Fin.val_inj]
  }
  have : Finset.univ (α := Fin (2 ^ (n + 1))) = (Finset.univ (α := Fin (2 ^ n))).map e₁
    ∪ (Finset.univ (α := Fin (2 ^ n))).map e₂ := by
    simp only [Finset.ext_iff, Finset.mem_univ, Finset.mem_union, Finset.mem_map, true_and,
      true_iff]
    intro x
    by_cases h : x.1 < 2 ^ n
    · left
      use ⟨x.1, h⟩
      simp [e₁, ← Function.Embedding.toFun_eq_coe]
    · right
      use ⟨x.1 - 2 ^ n , by lia⟩
      simp [e₂, ← Function.Embedding.toFun_eq_coe]
      grind
  have dist : Disjoint (Finset.map e₁ Finset.univ) (Finset.map e₂ Finset.univ) := by
    simp [Finset.disjoint_iff_ne, e₁, e₂, ← Function.Embedding.toFun_eq_coe]
    lia
  simp [this, Finset.sum_union dist, e₁, e₂, ← Function.Embedding.toFun_eq_coe]


lemma Matrix.toPreBlockForm_mul [Ring R] {A B : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R} :
    (A * B).toPreBlockForm = A.toPreBlockForm * B.toPreBlockForm := by
  simp only [Nat.succ_eq_add_one, ← ext_iff, mul_apply, Fintype.sum_sum_type, Sum.forall,
    toPreBlockForm_inl_inl, toPreBlockForm_inr_inl, toPreBlockForm_inl_inr, toPreBlockForm_inr_inr,
    ← forall_and]
  intro i j
  simp [sum_helper (f := fun k => A ⟨i, by lia⟩ k * B k ⟨j, by lia⟩),
    sum_helper (f := fun k => A ⟨i + 2 ^ n, by lia⟩ k * B k ⟨j, by lia⟩),
    sum_helper (f := fun k => A ⟨i, by lia⟩ k * B k ⟨j + 2 ^ n, by lia⟩),
    sum_helper (f := fun k => A ⟨i + 2 ^ n, by lia⟩ k * B k ⟨j + 2 ^ n, by lia⟩)
  ]

def StrassenHelper {n : ℕ} {R : Type} [Ring R]
  (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) (B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  match n with
  | .zero =>
    let r := A 0 0 * B 0 0
    .of fun _ _ => r
  | .succ _ =>
    let A := A.toPreBlockForm
    let B := B.toPreBlockForm
    -- block matrices
    let A₁₁ := A.toBlocks₁₁
    let A₁₂ := A.toBlocks₁₂
    let A₂₁ := A.toBlocks₂₁
    let A₂₂ := A.toBlocks₂₂
    let B₁₁ := B.toBlocks₁₁
    let B₁₂ := B.toBlocks₁₂
    let B₂₁ := B.toBlocks₂₁
    let B₂₂ := B.toBlocks₂₂
    -- intermediate results
    let M₁ := StrassenHelper (A₁₁ + A₂₂) (B₁₁ + B₂₂)
    let M₂ := StrassenHelper (A₂₁ + A₂₂) B₁₁
    let M₃ := StrassenHelper A₁₁ (B₁₂ - B₂₂)
    let M₄ := StrassenHelper A₂₂ (B₂₁ - B₁₁)
    let M₅ := StrassenHelper (A₁₁ + A₁₂) B₂₂
    let M₆ := StrassenHelper (A₂₁ - A₁₁) (B₁₁ + B₁₂)
    let M₇ := StrassenHelper (A₁₂ - A₂₂) (B₂₁ + B₂₂)
    --final result
    (Matrix.fromBlocks (M₁ + M₄ - M₅ + M₇) (M₃ + M₅) (M₂ + M₄) (M₁ - M₂ + M₃ + M₆)).ofPostBlockForm

lemma StrassenHelper_eq_matrixMul {n : ℕ} {R : Type} [Ring R]
  {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} {B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    StrassenHelper A B = A * B := by
  induction n with
  | zero =>
    simp [StrassenHelper, ← Matrix.ext_iff, Matrix.mul_apply]
  | succ m ih =>
    simp only [StrassenHelper, ih, Matrix.transformationHelper1 (N := A * B),
      Matrix.toPreBlockForm_mul]
    conv =>
      rhs
      rw [← Matrix.fromBlocks_toBlocks (M := A.toPreBlockForm),
        ← Matrix.fromBlocks_toBlocks (M:= B.toPreBlockForm), Matrix.fromBlocks_multiply]
    congr 1
    all_goals grind
