/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

import Mathlib.Data.Matrix.Reflection
public import Mathlib.Data.Matrix.Block
public import Algolean.Models.Arithmetic

lemma Nat.length_digits_le_of_le {x y b : ℕ} (hxy : x ≤ y) (hb : 1 < b) :
    (b.digits x).length ≤ (b.digits y).length := by
  induction y using Nat.strongRec generalizing x with
  | ind y ih =>
    cases x with
    | zero =>
      simp
    | succ x =>
      cases y with
      | zero => simp at hxy
      | succ y =>
        simp only [
          Nat.digits_def' (n := x + 1) hb (by simp), List.length_cons,
          Nat.digits_def' (n := y + 1) hb (by simp), add_le_add_iff_right]
        apply ih
        · exact div_lt_self (by simp) hb
        · exact Nat.div_le_div_right hxy

lemma Nat.div_pow_sub_one {x b : ℕ} (hb : 1 < b) : (b ^ (x + 1) - 1) / b = b ^ x - 1 := by
  cases x with
  | zero =>
    simp [zero_lt_of_lt hb]
  | succ m =>
    rw [Nat.pow_add', Nat.pow_one]
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm _ b, Nat.mul_sub]
      simp
      grind
    · grind

lemma Nat.mod_pow_sub_one {x b : ℕ} (hb : 1 < b) : (b ^ (x + 1) - 1) % b = b - 1 := by
  cases x with
  | zero =>
    simp
  | succ m =>
    rw [Nat.pow_add', Nat.pow_one]
    refine mul_sub_mod ?_
    refine Nat.mul_pos (zero_lt_of_lt hb) ?_
    refine Nat.pow_pos (zero_lt_of_lt hb)

lemma Nat.digits_pow_b_sub_one {x b : ℕ} (hb : 1 < b) :
    (b.digits (b ^ x - 1)) = List.replicate x (b - 1) := by
  induction x with
  | zero =>
    simp
  | succ m ih =>
    rw [Nat.digits_def' hb]
    · simp [List.replicate_succ, ← ih, div_pow_sub_one hb, mod_pow_sub_one hb]
    · simp [hb]

lemma Nat.length_digits_add {x y b : ℕ} (hb : 1 < b) :
    (b.digits (x + y)).length ≤ (max (b.digits x).length (b.digits y).length) + 1 := by
  have hx := le_sub_one_of_lt (lt_base_pow_length_digits (m := x) hb)
  have hy := le_sub_one_of_lt (lt_base_pow_length_digits (m := y) hb)
  have hxy : x + y ≤ b ^ (max (b.digits x).length (b.digits y).length + 1) - 1 := by
    apply Nat.le_trans (add_le_add hx hy)
    apply Nat.le_trans (m := (b ^ (max (b.digits x).length (b.digits y).length) - 1)
      + (b ^ (max (b.digits x).length (b.digits y).length) - 1))
    · refine add_le_add ?_ ?_
      · refine Nat.sub_le_sub_right ?_ 1
        refine Nat.pow_le_pow_right (by grind) (by apply Nat.le_max_left)
      · refine Nat.sub_le_sub_right ?_ 1
        refine Nat.pow_le_pow_right (by grind) (by apply Nat.le_max_right)
    · apply Nat.le_trans (m := b ^ max (b.digits x).length (b.digits y).length
        + (b ^ max (b.digits x).length (b.digits y).length - 1))
      · refine Nat.add_le_add_iff_right.mpr ?_
        exact sub_le (b ^ max (b.digits x).length (b.digits y).length) 1
      · rw [← Nat.add_sub_assoc]
        · apply Nat.sub_le_sub_right
          rw [Nat.pow_add_one, ← Nat.mul_two]
          exact mul_le_mul_left (b ^ max (b.digits x).length (b.digits y).length) hb
        · exact one_le_pow (max (b.digits x).length (b.digits y).length) b (zero_lt_of_lt hb)
  apply Nat.le_trans (length_digits_le_of_le hxy hb)
  simp [digits_pow_b_sub_one hb]

lemma Nat.length_digits_mul {x y b : ℕ} (hb : 1 < b) :
    (b.digits (x * y)).length ≤ 2*(max (b.digits x).length (b.digits y).length) := by
  have hx := le_sub_one_of_lt (lt_base_pow_length_digits (m := x) hb)
  have hy := le_sub_one_of_lt (lt_base_pow_length_digits (m := y) hb)
  have hxy : x * y ≤ b ^ (2 * (max (b.digits x).length (b.digits y).length)) - 1 := by
    apply Nat.le_trans (Nat.mul_le_mul hx hy)
    simp only [Nat.mul_sub, Nat.sub_mul, one_mul, mul_one, Nat.two_mul, Nat.pow_add,
      tsub_le_iff_right]
    apply Nat.le_trans (m := b ^ max (b.digits x).length (b.digits y).length *
      b ^ max (b.digits x).length (b.digits y).length)
    · refine Nat.mul_le_mul ?_ ?_
      · refine Nat.pow_le_pow_right (by grind) (by apply Nat.le_max_left)
      · refine Nat.pow_le_pow_right (by grind) (by apply Nat.le_max_right)
    · grind
  apply Nat.le_trans (length_digits_le_of_le hxy hb)
  simp [digits_pow_b_sub_one hb]

variable {n : ℕ} {R : Type}

abbrev StrassenMatrix (n : ℕ) (R : Type) := Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R

lemma helper_lt1 {i n : ℕ} (h : i < 2 ^ (n - 1)) (h' : 0 < n) : i < 2 ^ n := by
  apply Nat.lt_trans h (Nat.two_pow_pred_lt_two_pow h')

lemma helper_lt2 {i n : ℕ} (h : i < 2 ^ (n - 1)) (h' : 0 < n) : i + 2 ^ (n - 1) < 2 ^ n := by
  apply Nat.lt_of_lt_of_eq (m := 2 ^ (n - 1) + 2 ^ (n - 1))
  · exact Nat.add_lt_add_right h (2 ^ (n - 1))
  · exact Nat.two_pow_pred_add_two_pow_pred h'

def Matrix.toPreBlockForm (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) (h : 0 < n) :
    Matrix (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) R :=
  .of fun i j =>
    match i, j with
    | .inl i, .inl j => M ⟨i.1, helper_lt1 i.2 h⟩ ⟨j.1, helper_lt1 j.2 h⟩
    | .inl i, .inr j => M ⟨i.1, helper_lt1 i.2 h⟩ ⟨j.1 + 2 ^ (n - 1), helper_lt2 j.2 h⟩
    | .inr i, .inl j => M ⟨i.1 + 2 ^ (n - 1), helper_lt2 i.2 h⟩ ⟨j.1, helper_lt1 j.2 h⟩
    | .inr i, .inr j =>
      M ⟨i.1 + 2 ^ (n - 1), helper_lt2 i.2 h⟩ ⟨j.1 + 2 ^ (n - 1), helper_lt2 j.2 h⟩

@[simp, grind =]
lemma Matrix.toPreBlockForm_inl_inr {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R}
  {i j : Fin (2 ^ (n - 1))} (h : 0 < n) :
    (M.toPreBlockForm h) (.inl i) (.inr j) =
      M ⟨i.1, helper_lt1 i.2 h⟩ ⟨j.1 + 2 ^ (n - 1), helper_lt2 j.2 h⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inr_inl {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R}
  {i j : Fin (2 ^ (n - 1))} (h : 0 < n) :
    (M.toPreBlockForm h) (.inr i) (.inl j) =
      M ⟨i.1 + 2 ^ (n - 1), helper_lt2 i.2 h⟩ ⟨j.1, helper_lt1 j.2 h⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inr_inr {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R}
  {i j : Fin (2 ^ (n - 1))} (h : 0 < n) :
    (M.toPreBlockForm h) (.inr i) (.inr j) =
      M ⟨i.1 + 2 ^ (n - 1), helper_lt2 i.2 h⟩ ⟨j.1 + 2 ^ (n - 1), helper_lt2 j.2 h⟩ := by rfl

@[simp, grind =]
lemma Matrix.toPreBlockForm_inl_inl {M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R}
  {i j : Fin (2 ^ (n - 1))} (h : 0 < n) :
    (M.toPreBlockForm h) (.inl i) (.inl j) =
      M ⟨i.1, helper_lt1 i.2 h⟩ ⟨j.1, helper_lt1 j.2 h⟩ := by rfl

lemma helper_lt3 {i : ℕ} (hi₁ : ¬ i < 2 ^ (n - 1)) (hi₂ : i < 2 ^ n) (h : 0 < n) :
    i - 2 ^ (n - 1) < 2 ^ (n - 1) := by
  apply Nat.sub_lt_right_of_lt_add
  · exact Nat.not_lt.mp hi₁
  · rwa [← Nat.two_pow_succ, Nat.sub_one_add_one_eq_of_pos h]

def Matrix.ofPostBlockForm
  (M : Matrix (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) R)
  (h : 0 < n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  .of fun i j =>
    if hi : i.1 < 2 ^ (n - 1)
    then
      if hj : j.1 < 2 ^ (n - 1)
      then M (.inl ⟨i.1, hi⟩) (.inl ⟨j.1, hj⟩)
      else M (.inl ⟨i.1, hi⟩) (.inr ⟨j.1 - 2^(n - 1), helper_lt3 hj j.2 h⟩)
    else
      if hj : j.1 < 2 ^ (n - 1)
      then M (.inr ⟨i.1 - 2^(n - 1), helper_lt3 hi i.2 h⟩) (.inl ⟨j.1, hj⟩)
      else M (.inr ⟨i.1 - 2^(n - 1), helper_lt3 hi i.2 h⟩)
              (.inr ⟨j.1 - 2^(n - 1), helper_lt3 hj j.2 h⟩)

lemma Matrix.transformationHelper1
  {M : Matrix (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) (Fin (2 ^ (n - 1)) ⊕ Fin (2 ^ (n - 1))) R}
  {N : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} (h : 0 < n) :
    (M.ofPostBlockForm h) = N ↔ M = (N.toPreBlockForm h) := by
  simp only [ofPostBlockForm, toPreBlockForm]
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


lemma Matrix.toPreBlockForm_mul [Ring R] {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} (h : 0 < n) :
    (A * B).toPreBlockForm h = (A.toPreBlockForm h) * (B.toPreBlockForm h) := by
  simp only [Nat.succ_eq_add_one, ← ext_iff, mul_apply, Fintype.sum_sum_type, Sum.forall,
    toPreBlockForm_inl_inl, toPreBlockForm_inr_inl, toPreBlockForm_inl_inr, toPreBlockForm_inr_inr,
    ← forall_and]
  intro i j
  simp [sum_helper (f := fun k => A ⟨i, by lia⟩ k * B k ⟨j, by lia⟩),
    sum_helper (f := fun k => A ⟨i + 2 ^ n, by lia⟩ k * B k ⟨j, by lia⟩),
    sum_helper (f := fun k => A ⟨i, by lia⟩ k * B k ⟨j + 2 ^ n, by lia⟩),
    sum_helper (f := fun k => A ⟨i + 2 ^ n, by lia⟩ k * B k ⟨j + 2 ^ n, by lia⟩)
  ]

namespace Algolean.Algorithms

public def Strassen {n : ℕ} {R : Type} [Ring R]
  (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) (B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  if h : 0 < n
  then
    let A := A.toPreBlockForm h
    let B := B.toPreBlockForm h
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
    let M₁ := Strassen (A₁₁ + A₂₂) (B₁₁ + B₂₂)
    let M₂ := Strassen (A₂₁ + A₂₂) B₁₁
    let M₃ := Strassen A₁₁ (B₁₂ - B₂₂)
    let M₄ := Strassen A₂₂ (B₂₁ - B₁₁)
    let M₅ := Strassen (A₁₁ + A₁₂) B₂₂
    let M₆ := Strassen (A₂₁ - A₁₁) (B₁₁ + B₁₂)
    let M₇ := Strassen (A₁₂ - A₂₂) (B₂₁ + B₂₂)
    --final result
    let comb := (Matrix.fromBlocks (M₁ + M₄ - M₅ + M₇) (M₃ + M₅) (M₂ + M₄) (M₁ - M₂ + M₃ + M₆))
    comb.ofPostBlockForm h
  else
    let r := A 0 0 * B 0 0
    .of fun _ _ => r

public theorem StrassenHelper_eq_matrixMul {n : ℕ} {R : Type} [Ring R]
  {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} {B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    Strassen A B = A * B := by
  induction n with
  | zero =>
    simp [Strassen, ← Matrix.ext_iff, Matrix.mul_apply]
  | succ m ih =>
    simp only [Strassen, ih, Matrix.transformationHelper1 (N := A * B),
      Matrix.toPreBlockForm_mul]
    conv =>
      rhs
      rw [← Matrix.fromBlocks_toBlocks (M := A.toPreBlockForm),
        ← Matrix.fromBlocks_toBlocks (M:= B.toPreBlockForm), Matrix.fromBlocks_multiply]
    congr 1
    all_goals grind

def mulProg (x y : ℤ) : Prog unitArithmeticQuery ℤ := do
  let prod : ℕ ← unitArithmeticQuery.mul x.natAbs y.natAbs
  if x < 0
  then
    if y < 0
    then return prod
    else return (- (prod : ℤ))
  else
    if y < 0
    then return (- (prod : ℤ))
    else return prod

lemma mulProd_eval_unit {x y : ℤ} : (mulProg x y).eval unitArithmeticModel = x * y := by
  simp [mulProg]
  grind

lemma mulProd_cost_unit {x y : ℤ} : (mulProg x y).time unitArithmeticModel = 1 := by
  simp [mulProg]
  grind

def StrassenProg {n : ℕ}
  (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) (B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) :
    Prog unitArithmeticQuery (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) := do
  if h : 0 < n
  then
    let A := A.toPreBlockForm h
    let B := B.toPreBlockForm h
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
    let M₁ ← StrassenProg (A₁₁ + A₂₂) (B₁₁ + B₂₂)
    let M₂ ← StrassenProg (A₂₁ + A₂₂) B₁₁
    let M₃ ← StrassenProg A₁₁ (B₁₂ - B₂₂)
    let M₄ ← StrassenProg A₂₂ (B₂₁ - B₁₁)
    let M₅ ← StrassenProg (A₁₁ + A₁₂) B₂₂
    let M₆ ← StrassenProg (A₂₁ - A₁₁) (B₁₁ + B₁₂)
    let M₇ ← StrassenProg (A₁₂ - A₂₂) (B₂₁ + B₂₂)
    --final result
    let comb := (Matrix.fromBlocks (M₁ + M₄ - M₅ + M₇) (M₃ + M₅) (M₂ + M₄) (M₁ - M₂ + M₃ + M₆))
    return comb.ofPostBlockForm h
  else
    let r  ← mulProg (A 0 0) (B 0 0)
    return .of fun _ _ => r


end Algolean.Algorithms
