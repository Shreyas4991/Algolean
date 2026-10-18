/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Algolean.Algorithms.Karatsuba

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

inductive StrassenMatrix (R : Type) : Type
| base (r : R) : StrassenMatrix R
| combine (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R) : StrassenMatrix R

namespace StrassenMatrix

def height {R : Type} (A : StrassenMatrix R) : ℕ :=
  match A with
  | .base _ => 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ =>
    1 + (max (max A₁₁.height A₁₂.height) (max A₂₁.height A₂₂.height))

@[simp, grind =]
lemma height_combine_base {R : Type} {r : R} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R} :
    height (.combine A₁₁ A₁₂ A₂₁ A₂₂) = height (.base r) ↔ False := by
  simp [height]

@[simp, grind =]
lemma height_base_combine {R : Type} {r : R} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R} :
     height (.base r) = height (.combine A₁₁ A₁₂ A₂₁ A₂₂) ↔ False := by
  simp
  grind

@[simp, grind =]
lemma height_base {R : Type} {r : R} :
    height (.base r) = 0 := by rfl

@[simp, grind =]
lemma height_combine {R : Type} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R} :
    height (.combine A₁₁ A₁₂ A₂₁ A₂₂) =
      1 + (max (max A₁₁.height A₁₂.height) (max A₂₁.height A₂₂.height)) := by rfl

def wellFormed {R : Type} (A : StrassenMatrix R) : Prop :=
  match A with
  | .base _ => True
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ =>
    A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
    A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height

@[simp, grind .]
lemma wellFormed_base {R : Type} {r : R} :
    (StrassenMatrix.base r).wellFormed := by simp [wellFormed]

@[simp, grind =]
lemma wellFormed_combine {R : Type} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R} :
    wellFormed (.combine A₁₁ A₁₂ A₂₁ A₂₂) ↔
    A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
    A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height := by
  simp [wellFormed]

def zero [Zero R] (n : ℕ) : StrassenMatrix R :=
  match n with
  | .zero => .base 0
  | .succ m => .combine (zero m) (zero m) (zero m) (zero m)

def add {R} [Add R] [Zero R] (A B : StrassenMatrix R) : StrassenMatrix R :=
  match A, B with
  | .base r_1, .base r_2 => StrassenMatrix.base (r_1 + r_2)
  | .base _, .combine _ _ _ _ => StrassenMatrix.zero 0
  | .combine _ _ _ _, .base _ => StrassenMatrix.zero 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    StrassenMatrix.combine (add A₁₁ B₁₁) (add A₁₂ B₁₂) (add A₂₁ B₂₁) (add A₂₂ B₂₂)

instance [Zero R] [Add R] : Add (StrassenMatrix R) where
  add := StrassenMatrix.add

@[simp, grind =]
lemma add_base_base {R : Type} [Zero R] [Add R] {r t : R} :
    (StrassenMatrix.base r) + (StrassenMatrix.base t) = (StrassenMatrix.base (r + t)):= by rfl

@[simp, grind =]
lemma add_combine_combine {R : Type} [Add R] [Zero R]
  {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix R} :
    (.combine A₁₁ A₁₂ A₂₁ A₂₂) + (.combine B₁₁ B₁₂ B₂₁ B₂₂) =
      StrassenMatrix.combine (A₁₁ + B₁₁) (A₁₂ + B₁₂) (A₂₁ + B₂₁) (A₂₂ + B₂₂) := by rfl

@[grind =]
lemma height_add {R} [Add R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    height (A + B) = height A := by
  induction A generalizing B with
  | base _ =>
    cases B with
    | base _ => simp
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base _ => simp only [height_combine_base] at h
    | combine =>
      simp at ⊢ h hA hB
      grind

@[grind .]
lemma wellFormed_add {R} [Add R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    (A + B).wellFormed := by
  induction A generalizing B with
  | base _ =>
    cases B with
    | base _ => simp
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base _ => simp only [height_combine_base] at h
    | combine =>
      simp at ⊢ h hA hB
      grind

def neg {R : Type} [Neg R] (A : StrassenMatrix R) : StrassenMatrix R :=
  match A with
  | .base r => .base (- r)
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ => .combine (neg A₁₁) (neg A₁₂) (neg A₂₁) (neg A₂₂)

instance [Neg R] : Neg (StrassenMatrix R) where
  neg := neg

def sub {R} [Sub R] [Zero R] (A B : StrassenMatrix R) : StrassenMatrix R :=
  match A, B with
  | .base r_1, .base r_2 => StrassenMatrix.base (r_1 - r_2)
  | .base _, .combine _ _ _ _ => StrassenMatrix.zero 0
  | .combine _ _ _ _, .base _ => StrassenMatrix.zero 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    StrassenMatrix.combine (sub A₁₁ B₁₁) (sub A₁₂ B₁₂) (sub A₂₁ B₂₁) (sub A₂₂ B₂₂)

instance [Zero R] [Sub R] : Sub (StrassenMatrix R) where
  sub := StrassenMatrix.sub

@[simp, grind =]
lemma sub_base_base {R : Type} [Zero R] [Sub R] {r t : R} :
    (StrassenMatrix.base r) - (StrassenMatrix.base t) = (StrassenMatrix.base (r - t)):= by rfl

@[simp, grind =]
lemma sub_combine_combine {R : Type} [Sub R] [Zero R]
  {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix R} :
    (.combine A₁₁ A₁₂ A₂₁ A₂₂) - (.combine B₁₁ B₁₂ B₂₁ B₂₂) =
      StrassenMatrix.combine (A₁₁ - B₁₁) (A₁₂ - B₁₂) (A₂₁ - B₂₁) (A₂₂ - B₂₂) := by rfl

@[grind =]
lemma height_sub {R} [Sub R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    height (A - B) = height A := by
  induction A generalizing B with
  | base _ =>
    cases B with
    | base _ => simp
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base _ => simp only [height_combine_base] at h
    | combine =>
      simp at ⊢ h hA hB
      grind

@[grind .]
lemma wellFormed_sub {R} [Sub R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    (A - B).wellFormed := by
  induction A generalizing B with
  | base _ =>
    cases B with
    | base _ => simp
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base _ => simp only [height_combine_base] at h
    | combine =>
      simp at ⊢ h hA hB
      grind

def mul [Mul R] [Zero R] (A B : StrassenMatrix R) : StrassenMatrix R :=
  match A, B with
  | .base r_1, .base r_2 => StrassenMatrix.base (r_1 * r_2)
  | .base _, .combine _ _ _ _ => StrassenMatrix.zero 0
  | .combine _ _ _ _, .base _ => StrassenMatrix.zero 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    StrassenMatrix.combine (mul A₁₁ B₁₁) (mul A₁₂ B₁₂) (mul A₂₁ B₂₁) (mul A₂₂ B₂₂)

instance [Zero R] [Mul R] : Mul (StrassenMatrix R) where
  mul := StrassenMatrix.mul

def maxAbsEntry (A : StrassenMatrix ℤ) : ℕ :=
  match A with
  | .base r => r.natAbs
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ =>
    max (max A₁₁.maxAbsEntry A₁₂.maxAbsEntry) (max A₂₁.maxAbsEntry A₂₂.maxAbsEntry)

@[simp, grind =]
lemma maxAbsEntry_base (z : ℤ) : maxAbsEntry (.base z) = z.natAbs := by rfl

lemma maxAbsEntry_combine₁₁ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₁₁.maxAbsEntry ≤ (A₁₁.combine  A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₁₂ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₁₂.maxAbsEntry ≤ (A₁₁.combine  A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₂₁ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₂₁.maxAbsEntry ≤ (A₁₁.combine  A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₂₂ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₂₂.maxAbsEntry ≤ (A₁₁.combine  A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_add {A B : StrassenMatrix ℤ} (h : A.height = B.height)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    (A + B).maxAbsEntry ≤ A.maxAbsEntry + B.maxAbsEntry := by
  induction A generalizing B with
  | base =>
    cases B with
    | base => simpa using Int.natAbs_add_le _ _
    | combine => simp only [height_base_combine] at h
  | combine A₁₁ A₁₂ A₂₁ A₂₂ ih₁ ih₂ ih₃ ih₄ =>
    cases B with
    | base => simp only [height_combine_base] at h
    | combine B₁₁ B₁₂ B₂₁ B₂₂ =>
      conv =>
        lhs
        simp only [add_combine_combine, maxAbsEntry, Nat.max_assoc]
      grw [ih₁ (by grind) (by grind) (by grind), ih₂ (by grind) (by grind) (by grind),
        ih₃ (by grind) (by grind) (by grind), ih₄ (by grind) (by grind) (by grind)]
      simp only [sup_le_iff]
      grw [maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂, maxAbsEntry_combine₁₂ A₁₁ A₁₂ A₂₁ A₂₂,
        maxAbsEntry_combine₂₁ A₁₁ A₁₂ A₂₁ A₂₂, maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂,
        maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂, maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂,
        maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂, maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂]
      simp

lemma maxAbsEntry_sub {A B : StrassenMatrix ℤ} (h : A.height = B.height)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    (A - B).maxAbsEntry ≤ A.maxAbsEntry + B.maxAbsEntry := by
  induction A generalizing B with
  | base =>
    cases B with
    | base => simpa using Int.natAbs_sub_le _ _
    | combine => simp only [height_base_combine] at h
  | combine A₁₁ A₁₂ A₂₁ A₂₂ ih₁ ih₂ ih₃ ih₄ =>
    cases B with
    | base => simp only [height_combine_base] at h
    | combine B₁₁ B₁₂ B₂₁ B₂₂ =>
      conv =>
        lhs
        simp only [sub_combine_combine, maxAbsEntry, Nat.max_assoc]
      grw [ih₁ (by grind) (by grind) (by grind), ih₂ (by grind) (by grind) (by grind),
        ih₃ (by grind) (by grind) (by grind), ih₄ (by grind) (by grind) (by grind)]
      simp only [sup_le_iff]
      grw [maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂, maxAbsEntry_combine₁₂ A₁₁ A₁₂ A₂₁ A₂₂,
        maxAbsEntry_combine₂₁ A₁₁ A₁₂ A₂₁ A₂₂, maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂,
        maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂, maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂,
        maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂, maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂]
      simp

end StrassenMatrix

open StrassenMatrix

namespace Algolean.Algorithms

open Prog

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

public def arithReduction (b : ℕ) (hb : 2 ≤ b) :
    Reduction unitArithmeticQuery (boundedArithmeticQuery (b ^ 3)) where
  reduce
  | .mul x y => KaratsubaProg b x y hb

public lemma arithReduction_correct {b : ℕ} (hb : 2 ≤ b) {ι : Type} (q : unitArithmeticQuery ι) :
    ((arithReduction b hb).reduce q).eval (boundedArithmeticModel (b ^ 3))
      = unitArithmeticModel.evalQuery q := by
  cases q with
  | mul x y => simp [arithReduction, KaratsubaProg_eval, Karatsuba_correct hb]


def StrassenProg (A B : StrassenMatrix ℤ) (h : A.height = B.height)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    Prog unitArithmeticQuery (StrassenMatrix ℤ) := do
  match h₁ : A, h₂ : B with
  | .base r, .base t =>
     return .base (← mulProg r t)
  | .base _, .combine _ _ _ _ => by simp [h₁, h₂] at h; grind
  | .combine _ _ _ _, .base _ => by simp [h₁, h₂] at h;
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    have h := by simp only [h₁, height_combine, Nat.max_assoc, h₂,
      Nat.add_left_cancel_iff] at h; exact h
    have hA := by simp only [h₁, wellFormed] at hA; exact hA
    have hB := by simp only [h₂, wellFormed] at hB; exact hB
    let M₁ ← StrassenProg (A₁₁ + A₂₂) (B₁₁ + B₂₂) (by grind) (by grind) (by grind)
    let M₂ ← StrassenProg (A₂₁ + A₂₂) B₁₁ (by grind) (by grind) (by grind)
    let M₃ ← StrassenProg A₁₁ (B₁₂ - B₂₂) (by grind) (by grind) (by grind)
    let M₄ ← StrassenProg A₂₂ (B₂₁ - B₁₁) (by grind) (by grind) (by grind)
    let M₅ ← StrassenProg (A₁₁ + A₁₂) B₂₂ (by grind) (by grind) (by grind)
    let M₆ ← StrassenProg (A₂₁ - A₁₁) (B₁₁ + B₁₂) (by grind) (by grind) (by grind)
    let M₇ ← StrassenProg (A₁₂ - A₂₂) (B₂₁ + B₂₂) (by grind) (by grind) (by grind)
    return .combine (M₁ + M₄ - M₅ + M₇) (M₃ + M₅) (M₂ + M₄) (M₁ - M₂ + M₃ + M₆)
termination_by StrassenMatrix.height A
decreasing_by
  all_goals grind

lemma StrassenProg_time_unit {A B : StrassenMatrix ℤ} (h : A.height = B.height)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    (StrassenProg A B h hA hB).time unitArithmeticModel = 7 ^ (A.height) := by
  induction h' : A.height generalizing A B with
  | zero =>
    cases A with
    | base =>
      cases B with
      | base => simp [StrassenProg, mulProd_cost_unit]
      | combine => grind
    | combine => grind
  | succ m ih =>
    cases A with
    | base => grind
    | combine =>
      cases B with
      | base => grind
      | combine =>
        simp [StrassenProg]
        simp [Nat.add_comm m 1] at h h'
        grind

noncomputable def KaratsubaTime (x y : ℕ) : ℝ := 3 * (max x y) ^ Real.logb 2 3

lemma KaratsubaTime_mono (hx : x ≤ x') (hy : y ≤ y') : KaratsubaTime x y ≤ KaratsubaTime x' y' := by
  simp only [KaratsubaTime, Nat.cast_max, Nat.ofNat_pos, mul_le_mul_iff_right₀]
  refine Real.rpow_le_rpow ?_ ?_ ?_
  · grind
  · refine sup_le_sup (Nat.cast_le.mpr hx) (Nat.cast_le.mpr hy)
  · refine (Real.logb_nonneg_iff (by grind) (by grind)).mpr (by grind)

theorem StrassenProg_time_boundedArithmetic {b : ℕ} (hb : 2 ≤ b) {A B : StrassenMatrix ℤ}
  (h : A.height = B.height) (hA : A.wellFormed) (hB : B.wellFormed) :
  (((StrassenProg A B h hA hB).reduceProg (arithReduction b hb)).time
      (boundedArithmeticModel (b ^ 3)))
    ≤ 7 ^ A.height * KaratsubaTime ((b.digits A.maxAbsEntry).length + A.height) ((b.digits B.maxAbsEntry).length + A.height) := by
  rw [reduceProg_time _ _ _ _ (arithReduction_correct hb)]
  induction h' : A.height generalizing A B with
  | zero =>
    cases A with
    | base =>
      cases B with
      | base =>
        simp [StrassenProg, mulProg, KaratsubaTime]
        split <;> split <;> simpa [arithReduction] using Karatsuba_time hb
      | combine => simp only [height_base_combine] at h
    | combine => simp at h'
  | succ m ih =>
    cases A with
    | base => simp at h'
    | combine A₁₁ A₁₂ A₂₁ A₂₂ =>
      cases B with
      | base => simp only [height_combine_base] at h
      | combine B₁₁ B₁₂ B₂₁ B₂₂ =>
        have hb' : 1 < b := by grind
        simp [StrassenProg]
        simp [unitArithmeticModel] at ih
        simp at hA hB h
        grw [ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind),
          ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind)]
        have h₁ : (KaratsubaTime ((b.digits (A₁₁ + A₂₂).maxAbsEntry).length + m) ((b.digits (B₁₁ + B₂₂).maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := A₁₁.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := B₁₁.maxAbsEntry + B₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
        have h₂ : (KaratsubaTime ((b.digits (A₂₁ + A₂₂).maxAbsEntry).length + m) ((b.digits B₁₁.maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := A₂₁.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₁ A₁₁ A₁₂ A₂₁ A₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            apply Nat.le_add_right_of_le
            apply Nat.length_digits_le_of_le _ hb'
            apply maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
        have h₃ : (KaratsubaTime ((b.digits A₁₁.maxAbsEntry).length + m) ((b.digits (B₁₂ - B₂₂).maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            apply Nat.le_add_right_of_le
            apply Nat.length_digits_le_of_le _ hb'
            apply maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := B₁₂.maxAbsEntry + B₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
            · apply maxAbsEntry_sub (by grind) (by grind) (by grind)
        have h₄ : (KaratsubaTime ((b.digits A₂₂.maxAbsEntry).length + m) ((b.digits (B₂₁ - B₁₁).maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            apply Nat.le_add_right_of_le
            apply Nat.length_digits_le_of_le _ hb'
            apply maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := B₂₁.maxAbsEntry + B₁₁.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
            · apply maxAbsEntry_sub (by grind) (by grind) (by grind)
        have h₅ : (KaratsubaTime ((b.digits (A₁₁ + A₁₂).maxAbsEntry).length + m) ((b.digits B₂₂.maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := A₁₁.maxAbsEntry + A₁₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            · simp
              constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₂ A₁₁ A₁₂ A₂₁ A₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            apply Nat.le_add_right_of_le
            apply Nat.length_digits_le_of_le _ hb'
            apply maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
        have h₆ : (KaratsubaTime ((b.digits (A₂₁ - A₁₁).maxAbsEntry).length + m) ((b.digits (B₁₁ + B₁₂).maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := A₂₁.maxAbsEntry + A₁₁.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            · simp
              constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₁ A₁₁ A₁₂ A₂₁ A₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂
            · apply maxAbsEntry_sub (by grind) (by grind) (by grind)
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := B₁₁.maxAbsEntry + B₁₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
        have h₇ : (KaratsubaTime ((b.digits (A₁₂ - A₂₂).maxAbsEntry).length + m) ((b.digits (B₂₁ + B₂₂).maxAbsEntry).length + m))
            ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
                ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1)))  := by
          apply KaratsubaTime_mono
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := A₁₂.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            · simp
              constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₁₂ A₁₁ A₁₂ A₂₁ A₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂
            · apply maxAbsEntry_sub (by grind) (by grind) (by grind)
          · rw [Nat.add_comm m 1, ← Nat.add_assoc]
            refine Nat.add_le_add_right ?_ m
            grw [Nat.length_digits_le_of_le (y := B₂₁.maxAbsEntry + B₂₂.maxAbsEntry) _ hb',
              Nat.length_digits_add (by grind)]
            simp
            · constructor
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂
              · apply Nat.length_digits_le_of_le _ hb'
                exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
            · apply maxAbsEntry_add (by grind) (by grind) (by grind)
        grw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
        let (eq := h') x := KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1)) ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))
        simp [← h']
        clear ih h₁ h₂ h₃ h₄ h₅ h₆ h₇ hA hB
        rw [← two_mul]
        have eq' : (2 : ℝ) = ↑(2 : ℕ) := by grind
        have : ∀ (x : ℝ) (y : ℕ) , x + y * x = ((Nat.add y 1) : ℝ) * x := by
          grind
        rw [eq']
        rw [this (7 ^ m * x), this (7 ^ m * x), this (7 ^ m * x), this (7 ^ m * x), this (7 ^ m * x)]
        simp
        have : (7 ^ (m + 1) : ℝ) = (7 ^ (m + 1) : ℕ) := by grind
        rw [this, Nat.pow_add', Nat.pow_one]
        simp
        grind

end Algolean.Algorithms
