/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Algolean.Algorithms.Karatsuba

section digits

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

end digits

inductive StrassenMatrix (R : Type) : Type
| base (r : R) : StrassenMatrix R
| combine (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R) : StrassenMatrix R

namespace StrassenMatrix

def height {R : Type} (A : StrassenMatrix R) : ℕ :=
  match A with
  | .base _ => 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ =>
    (max (max A₁₁.height A₁₂.height) (max A₂₁.height A₂₂.height)) + 1

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
      (max (max A₁₁.height A₁₂.height) (max A₂₁.height A₂₂.height)) + 1 := by rfl

def wellFormed {R : Type} (A : StrassenMatrix R) : Bool :=
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

lemma height_combined_of_wellFormed {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix R}
  (hA : (StrassenMatrix.combine A₁₁ A₁₂ A₂₁ A₂₂).wellFormed)
  (hB : (StrassenMatrix.combine B₁₁ B₁₂ B₂₁ B₂₂).wellFormed)
  (h : (StrassenMatrix.combine A₁₁ A₁₂ A₂₁ A₂₂).height =
    (StrassenMatrix.combine B₁₁ B₁₂ B₂₁ B₂₂).height) :
    A₁₁.height = B₁₁.height ∧ A₁₂.height = B₁₂.height ∧
      A₂₁.height = B₂₁.height ∧ A₂₂.height = B₂₂.height := by
  simp only [wellFormed_combine, height_combine, Nat.max_assoc, Nat.add_right_cancel_iff] at hA hB h
  have h₁ := hA.2.2.2.2.1
  have h₂ := hA.2.2.2.2.2.1
  have h₃ := hA.2.2.2.2.2.2
  have h₄ := hB.2.2.2.2.1
  have h₅ := hB.2.2.2.2.2.1
  have h₆ := hB.2.2.2.2.2.2
  simp [h₁, h₂, h₃, h₄, h₅, h₆] at h
  grind

lemma height_combined_of_wellFormed' {n : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R}
  (hA : (StrassenMatrix.combine A₁₁ A₁₂ A₂₁ A₂₂).wellFormed)
  (h : (StrassenMatrix.combine A₁₁ A₁₂ A₂₁ A₂₂).height = n.succ) :
    A₁₁.height = n ∧ A₁₂.height = n ∧
      A₂₁.height = n ∧ A₂₂.height = n := by
  simp only [wellFormed_combine, height_combine, Nat.max_assoc] at hA h
  have h₁ := hA.2.2.2.2.1
  have h₂ := hA.2.2.2.2.2.1
  have h₃ := hA.2.2.2.2.2.2
  simp [h₁, h₂, h₃] at h
  grind

def zero [Zero R] (n : ℕ) : StrassenMatrix R :=
  match n with
  | .zero => .base 0
  | .succ m => .combine (zero m) (zero m) (zero m) (zero m)

@[simp, grind =]
lemma height_zero {R : Type} [Zero R] {n : ℕ} : (StrassenMatrix.zero n (R:= R)).height = n := by
  induction n with
  | zero => simp [zero]
  | succ => simp [zero]; grind

@[simp, grind .]
lemma wellFormed_zero {R : Type} [Zero R] {n : ℕ} : (StrassenMatrix.zero n (R:= R)).wellFormed := by
  induction n with
  | zero => simp [zero]
  | succ => simp [zero]; grind

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

@[simp, grind =]
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
  | combine A₁₁ A₁₂ A₂₁ A₂₂ ih₁ ih₂ ih₃ ih₄ =>
    cases B with
    | base _ => simp only [height_combine_base] at h
    | combine B₁₁ B₁₂ B₂₁ B₂₂ =>
      have h := height_combined_of_wellFormed hA hB h
      simp at ⊢ hA hB
      grind

@[grind =]
lemma add_assoc {R} [Ring R] {A B C : StrassenMatrix R}
  (h : height A = height B) (h' : height B = height C)
  (hA : A.wellFormed) (hB : B.wellFormed) (hC : C.wellFormed) :
    A + B + C = A + (B + C) := by
  induction A generalizing B C with
  | base =>
    cases B with
    | base =>
      cases C with
      | base => simp [_root_.add_assoc]
      | combine => simp only [height_base_combine] at h'
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base => simp at h
    | combine =>
      cases C with
      | base => simp at h'
      | combine =>
        have h := height_combined_of_wellFormed hA hB h
        grind

@[grind =]
lemma add_comm {R} [Ring R] {A B : StrassenMatrix R}
  (h : height A = height B)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    A + B = B + A:= by
  induction A generalizing B with
  | base =>
    cases B with
    | base => grind
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base => simp at h
    | combine =>
      have h := height_combined_of_wellFormed hA hB h
      grind

@[simp, grind =]
lemma add_zero {R} [Ring R] {A : StrassenMatrix R} {n : ℕ}
  (h : A.height = n) (hA : A.wellFormed) :
    A + (StrassenMatrix.zero n) = A := by
  induction A generalizing n with
  | base =>
    simp at h
    simp [← h, zero]
  | combine =>
    simp only [height_combine, Nat.max_assoc] at h
    simp [← h, zero]
    grind

@[simp, grind =]
lemma zero_add {R} [Ring R] {A : StrassenMatrix R} {n : ℕ}
  (h : A.height = n) (hA : A.wellFormed) :
    (StrassenMatrix.zero n) + A = A := by
  grind

def neg {R : Type} [Neg R] (A : StrassenMatrix R) : StrassenMatrix R :=
  match A with
  | .base r => .base (- r)
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ => .combine (neg A₁₁) (neg A₁₂) (neg A₂₁) (neg A₂₂)

instance {R : Type} [Neg R] : Neg (StrassenMatrix R) where
  neg := neg

@[simp, grind =]
lemma neg_base {R : Type} [Neg R] {r : R} :
  - (.base r) = (StrassenMatrix.base (- r)) := by rfl

@[simp, grind =]
lemma neg_combine {R : Type} [Neg R]
  {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix R} :
    - (.combine A₁₁ A₁₂ A₂₁ A₂₂) = StrassenMatrix.combine (- A₁₁) (-A₁₂) (- A₂₁) (- A₂₂) := by
  rfl

@[simp, grind =]
lemma height_neg {R : Type} [Neg R] {A : StrassenMatrix R} :
    (- A).height = A.height := by
  induction A with
  | base => simp
  | combine => grind

@[simp, grind =]
lemma wellFormed_neg {R : Type} [Neg R] {A : StrassenMatrix R} :
    (- A).wellFormed ↔ A.wellFormed := by
  induction A with
  | base => simp
  | combine => grind

@[simp, grind =]
lemma neg_add_cancel {R : Type} [Ring R] {A : StrassenMatrix R} (hA : A.wellFormed) :
    (-A) + A = StrassenMatrix.zero (A.height) := by
  induction A with
  | base => simp [zero]
  | combine =>
    simp [zero] at hA ⊢
    grind

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

@[grind =]
lemma sub_eq_add_neg {R : Type} [Ring R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    A - B = A + (- B) := by
  induction A generalizing B with
  | base =>
    cases B with
    | base =>
      simp only [sub_base_base, neg_base, add_base_base, base.injEq]
      apply SubNegMonoid.sub_eq_add_neg
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base => simp only [height_combine_base] at h
    | combine =>
      grind

def mul [Mul R] [Add R] [Zero R] (A B : StrassenMatrix R) : StrassenMatrix R :=
  match A, B with
  | .base r_1, .base r_2 => StrassenMatrix.base (r_1 * r_2)
  | .base _, .combine _ _ _ _ => StrassenMatrix.zero 0
  | .combine _ _ _ _, .base _ => StrassenMatrix.zero 0
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    StrassenMatrix.combine ((mul A₁₁ B₁₁) + (mul A₁₂ B₂₁)) ((mul A₁₁ B₁₂) + (mul A₁₂ B₂₂))
        ((mul A₂₁ B₁₁) + (mul A₂₂ B₂₁)) ((mul A₂₁ B₁₂) + (mul A₂₂ B₂₂))

instance [Zero R] [Add R] [Mul R] : Mul (StrassenMatrix R) where
  mul := StrassenMatrix.mul

@[simp, grind =]
lemma mul_base_base [Add R] [Mul R] [Zero R] {r s : R} :
    (.base r) * (.base s) = (StrassenMatrix.base (r * s)) := by
  rfl

@[simp, grind =]
lemma mul_combine_combine {R : Type} [Add R] [Mul R] [Zero R]
  {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix R} :
    (.combine A₁₁ A₁₂ A₂₁ A₂₂) * (.combine B₁₁ B₁₂ B₂₁ B₂₂) =
      StrassenMatrix.combine (A₁₁ * B₁₁ + A₁₂ * B₂₁) (A₁₁ * B₁₂ + A₁₂ * B₂₂)
        (A₂₁ * B₁₁ + A₂₂ * B₂₁) (A₂₁ * B₁₂ + A₂₂ * B₂₂) := by rfl

lemma wellFormed_height_mul {R} [Add R] [Mul R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    (A*B).wellFormed ∧ height (A * B) = height A := by
  induction A generalizing B with
  | base =>
    cases B with
    | base => simp
    | combine => simp only [height_base_combine] at h
  | combine =>
    cases B with
    | base => simp only [height_combine_base] at h
    | combine =>
      simp at ⊢ h hA hB
      grind

@[simp, grind =]
lemma height_mul {R} [Add R] [Mul R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    height (A * B) = height A := by
  apply (wellFormed_height_mul h hA hB).2

@[simp, grind =]
lemma height_mul' {R} [Add R] [Mul R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    height (A * B) = height B := by
  simp [h, hA, hB]

@[grind .]
lemma wellFormed_mul {R} [Add R] [Mul R] [Zero R] {A B : StrassenMatrix R}
  (h : height A = height B) (hA : A.wellFormed) (hB : B.wellFormed) :
    (A * B).wellFormed := by
  apply (wellFormed_height_mul h hA hB).1

def maxAbsEntry (A : StrassenMatrix ℤ) : ℕ :=
  match A with
  | .base r => r.natAbs
  | .combine A₁₁ A₁₂ A₂₁ A₂₂ =>
    max (max A₁₁.maxAbsEntry A₁₂.maxAbsEntry) (max A₂₁.maxAbsEntry A₂₂.maxAbsEntry)

@[simp, grind =]
lemma maxAbsEntry_base (z : ℤ) : maxAbsEntry (.base z) = z.natAbs := by rfl

lemma maxAbsEntry_combine (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry = A₁₁.maxAbsEntry ∨
    (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry = A₁₂.maxAbsEntry ∨
    (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry = A₂₁.maxAbsEntry ∨
    (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry = A₂₂.maxAbsEntry := by
  simp [maxAbsEntry]
  grind

lemma maxAbsEntry_combine₁₁ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₁₁.maxAbsEntry ≤ (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₁₂ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₁₂.maxAbsEntry ≤ (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₂₁ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₂₁.maxAbsEntry ≤ (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry := by
  simp [maxAbsEntry]

lemma maxAbsEntry_combine₂₂ (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ) :
    A₂₂.maxAbsEntry ≤ (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry := by
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

def toStrassenMatrix (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) : StrassenMatrix R :=
  match n with
  | .zero => .base (A 0 0)
  | .succ m =>
    .combine (toStrassenMatrix (.of (fun (i j : Fin (2 ^ m)) => A ⟨i.1, by lia⟩ ⟨j.1, by lia⟩)))
      (toStrassenMatrix (.of (fun (i j : Fin (2 ^ m)) => A ⟨i.1, by lia⟩ ⟨j.1 + 2 ^ m, by lia⟩)))
      (toStrassenMatrix (.of (fun (i j : Fin (2 ^ m)) => A ⟨i.1 + 2 ^ m, by lia⟩ ⟨j.1, by lia⟩)))
      (toStrassenMatrix (.of (fun (i j : Fin (2 ^ m)) => A ⟨i.1 + 2 ^ m, by lia⟩
        ⟨j.1 + 2 ^ m, by lia⟩)))

@[simp, grind =]
lemma height_toStrassenMatrix {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    height (toStrassenMatrix A) = n := by
  induction n with
  | zero => simp [toStrassenMatrix]
  | succ m ih =>
    simp [toStrassenMatrix, ih]

lemma wellFormed_toStrassenMatrix {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    wellFormed (toStrassenMatrix A) := by
  induction n with
  | zero => simp [toStrassenMatrix]
  | succ m ih => simp [toStrassenMatrix, ih]

lemma toStrassenMatrix_inj {n : ℕ} {R : Type} {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    toStrassenMatrix A = toStrassenMatrix B ↔ A = B := by
  induction n with
  | zero => simp [toStrassenMatrix, ← Matrix.ext_iff]
  | succ m ih =>
    simp only [toStrassenMatrix, Nat.succ_eq_add_one, combine.injEq, ih,
      EmbeddingLike.apply_eq_iff_eq, ← Matrix.ext_iff]
    constructor
    · simp only [funext_iff, and_imp]
      intro h₁ h₂ h₃ h₄ i j
      by_cases hi : i.1 < 2 ^ m
      · by_cases hj : j.1 < 2 ^ m
        · apply h₁ ⟨i.1, hi⟩ ⟨j.1, hj⟩
        · specialize h₂ ⟨i.1, hi⟩ ⟨j.1 - 2 ^ m, by lia⟩
          simp only [Fin.eta] at h₂
          have : ⟨↑j - 2 ^ m + 2 ^ m, by lia⟩ = j := by
            simp only [Fin.ext_iff]
            apply Nat.sub_add_cancel
            simp only [not_lt] at hj
            apply hj
          rw [this] at h₂
          apply h₂
      · by_cases hj : j.1 < 2 ^ m
        · specialize h₃ ⟨i.1 - 2 ^ m, by lia⟩ ⟨j.1, hj⟩
          grind
        · specialize h₄ ⟨i.1 - 2 ^ m, by lia⟩ ⟨j.1 - 2 ^ m, by lia⟩
          grind
    · intro h
      simp [h]

@[simp, grind =]
lemma toStrassenMatrix_add [Ring R] {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    (toStrassenMatrix A) + (toStrassenMatrix B) = toStrassenMatrix (A + B) := by
  induction n with
  | zero => simp [toStrassenMatrix]
  | succ m ih =>
    have : ∀ (f g: (Fin (2 ^ m)) → (Fin (2 ^ m)) → R),
      (fun i j => (f i j) + (g i j)) = fun i j => ((f + g) i j) := by
      intro f g
      apply funext₂
      intro i j
      simp
    simp [toStrassenMatrix, ih, this]

@[simp, grind =]
lemma toStrassenMatrix_sub [Ring R] {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    (toStrassenMatrix A) - (toStrassenMatrix B) = toStrassenMatrix (A - B) := by
  induction n with
  | zero => simp [toStrassenMatrix]
  | succ m ih =>
    have : ∀ (f g: (Fin (2 ^ m)) → (Fin (2 ^ m)) → R),
      (fun i j => (f i j) - (g i j)) = fun i j => ((f - g) i j) := by
      intro f g
      apply funext₂
      intro i j
      simp
    simp [toStrassenMatrix, ih, this]

lemma sum_helper (f : Fin (2 ^ (n + 1)) → R) [Ring R] :
    ∑ (x : Fin (2 ^ n)), f ⟨x.1, by lia⟩
    + ∑ (x : Fin (2 ^ n)), f ⟨x.1 + 2 ^ n, by lia⟩
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
    by_cases h' : x.1 < 2 ^ n
    · left
      use ⟨x.1, h'⟩
      simp [e₁, ← Function.Embedding.toFun_eq_coe]
    · right
      use ⟨x.1 - 2 ^ n , by lia⟩
      simp [e₂, ← Function.Embedding.toFun_eq_coe]
      grind
  have dist : Disjoint (Finset.map e₁ Finset.univ) (Finset.map e₂ Finset.univ) := by
    simp [Finset.disjoint_iff_ne, e₁, e₂, ← Function.Embedding.toFun_eq_coe]
    lia
  simp [this, Finset.sum_union dist, e₁, e₂, ← Function.Embedding.toFun_eq_coe]

@[simp, grind =]
lemma toStrassenMatrix_mul [Ring R] {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    (toStrassenMatrix A) * (toStrassenMatrix B) = toStrassenMatrix (A * B) := by
  induction n with
  | zero =>
    simp [toStrassenMatrix, Matrix.mul_apply]
  | succ m ih =>
    simp only [toStrassenMatrix, Nat.succ_eq_add_one, StrassenMatrix.mul_combine_combine, ih,
      toStrassenMatrix_add, Matrix.mul_apply, StrassenMatrix.combine.injEq]
    split_ands
    · congr
      simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
      intro i j
      rw [sum_helper (fun k => A ⟨i, by lia⟩ k * B k ⟨j, by lia⟩)]
    · congr
      simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
      intro i j
      rw [sum_helper (fun k => A ⟨i, by lia⟩ k * B k ⟨j + 2 ^ m, by lia⟩)]
    · congr
      simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
      intro i j
      rw [sum_helper (fun k => A ⟨i + 2 ^ m, by lia⟩ k * B k ⟨j, by lia⟩)]
    · congr
      simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
      intro i j
      rw [sum_helper (fun k => A ⟨i + 2 ^ m, by lia⟩ k * B k ⟨j + 2 ^ m, by lia⟩)]

def ofStrassenMatrixHelper {R : Type} {n : ℕ} (A : StrassenMatrix R)
  (hA : A.wellFormed) (h : height A = n) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  match A, n with
  | .base r, .zero => .of (fun _ _ => r)
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .succ m =>
    have h := height_combined_of_wellFormed' hA h
    have hA := by simp only [wellFormed_combine] at hA; exact hA
    .of (fun i j =>
      if hi : i.1 < 2 ^ m
      then
        if hj : j.1 < 2 ^ m
        then (ofStrassenMatrixHelper A₁₁ (by grind) h.1) ⟨i, hi⟩ ⟨j, hj⟩
        else (ofStrassenMatrixHelper A₁₂ (by grind) h.2.1) ⟨i, hi⟩ ⟨j - 2 ^ m, by lia⟩
      else
        if hj : j.1 < 2 ^ m
        then (ofStrassenMatrixHelper A₂₁ (by grind) h.2.2.1) ⟨i - 2 ^ m, by lia⟩ ⟨j, hj⟩
        else (ofStrassenMatrixHelper A₂₂ (by grind) h.2.2.2) ⟨i - 2 ^ m, by lia⟩ ⟨j - 2 ^ m, by lia⟩
    )

def ofStrassenMatrix {R : Type} [Zero R] (n : ℕ) (A : StrassenMatrix R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  if h : A.wellFormed ∧ A.height = n
  then ofStrassenMatrixHelper A h.1 h.2
  else .of (fun _ _ => 0)

@[simp, grind =]
lemma ofStrassenMatrix_toStrassenMatrix_eq_self {R : Type} [Zero R] {n : ℕ}
  (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    ofStrassenMatrix n (toStrassenMatrix A) = A := by
  simp only [ofStrassenMatrix, wellFormed_toStrassenMatrix, height_toStrassenMatrix, and_self,
    ↓reduceDIte]
  induction n with
  | zero => simp [toStrassenMatrix, ofStrassenMatrixHelper, ← Matrix.ext_iff]
  | succ m ih =>
    simp only [toStrassenMatrix, Nat.succ_eq_add_one, ofStrassenMatrixHelper, ← Matrix.ext_iff,
      Matrix.of_apply]
    intro i j
    by_cases hi : i.1 < 2 ^ m
    · by_cases hj : j.1 < 2 ^ m
      · simp [hi, hj, ih]
      · simp [hi, hj, ih]
        grind
    · by_cases hj : j.1 < 2 ^ m
      · simp [hi, hj, ih]
        grind
      · simp [hi, hj, ih]
        grind

def Matrix.maxAbsEntry {n : ℕ} (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) :=
  Finset.univ (α := (Fin (2 ^ n)) × (Fin (2 ^ n))) |>.image (fun x => (A x.1 x.2).natAbs)
    |>.max' (by simp)

lemma maxAbsEntry_iff {n a : ℕ} {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ} :
    a = A.maxAbsEntry ↔
      (∃ (i j : Fin (2 ^ n)), (A i j).natAbs = a) ∧ ∀ i j, (A i j).natAbs ≤ a := by
  rw [Eq.comm]
  simp only [Matrix.maxAbsEntry, Finset.max'_eq_iff, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists, forall_exists_index, and_congr_right_iff]
  intro i j ha
  constructor
  · intro h k l
    apply h _ k l rfl
  · intro h b k l hb
    rw [← hb]
    apply h

lemma maxAbsEntry_toStrassenMatrix {n : ℕ} (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ) :
    (toStrassenMatrix A).maxAbsEntry = A.maxAbsEntry := by
  simp only [maxAbsEntry_iff]
  induction n with
  | zero =>
    simp [toStrassenMatrix]
  | succ m ih =>
    simp only [toStrassenMatrix, Nat.succ_eq_add_one]
    let (eq := h₁) A₁₁ := (toStrassenMatrix
      (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j, by lia⟩)))
    let (eq := h₂) A₁₂ := (toStrassenMatrix
      (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j + 2 ^ m, by lia⟩)))
    let (eq := h₃) A₂₁ := (toStrassenMatrix
      (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩ ⟨↑j, by lia⟩)))
    let (eq := h₄) A₂₂ := (toStrassenMatrix
      (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩ ⟨↑j + 2 ^ m, by lia⟩)))
    simp only [← h₁, ← h₂, ← h₃, ← h₄]
    constructor
    · have h := maxAbsEntry_combine A₁₁ A₁₂ A₂₁ A₂₂
      cases h with
      | inl h =>
        specialize ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j, by lia⟩))
        rcases ih.1 with ⟨i, j, hij⟩
        simp [← h₁] at hij
        simp [h, ← hij]
      | inr h =>
        cases h with
        | inl h =>
          specialize ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j + 2 ^ m, by lia⟩))
          rcases ih.1 with ⟨i, j, hij⟩
          simp [← h₂] at hij
          simp [h, ← hij]
        | inr h =>
          cases h with
          | inl h =>
            specialize ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩
              ⟨↑j, by lia⟩))
            rcases ih.1 with ⟨i, j, hij⟩
            simp [← h₃] at hij
            simp [h, ← hij]
          | inr h =>
            specialize ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩
              ⟨↑j + 2 ^ m, by lia⟩))
            rcases ih.1 with ⟨i, j, hij⟩
            simp [← h₄] at hij
            simp [h, ← hij]
    · intro i j
      by_cases hi : i.1 < 2 ^ m
      · by_cases hj : j.1 < 2 ^ m
        · apply Nat.le_trans ?_ (maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂)
          simp only [h₁]
          have := (ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j, by lia⟩))).2
            ⟨i.1, hi⟩ ⟨j.1, hj⟩
          simp only [Matrix.of_apply, Fin.eta] at this
          apply this
        · apply Nat.le_trans ?_ (maxAbsEntry_combine₁₂ A₁₁ A₁₂ A₂₁ A₂₂)
          simp only [h₂]
          have := (ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i, by lia⟩ ⟨↑j + 2 ^ m, by lia⟩))).2
            ⟨i.1, hi⟩ ⟨j.1 - 2 ^ m, by lia⟩
          have hj' : ⟨↑j - 2 ^ m + 2 ^ m, by lia⟩ = j := by
            simp only [Fin.ext_iff]
            apply Nat.sub_add_cancel
            simp only [not_lt] at hj
            apply hj
          simp only [Matrix.of_apply, Fin.eta, hj'] at this
          apply this
      · have hi' : ⟨↑i - 2 ^ m + 2 ^ m, by lia⟩ = i := by
            simp only [Fin.ext_iff]
            apply Nat.sub_add_cancel
            simp only [not_lt] at hi
            apply hi
        by_cases hj : j.1 < 2 ^ m
        · apply Nat.le_trans ?_ (maxAbsEntry_combine₂₁ A₁₁ A₁₂ A₂₁ A₂₂)
          simp only [h₃]
          have := (ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩ ⟨↑j, by lia⟩))).2
            ⟨i.1 - 2 ^ m, by lia⟩ ⟨j.1, hj⟩
          simp only [Matrix.of_apply, hi', Fin.eta] at this
          apply this
        · apply Nat.le_trans ?_ (maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂)
          simp only [h₄]
          have := (ih (Matrix.of (fun (i j : Fin (2 ^ m)) ↦ A ⟨↑i + 2 ^ m, by lia⟩
            ⟨↑j + 2 ^ m, by lia⟩))).2 ⟨i.1 - 2 ^ m, by lia⟩ ⟨j.1 - 2 ^ m, by lia⟩
          have hj' : ⟨↑j - 2 ^ m + 2 ^ m, by lia⟩ = j := by
            simp only [Fin.ext_iff]
            apply Nat.sub_add_cancel
            simp only [not_lt] at hj
            apply hj
          simp only [Matrix.of_apply, hi', hj'] at this
          apply this

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

def arithReduction (b : ℕ) (hb : 2 ≤ b) :
    Reduction unitArithmeticQuery (boundedArithmeticQuery (b ^ 3)) where
  reduce
  | .mul x y => KaratsubaProg b x y hb

lemma arithReduction_correct {b : ℕ} (hb : 2 ≤ b) {ι : Type} (q : unitArithmeticQuery ι) :
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
  | .base _, .combine _ _ _ _ => by simp [h₁, h₂] at h
  | .combine _ _ _ _, .base _ => by simp [h₁, h₂] at h;
  | .combine A₁₁ A₁₂ A₂₁ A₂₂, .combine B₁₁ B₁₂ B₂₁ B₂₂ =>
    have h := by simp only [h₁, height_combine, Nat.max_assoc, h₂] at h; exact h
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

theorem StrassenProg_eval_unit {A B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ} :
    (StrassenProg (toStrassenMatrix A) (toStrassenMatrix B) (by simp)
        (by apply wellFormed_toStrassenMatrix) (by apply wellFormed_toStrassenMatrix)).eval
      unitArithmeticModel = toStrassenMatrix (A * B) := by
  induction n with
  | zero =>
    simp [toStrassenMatrix, StrassenProg, mulProd_eval_unit, Matrix.mul_apply]
  | succ m ih =>
    simp only [toStrassenMatrix, Nat.succ_eq_add_one, StrassenProg, toStrassenMatrix_add,
      toStrassenMatrix_sub, bind_pure_comp, eval_bind, ih, eval_map, Matrix.mul_apply,
      combine.injEq, toStrassenMatrix_inj]
    let (eq := h₁) A₁₁ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ A ⟨i.1, by lia⟩ ⟨j.1, by lia⟩)
    let (eq := h₂) A₁₂ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ A ⟨i.1, by lia⟩
      ⟨j.1 + 2 ^ m, by lia⟩)
    let (eq := h₃) A₂₁ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ A ⟨i.1 + 2 ^ m, by lia⟩
      ⟨j.1, by lia⟩)
    let (eq := h₄) A₂₂ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ A ⟨i.1 + 2 ^ m, by lia⟩
      ⟨j.1 + 2 ^ m, by lia⟩)
    let (eq := h₅) B₁₁ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ B ⟨i.1, by lia⟩ ⟨j.1, by lia⟩)
    let (eq := h₆) B₁₂ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ B ⟨i.1, by lia⟩
      ⟨j.1 + 2 ^ m, by lia⟩)
    let (eq := h₇) B₂₁ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ B ⟨i.1 + 2 ^ m, by lia⟩
      ⟨j.1, by lia⟩)
    let (eq := h₈) B₂₂ := (Matrix.of fun (i j : Fin (2 ^ m)) ↦ B ⟨i.1 + 2 ^ m, by lia⟩
      ⟨j.1 + 2 ^ m, by lia⟩)
    simp only [← h₁, ← h₄, ← h₅, ← h₈, ← h₇, ← h₂, ← h₆, ← h₃]
    have : Matrix.of (fun (i j : Fin (2 ^ m)) ↦ ∑ k, A ⟨↑i, by lia⟩ k * B k ⟨↑j, by lia⟩) =
        A₁₁ * B₁₁ + A₁₂ * B₂₁ := by
      simp only [h₁, h₅, h₂, h₇, ← Matrix.ext_iff, Matrix.of_apply, Matrix.add_apply,
        Matrix.mul_apply]
      intro i j
      rw [sum_helper (f := fun k => A ⟨i.1, by lia⟩ k * B k ⟨j.1, by lia⟩)]
    rw [this]
    have : Matrix.of (fun (i j : Fin (2 ^ m)) ↦ ∑ k, A ⟨↑i, by lia⟩ k * B k ⟨↑j + 2 ^ m, by lia⟩) =
        A₁₁ * B₁₂ + A₁₂ * B₂₂ := by
      simp only [h₁, h₆, h₂, h₈, ← Matrix.ext_iff, Matrix.of_apply, Matrix.add_apply,
        Matrix.mul_apply]
      intro i j
      rw [sum_helper (f := fun k => A ⟨i.1, by lia⟩ k * B k ⟨j.1 + 2 ^ m, by lia⟩)]
    rw [this]
    have : Matrix.of (fun (i j : Fin (2 ^ m)) ↦ ∑ k, A ⟨↑i + 2 ^ m, by lia⟩ k * B k ⟨↑j, by lia⟩) =
        A₂₁ * B₁₁ + A₂₂ * B₂₁ := by
      simp only [h₃, h₅, h₄, h₇, ← Matrix.ext_iff, Matrix.of_apply, Matrix.add_apply,
        Matrix.mul_apply]
      intro i j
      rw [sum_helper (f := fun k => A ⟨i.1 + 2 ^ m, by lia⟩ k * B k ⟨j.1, by lia⟩)]
    rw [this]
    have : Matrix.of (fun (i j : Fin (2 ^ m)) ↦ ∑ k, A ⟨↑i + 2 ^ m, by lia⟩ k *
        B k ⟨↑j + 2 ^ m, by lia⟩) = A₂₁ * B₁₂ + A₂₂ * B₂₂ := by
      simp only [h₃, h₆, h₄, h₈, ← Matrix.ext_iff, Matrix.of_apply, Matrix.add_apply,
        Matrix.mul_apply]
      intro i j
      rw [sum_helper (f := fun k => A ⟨i.1 + 2 ^ m, by lia⟩ k * B k ⟨j.1 + 2 ^ m, by lia⟩)]
    rw [this]
    grind

theorem StrassenProg_time_unit {A B : StrassenMatrix ℤ} (h : A.height = B.height)
  (hA : A.wellFormed) (hB : B.wellFormed) :
    (StrassenProg A B h hA hB).time unitArithmeticModel = 7 ^ (A.height) := by
  induction h' : A.height generalizing A B with
  | zero =>
    cases A with
    | base =>
      cases B with
      | base => simp [StrassenProg, mulProd_cost_unit]
      | combine => simp only [height_base_combine] at h
    | combine => simp at h'
  | succ m ih =>
    cases A with
    | base => simp at h'
    | combine =>
      cases B with
      | base => grind
      | combine =>
        simp [StrassenProg]
        simp [Nat.add_comm m 1] at h h'
        grind

noncomputable def KaratsubaTime (x y : ℕ) : ℝ := 3 * (max x y) ^ Real.logb 2 3

lemma KaratsubaTime_mono {x x' y y' : ℕ} (hx : x ≤ x') (hy : y ≤ y') :
    KaratsubaTime x y ≤ KaratsubaTime x' y' := by
  simp only [KaratsubaTime, Nat.cast_max, Nat.ofNat_pos, mul_le_mul_iff_right₀]
  refine Real.rpow_le_rpow ?_ ?_ ?_
  · grind
  · refine sup_le_sup (Nat.cast_le.mpr hx) (Nat.cast_le.mpr hy)
  · refine (Real.logb_nonneg_iff (by grind) (by grind)).mpr (by grind)

-- the following seven lemmas are used in the time complexity proof but moved out
-- for a better overview and speed.

private lemma StrassenProg_Karatsuba_helper1
  {b : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ} (m : ℕ) (hb' : 1 < b)
  (hA : A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
     A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height)
  (hB : B₁₁.wellFormed ∧ B₁₂.wellFormed ∧ B₂₁.wellFormed ∧ B₂₂.wellFormed
    ∧ B₁₁.height = B₁₂.height ∧ B₁₂.height = B₂₁.height ∧ B₂₁.height = B₂₂.height) :
    (KaratsubaTime ((b.digits (A₁₁ + A₂₂).maxAbsEntry).length + m)
        ((b.digits (B₁₁ + B₂₂).maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
  apply KaratsubaTime_mono
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := A₁₁.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₁ A₁₁ A₁₂ A₂₁ A₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₂ A₁₁ A₁₂ A₂₁ A₂₂
    · apply maxAbsEntry_add (by grind) (by grind) (by grind)
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := B₁₁.maxAbsEntry + B₂₂.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
    · apply maxAbsEntry_add (by grind) (by grind) (by grind)

private lemma StrassenProg_Karatsuba_helper2
  {b : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ} (B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ)
  (m : ℕ) (hb' : 1 < b)
  (hA : A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
     A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height) :
    (KaratsubaTime ((b.digits (A₂₁ + A₂₂).maxAbsEntry).length + m)
        ((b.digits B₁₁.maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
  apply KaratsubaTime_mono
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := A₂₁.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
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

private lemma StrassenProg_Karatsuba_helper3
  {b : ℕ} {B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ} (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ)
  (m : ℕ) (hb' : 1 < b)
  (hB : B₁₁.wellFormed ∧ B₁₂.wellFormed ∧ B₂₁.wellFormed ∧ B₂₂.wellFormed
    ∧ B₁₁.height = B₁₂.height ∧ B₁₂.height = B₂₁.height ∧ B₂₁.height = B₂₂.height) :
    (KaratsubaTime ((b.digits A₁₁.maxAbsEntry).length + m)
        ((b.digits (B₁₂ - B₂₂).maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
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
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
    · apply maxAbsEntry_sub (by grind) (by grind) (by grind)

private lemma StrassenProg_Karatsuba_helper4
  {b : ℕ} {B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ} (A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ)
  (m : ℕ) (hb' : 1 < b)
  (hB : B₁₁.wellFormed ∧ B₁₂.wellFormed ∧ B₂₁.wellFormed ∧ B₂₂.wellFormed
    ∧ B₁₁.height = B₁₂.height ∧ B₁₂.height = B₂₁.height ∧ B₂₁.height = B₂₂.height) :
    (KaratsubaTime ((b.digits A₂₂.maxAbsEntry).length + m)
        ((b.digits (B₂₁ - B₁₁).maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
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
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
    · apply maxAbsEntry_sub (by grind) (by grind) (by grind)

private lemma StrassenProg_Karatsuba_helper5
  {b : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ : StrassenMatrix ℤ} (B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ)
  (m : ℕ) (hb' : 1 < b)
  (hA : A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
     A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height) :
    (KaratsubaTime ((b.digits (A₁₁ + A₁₂).maxAbsEntry).length + m)
        ((b.digits B₂₂.maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
        ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
  apply KaratsubaTime_mono
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := A₁₁.maxAbsEntry + A₁₂.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
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

private lemma StrassenProg_Karatsuba_helper6
  {b : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ} (m : ℕ) (hb' : 1 < b)
  (hA : A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
     A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height)
  (hB : B₁₁.wellFormed ∧ B₁₂.wellFormed ∧ B₂₁.wellFormed ∧ B₂₂.wellFormed
    ∧ B₁₁.height = B₁₂.height ∧ B₁₂.height = B₂₁.height ∧ B₂₁.height = B₂₂.height) :
    (KaratsubaTime ((b.digits (A₂₁ - A₁₁).maxAbsEntry).length + m)
        ((b.digits (B₁₁ + B₁₂).maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
  apply KaratsubaTime_mono
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := A₂₁.maxAbsEntry + A₁₁.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
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
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₁ B₁₁ B₁₂ B₂₁ B₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₁₂ B₁₁ B₁₂ B₂₁ B₂₂
    · apply maxAbsEntry_add (by grind) (by grind) (by grind)

private lemma StrassenProg_Karatsuba_helper7
  {b : ℕ} {A₁₁ A₁₂ A₂₁ A₂₂ B₁₁ B₁₂ B₂₁ B₂₂ : StrassenMatrix ℤ} (m : ℕ) (hb' : 1 < b)
  (hA : A₁₁.wellFormed ∧ A₁₂.wellFormed ∧ A₂₁.wellFormed ∧ A₂₂.wellFormed ∧
     A₁₁.height = A₁₂.height ∧ A₁₂.height = A₂₁.height ∧ A₂₁.height = A₂₂.height)
  (hB : B₁₁.wellFormed ∧ B₁₂.wellFormed ∧ B₂₁.wellFormed ∧ B₂₂.wellFormed
    ∧ B₁₁.height = B₁₂.height ∧ B₁₂.height = B₂₁.height ∧ B₂₁.height = B₂₂.height) :
    (KaratsubaTime ((b.digits (A₁₂ - A₂₂).maxAbsEntry).length + m)
        ((b.digits (B₂₁ + B₂₂).maxAbsEntry).length + m))
      ≤ (KaratsubaTime ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
        ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))) := by
  apply KaratsubaTime_mono
  · rw [Nat.add_comm m 1, ← Nat.add_assoc]
    refine Nat.add_le_add_right ?_ m
    grw [Nat.length_digits_le_of_le (y := A₁₂.maxAbsEntry + A₂₂.maxAbsEntry) _ hb',
      Nat.length_digits_add (by grind)]
    · simp only [add_le_add_iff_right, sup_le_iff]
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
    · simp only [add_le_add_iff_right, sup_le_iff]
      constructor
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₁ B₁₁ B₁₂ B₂₁ B₂₂
      · apply Nat.length_digits_le_of_le _ hb'
        exact maxAbsEntry_combine₂₂ B₁₁ B₁₂ B₂₁ B₂₂
    · apply maxAbsEntry_add (by grind) (by grind) (by grind)

theorem StrassenProg_time_boundedArithmetic {b : ℕ} (hb : 2 ≤ b) {A B : StrassenMatrix ℤ}
  (h : A.height = B.height) (hA : A.wellFormed) (hB : B.wellFormed) :
  (((StrassenProg A B h hA hB).reduceProg (arithReduction b hb)).time
      (boundedArithmeticModel (b ^ 3)))
    ≤ 7 ^ A.height * (KaratsubaTime ((b.digits A.maxAbsEntry).length + A.height)
      ((b.digits B.maxAbsEntry).length + A.height)) := by
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
        simp only [unitArithmeticModel_evalQuery, StrassenProg, bind_pure_comp,
          Cslib.FreeM.liftM_bind, Cslib.FreeM.liftM_map, AddWriter.tell_bind, AddWriter.tell_map,
          Nat.cast_add, ge_iff_le]
        simp only [unitArithmeticModel] at ih
        simp only [wellFormed_combine, height_combine, Nat.max_assoc] at hA hB h
        grw [ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind),
          ih _ _ _ (by grind), ih _ _ _ (by grind), ih _ _ _ (by grind)]
        have h₁ := StrassenProg_Karatsuba_helper1 m hb' hA hB
        have h₂ := StrassenProg_Karatsuba_helper2 B₁₁ B₁₂ B₂₁ B₂₂ m hb' hA
        have h₃ := StrassenProg_Karatsuba_helper3 A₁₁ A₁₂ A₂₁ A₂₂ m hb' hB
        have h₄ := StrassenProg_Karatsuba_helper4 A₁₁ A₁₂ A₂₁ A₂₂ m hb' hB
        have h₅ := StrassenProg_Karatsuba_helper5 B₁₁ B₁₂ B₂₁ B₂₂ m hb' hA
        have h₆ := StrassenProg_Karatsuba_helper6 m hb' hA hB
        have h₇ := StrassenProg_Karatsuba_helper7 m hb' hA hB
        grw [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
        let (eq := h') x := KaratsubaTime
          ((b.digits (A₁₁.combine A₁₂ A₂₁ A₂₂).maxAbsEntry).length + (m + 1))
          ((b.digits (B₁₁.combine B₁₂ B₂₁ B₂₂).maxAbsEntry).length + (m + 1))
        simp only [← h', ge_iff_le]
        clear ih h₁ h₂ h₃ h₄ h₅ h₆ h₇ hA hB
        rw [← two_mul]
        have eq' : (2 : ℝ) = ↑(2 : ℕ) := by grind
        have : ∀ (x : ℝ) (y : ℕ) , x + y * x = ((Nat.add y 1) : ℝ) * x := by
          grind
        rw [eq']
        rw [this (7 ^ m * x), this (7 ^ m * x), this (7 ^ m * x), this (7 ^ m * x),
          this (7 ^ m * x)]
        simp only [Nat.add_eq, Nat.reduceAdd, Nat.cast_ofNat, ge_iff_le]
        have : (7 ^ (m + 1) : ℝ) = (7 ^ (m + 1) : ℕ) := by grind
        rw [this, Nat.pow_add', Nat.pow_one]
        simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, ge_iff_le]
        rw [mul_assoc]

end Algolean.Algorithms
