
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection

variable {n : ℕ} {R : Type}

def M₁₁ (M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  .of fun i j => M ⟨i.1, by lia⟩ ⟨j.1, by lia⟩

def M₁₂ (M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  .of fun i j => M ⟨i.1, by lia⟩ ⟨j.1 + 2^n, by lia⟩

def M₂₁ (M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  .of fun i j => M ⟨i.1 + 2^n , by lia⟩ ⟨j.1, by lia⟩

def M₂₂ (M : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  .of fun i j => M ⟨i.1+2^n, by lia⟩ ⟨j.1 + 2^n, by lia⟩

def combine (N₁₁ N₁₂ N₂₁ N₂₂ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R :=
  .of fun i j =>
    if hi : i.1 < 2^n
    then
      if hj : j.1 < 2^n
      then N₁₁ ⟨i.1, hi⟩ ⟨j.1, hj⟩
      else N₁₂ ⟨i.1, hi⟩ ⟨j.1 - 2^n, by lia⟩
    else
      if hj : j.1 < 2^n
      then N₂₁ ⟨i.1 - 2^n, by lia⟩ ⟨j.1, hj⟩
      else N₂₂ ⟨i.1 - 2^n, by lia⟩ ⟨j.1 - 2^n, by lia⟩

lemma combine_eq_self {A : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R} :
    combine (M₁₁ A) (M₁₂ A) (M₂₁ A) (M₂₂ A) = A := by
  simp [combine, ← Matrix.ext_iff, M₁₁, M₂₁, M₁₂, M₂₂]
  grind

variable [Ring R]

lemma mul_combine {A B : Matrix (Fin (2 ^ n.succ)) (Fin (2 ^ n.succ)) R} :
    combine (M₁₁ A * M₁₁ B + M₁₂ A * M₂₁ B) (M₁₁ A * M₁₂ B + M₁₂ A * M₂₂ B) (M₂₁ A * M₁₁ B + M₂₂ A * M₂₁ B)
      (M₂₁ A * M₁₂ B + M₂₂ A * M₂₂ B) = A * B := by
  rw [← combine_eq_self (A := A*B)]
  sorry

def Strassen.helper {n : ℕ} {R : Type} [Ring R]
  (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) (B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R :=
  match n with
  | .zero =>
    let r := A 0 0 * B 0 0
    .of fun _ _ => r
  | .succ _ =>
    let M₁ := helper (M₁₁ A + M₂₂ A) (M₁₁ B + M₂₂ B)
    let M₂ := helper (M₂₁ A + M₂₂ A) (M₁₁ B)
    let M₃ := helper (M₁₁ A) (M₁₂ B - M₂₂ B)
    let M₄ := helper (M₂₂ A) (M₂₁ B - M₁₁ B)
    let M₅ := helper (M₁₁ A + M₁₂ A) (M₂₂ B)
    let M₆ := helper (M₂₁ A - M₁₁ A) (M₁₁ B + M₁₂ B)
    let M₇ := helper (M₁₂ A - M₂₂ A) (M₂₁ B + M₂₂ B)
    combine (M₁ + M₄ - M₅ + M₇) (M₃ + M₅) (M₂ + M₄) (M₁ - M₂ + M₃ + M₆)

lemma Strassen.helper_eq_matrixMul {n : ℕ} {R : Type} [Ring R]
  {A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} {B : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) R} :
    Strassen.helper A B = A * B := by
  induction n with
  | zero =>
    simp [helper, ← Matrix.ext_iff, Matrix.mul_apply]
  | succ m ih =>
    rw [← mul_combine]
    simp [helper, ih]
    congr 1
    · grind
    · grind
    · grind
    · grind
