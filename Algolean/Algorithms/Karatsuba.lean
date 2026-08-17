import Mathlib.Data.Nat.Digits.Defs

open Nat

theorem carryAddHelper (b x y z : ℕ) (h₁ : y < b) (h₂ : z < b) (h₃ : x ≤ 1) (h₄ : 2 ≤ b) :
    (x + y + z)/b ≤ 1 := by
  refine (Nat.div_le_iff_le_mul_add_pred ?_).mpr ?_
  · apply Nat.lt_of_lt_of_le (by simp) h₄
  · lia

def listAddHelper (carry b : ℕ) (l₁ l₂ : List ℕ) : List ℕ :=
  match l₁, l₂ with
  | [], [] =>
    if carry = 1
    then [1]
    else []
  | [], hd::tl =>
    ((carry + hd) % b)::(listAddHelper ((carry + hd) / b) b [] tl)
  | hd::tl, [] =>
    ((carry + hd) % b)::(listAddHelper ((carry + hd) / b) b tl [])
  | hd::tl, hd'::tl' =>
    ((carry + hd + hd') % b)::(listAddHelper ((carry + hd + hd') / b) b tl tl')

def listAdd (b : ℕ) (l₁ l₂ : List ℕ) : List ℕ :=
  listAddHelper 0 b l₁ l₂

theorem ofDigits_listAddHelper_eq_add_carry_ofDigits {b : ℕ} (carry : ℕ) {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (hc : carry ≤ 1) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    ofDigits b (listAddHelper carry b l₁ l₂) = carry + ofDigits b l₁ + ofDigits b l₂ := by
  fun_induction listAddHelper with
  | case1 => simp
  | case2 carry h =>
    simp
    lia
  | case3 carry hd tl ih =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, ofDigits_nil, add_zero,
      forall_const, List.mem_cons, forall_eq_or_imp, ofDigits_cons] at ⊢ ih h₂
    rw [ih]
    · rw [mul_add, ← add_assoc, mod_add_div, add_assoc]
    · have := carryAddHelper b carry hd 0 h₂.1 (by lia) hc hb
      simp only [add_zero] at this
      exact this
    · apply h₂.2
  | case4 carry hd tl ih =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, ofDigits_nil, add_zero,
      forall_const, List.mem_cons, forall_eq_or_imp, ofDigits_cons] at ⊢ ih h₁
    rw [ih]
    · rw [mul_add, ← add_assoc, mod_add_div, add_assoc]
    · have := carryAddHelper b carry hd 0 h₁.1 (by lia) hc hb
      simp only [add_zero] at this
      exact this
    · apply h₁.2
  | case5 carry hd tl hd' tl' ih =>
    simp only [List.mem_cons, forall_eq_or_imp, ofDigits_cons] at ⊢ ih h₁ h₂
    rw [ih]
    · rw [mul_add, mul_add, ← add_assoc, ← add_assoc, mod_add_div]
      lia
    · exact carryAddHelper b carry hd hd' h₁.1 h₂.1 hc hb
    · apply h₁.2
    · apply h₂.2

theorem length_listAddHelper {b : ℕ} (carry : ℕ) {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (hc : carry ≤ 1) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    (listAddHelper carry b l₁ l₂).length = max l₁.length l₂.length ∨
    (listAddHelper carry b l₁ l₂).length = max l₁.length l₂.length + 1 := by
  fun_induction listAddHelper with
  | case1 => simp
  | case2 => simp
  | case3 carry hd tl ih =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.length_nil, _root_.zero_le,
      sup_of_le_right, forall_const, List.mem_cons, forall_eq_or_imp, List.length_cons,
      le_add_iff_nonneg_left, Nat.add_right_cancel_iff] at ⊢ ih h₂
    apply ih ?_ h₂.2
    have := carryAddHelper b carry hd 0 h₂.1 (by lia) hc hb
    simp only [add_zero] at this
    exact this
  | case4 carry hd tl ih =>
    simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, List.length_nil, _root_.zero_le,
      sup_of_le_left, forall_const, List.mem_cons, forall_eq_or_imp, List.length_cons,
      le_add_iff_nonneg_left, Nat.add_right_cancel_iff] at ⊢ ih h₁
    apply ih ?_ h₁.2
    have := carryAddHelper b carry hd 0 h₁.1 (by lia) hc hb
    simp only [add_zero] at this
    exact this
  | case5 carry hd tl hd' tl' ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, Nat.add_max_add_right,
      Nat.add_right_cancel_iff] at ⊢ ih h₁ h₂
    apply ih ?_ h₁.2 h₂.2
    exact carryAddHelper b carry hd hd' h₁.1 h₂.1 hc hb

theorem ofDigits_listAdd_eq_add_ofDigits {b : ℕ} {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    ofDigits b (listAdd b l₁ l₂) = ofDigits b l₁ + ofDigits b l₂ := by
  simpa [listAdd] using ofDigits_listAddHelper_eq_add_carry_ofDigits 0 hb (by simp) h₁ h₂

theorem length_listAdd {b : ℕ} {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    (listAdd b l₁ l₂).length = max l₁.length l₂.length ∨
    (listAdd b l₁ l₂).length = max l₁.length l₂.length + 1 := by
  simpa [listAdd] using length_listAddHelper 0 hb (by simp) h₁ h₂
