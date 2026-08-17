import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Log

open Nat

section listAddition

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

theorem lt_base_of_mem_listAddHelper {b : ℕ} (carry : ℕ) {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (hc : carry ≤ 1) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    ∀ x ∈ listAddHelper carry b l₁ l₂, x < b := by
  fun_induction listAddHelper with
  | case1 => simpa
  | case2 => simp
  | case3 carry hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at ⊢ h₂
    constructor
    · refine mod_lt (carry + hd) (by grind)
    · apply ih
      · have := carryAddHelper b carry hd 0 h₂.1 (by lia) hc hb
        simp only [add_zero] at this
        exact this
      · simp
      · apply h₂.2
  | case4 carry hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at ⊢ h₁
    constructor
    · refine mod_lt (carry + hd) (by grind)
    · apply ih
      · have := carryAddHelper b carry 0 hd (by lia) h₁.1 hc hb
        simp only [add_zero] at this
        exact this
      · apply h₁.2
      · simp
  | case5 carry hd tl hd' tl' ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at ⊢ h₁ h₂
    constructor
    · apply mod_lt (carry + hd + hd') (by grind)
    · apply ih
      · apply carryAddHelper b carry hd hd' h₁.1 h₂.1 hc hb
      · apply h₁.2
      · apply h₂.2

theorem ofDigits_listAdd_eq_add_ofDigits {b : ℕ} {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    ofDigits b (listAdd b l₁ l₂) = ofDigits b l₁ + ofDigits b l₂ := by
  simpa [listAdd] using ofDigits_listAddHelper_eq_add_carry_ofDigits 0 hb (by simp) h₁ h₂

theorem length_listAdd {b : ℕ} {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    (listAdd b l₁ l₂).length = max l₁.length l₂.length ∨
    (listAdd b l₁ l₂).length = max l₁.length l₂.length + 1 := by
  simpa [listAdd] using length_listAddHelper 0 hb (by simp) h₁ h₂

theorem lt_base_of_mem_listAdd {b : ℕ} {l₁ l₂ : List ℕ}
  (hb : 2 ≤ b) (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    ∀ x ∈ listAdd b l₁ l₂, x < b := by
  simpa [listAdd] using lt_base_of_mem_listAddHelper 0 hb (by simp) h₁ h₂

end listAddition

section correctness

def KaratsubaHelper (b d : ℕ) (l₁ l₂ : List ℕ) : ℕ :=
  match d with
  | 0 =>
    let x := l₁.take 3
    let y := l₂.take 3
    (ofDigits b x) * (ofDigits b y)
  | succ d' =>
    -- extract parts
    let x₁ := l₁.drop (2^d' + 1)
    let x₂ := l₁.take (2^d' + 1)
    let y₁ := l₂.drop (2^d' + 1)
    let y₂ := l₂.take (2^d' + 1)
    -- addition and bringing into the correct length
    let x₁_add_x₂ := listAdd b x₁ x₂
    let x₁_add_x₂ := x₁_add_x₂ ++ List.replicate (2^d' + 2 - x₁_add_x₂.length) 0
    let y₁_add_y₂ := listAdd b y₁ y₂
    let y₁_add_y₂ := y₁_add_y₂ ++ List.replicate (2^d' + 2 - y₁_add_y₂.length) 0
    -- intermediate results
    let x₁y₁ := KaratsubaHelper b d' (x₁ ++ [0]) (y₁ ++ [0])
    let x₂y₂ := KaratsubaHelper b d' (x₂ ++ [0]) (y₂ ++ [0])
    let x₁y₂_add_x₂y₁ := KaratsubaHelper b d' x₁_add_x₂ y₁_add_y₂ - x₁y₁ - x₂y₂
    --final result
    x₂y₂ + b^(2^d' + 1) * x₁y₂_add_x₂y₁ + (b^(2^d' + 1))^2 * x₁y₁

def Karatsuba (b x y : ℕ) : ℕ :=
  let l₁ := Nat.digits b x
  let l₂ := Nat.digits b y
  let maxLength := max l₁.length l₂.length
  let d := Nat.clog 2 (maxLength - 2)
  KaratsubaHelper b d (l₁ ++ List.replicate (2^d + 2 - l₁.length) 0)
    (l₂ ++ List.replicate (2^d + 2 - l₂.length) 0)

theorem KaratsubaHelper_correct {b d : ℕ} {l₁ l₂ : List ℕ} (h₁ : l₁.length = 2 ^ d + 2)
  (h₂ : l₂.length = 2 ^ d + 2) (h₃ : ∀ x ∈ l₁, x < b) (h₄ : ∀ x ∈ l₂, x < b) (hb : 2 ≤ b) :
    KaratsubaHelper b d l₁ l₂ = ofDigits b l₁ * ofDigits b l₂ := by
  fun_induction KaratsubaHelper with
  | case1 l₁ l₂ x y =>
    simp only [pow_zero, reduceAdd] at h₁ h₂
    have hx : x = l₁ := by simp [x, ← h₁]
    have hy : y = l₂ := by simp [y, ← h₂]
    rw [hx, hy]
  | case2 =>
    expose_names
    have hl₁ : l₁ = x₂ ++ x₁ := by simp [x₂, x₁]
    have hl₂ : l₂ = y₂ ++ y₁ := by simp [y₂, y₁]
    have hx₁_length : x₁.length = 2^d' + 1 := by simp [x₁, h₁]; lia
    have hx₂_length : x₂.length = 2^d' + 1 := by simp [x₂, h₁]; lia
    have hy₁_length : y₁.length = 2^d' + 1 := by simp [y₁, h₂]; lia
    have hy₂_length : y₂.length = 2^d' + 1 := by simp [y₂, h₂]; lia
    have hx₁ : ∀ x ∈ x₁, x < b := by grind
    have hx₂ : ∀ x ∈ x₂, x < b := by grind
    have hy₁ : ∀ y ∈ y₁, y < b := by grind
    have hy₂ : ∀ y ∈ y₂, y < b := by grind
    have hres₁ : x₁y₁ = ofDigits b x₁ * ofDigits b y₁ := by
      simp [x₁y₁, ih3 (by simpa) (by simpa) (by grind) (by grind)]
    have hres₂ : x₂y₂ = ofDigits b x₂ * ofDigits b y₂ := by
      simp [x₂y₂, ih2 (by simpa) (by simpa) (by grind) (by grind)]
    have hres₃ : x₁y₂_add_x₂y₁ = ofDigits b x₁ * ofDigits b y₂ + ofDigits b x₂ * ofDigits b y₁ := by
      simp only [x₁y₂_add_x₂y₁]
      rw [ih1]
      · simp only [ofDigits_append_replicate_zero, hres₁, hres₂, x₁_add_x₂_1, x₁_add_x₂,
        y₁_add_y₂_1, y₁_add_y₂]
        rw [ofDigits_listAdd_eq_add_ofDigits hb, ofDigits_listAdd_eq_add_ofDigits hb]
        · lia
        · grind
        · grind
        · grind
        · grind
      · simp only [List.length_append, List.length_replicate, x₁_add_x₂_1, x₁_add_x₂]
        have := length_listAdd hb hx₁ hx₂
        simp only [hx₁_length, hx₂_length, max_self] at this
        cases this with
        | inl this => simp [this]
        | inr this => simp [this]
      · simp only [List.length_append, List.length_replicate, y₁_add_y₂_1, y₁_add_y₂]
        have := length_listAdd hb hy₁ hy₂
        simp only [hy₁_length, hy₂_length, max_self] at this
        cases this with
        | inl this => simp [this]
        | inr this => simp [this]
      · simp only [List.mem_append, List.mem_replicate, ne_eq, x₁_add_x₂_1, x₁_add_x₂]
        intro x hx
        cases hx with
        | inl hx => apply lt_base_of_mem_listAdd hb hx₁ hx₂ x hx
        | inr hx => grind
      · simp only [List.mem_append, List.mem_replicate, ne_eq, y₁_add_y₂_1, y₁_add_y₂]
        intro y hy
        cases hy with
        | inl hy => apply lt_base_of_mem_listAdd hb hy₁ hy₂ y hy
        | inr hy => grind
    simp [hl₁, hl₂, ofDigits_append, hx₂_length, hy₂_length, hres₁, hres₂, hres₃]
    lia

theorem Karatsuba_correct {b x y : ℕ} (hb : 2 ≤ b) :
    Karatsuba b x y = x * y := by
  simp only [Karatsuba]
  rw [KaratsubaHelper_correct]
  · simp [ofDigits_digits]
  · simp only [List.length_append, List.length_replicate]
    rw [← Nat.add_sub_assoc (n := (b.digits x).length), Nat.sub_add_comm]
    · simp
    · simp
    · apply Nat.le_add_of_sub_le
      simp only [max]
      split
      · rename_i h
        refine Nat.le_trans (m := (b.digits y).length - 2) ?_ ?_
        · exact Nat.sub_le_sub_right h 2
        · apply le_pow_clog
          simp
      · rename_i h
        apply le_pow_clog
        simp
  · simp only [List.length_append, List.length_replicate]
    rw [← Nat.add_sub_assoc (n := (b.digits y).length), Nat.sub_add_comm]
    · simp
    · simp
    · apply Nat.le_add_of_sub_le
      simp only [max]
      split
      · rename_i h
        apply le_pow_clog
        simp
      · rename_i h
        refine Nat.le_trans (m := (b.digits x).length - 2) ?_ ?_
        · simp only [not_le] at h
          exact Nat.sub_le_sub_right (Nat.le_of_lt h) 2
        · apply le_pow_clog
          simp
  · simp only [List.mem_append, List.mem_replicate, ne_eq]
    intro x hx
    cases hx with
    | inl hx => apply Nat.digits_lt_base (by grind) hx
    | inr hx => grind
  · simp only [List.mem_append, List.mem_replicate, ne_eq]
    intro x hx
    cases hx with
    | inl hx => apply Nat.digits_lt_base (by grind) hx
    | inr hx => grind
  · exact hb
end correctness
