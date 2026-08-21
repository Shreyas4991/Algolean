/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/

module

public import Algolean.Models.Arithmetic
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Karatsuba's Algorithm

In this module we state Karatsuba's algorithm for multiplying two numbers
in O(n^log_2(3)) and prove its correctness and the time bound. The algorithm works
for arbitrary bases b ≥ 2. We analyse the complexity in the bounded-length multiplication
model where we are only allowed to multiply at most 3 digit numbers except for shifts.
We measure the runtime by counting the number of these multiplications.

--

## Main definitions

- `Karatsuba` : Karatsuba's algorithm for two natural numbers x and y and a base b
- `KaratsubaProg` : Karatsuba's algorithm implemented in Prog.

## Main results

- `Karatsuba_correct` : shows that the `Karatsuba` computes the product of x and y if 2 ≤ b
- `Karatsuba_time` : shows that `KaratsubaProg` uses at most
  3 * (max (b.digits x).length (b.digits y).length ^ (Real.logb 2 3) multiplication of
    3 digit numbers in base b for 2 ≤ b
-/

@[expose] public section

namespace Algolean.Algorithms

open Nat Prog

section listAddition

theorem carryAddHelper (b x y z : ℕ) (h₁ : y < b) (h₂ : z < b) (h₃ : x ≤ 1) (h₄ : 2 ≤ b) :
    (x + y + z)/b ≤ 1 := by
  refine (Nat.div_le_iff_le_mul_add_pred ?_).mpr ?_
  · apply Nat.lt_of_lt_of_le (by simp) h₄
  · lia

/--
A helper function that adds two lists of natural numbers viewed as a representation of a number
in base b together with a carry.
-/
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

/--
A helper function that adds two lists of natural numbers viewed as a representation of a number
in base b. We use this to bound the length of the sum of two numbers.
-/
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

/--
A helper function to execute Karatsubas algorithm for two numbers entered as digit lists l₁ l₂
in base b. In order to be correct it is assumed that |l₁| = |l₂| = 2 ^ d + 2
-/
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

/--
Karatsuba's algorithm to multiply two numbers in subquadratic time.
-/
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

section time

theorem boundedMul_helper {b : ℕ} {l : List ℕ} (hb : 2 ≤ b) (h : ∀ x ∈ l, x < b) :
    ofDigits b (l.take 3) < b^3 := by
  have := @Nat.ofDigits_lt_base_pow_length b (l.take 3) (by grind) ?_
  · simp only [List.length_take, min, pow_ite] at this
    split at this
    · exact this
    · rename_i h'
      simp only [not_le] at h'
      apply Nat.lt_trans this (Nat.pow_lt_pow_of_lt hb h')
  · intro x hx
    apply h x (List.mem_of_mem_take hx)

/--
`KaratsubaHelper` implemented in Prog with the `mulQuery` query type.
-/
def KaratsubaHelperProg (b d : ℕ) (l₁ l₂ : List ℕ) (hb : 2 ≤ b)
  (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    Prog (mulQuery (b^3)) ℕ := do
  match d with
  | 0 =>
    let x := l₁.take 3
    let y := l₂.take 3
    have h₁ : ofDigits b x < b^3 := boundedMul_helper hb h₁
    have h₂ : ofDigits b y < b^3 := boundedMul_helper hb h₂
    return ← mulQuery.mul (ofDigits b x) (ofDigits b y) h₁ h₂
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
    let x₁y₁ ← KaratsubaHelperProg b d' (x₁ ++ [0]) (y₁ ++ [0]) hb (by grind) (by grind)
    let x₂y₂ ← KaratsubaHelperProg b d' (x₂ ++ [0]) (y₂ ++ [0]) hb (by grind) (by grind)
    have h₁' : ∀ x ∈ x₁_add_x₂, x < b := by
      expose_names
      simp only [List.mem_append, List.mem_replicate, ne_eq, x₁_add_x₂, x₁_add_x₂_1]
      intro x hx
      cases hx with
      | inl hx =>
        apply lt_base_of_mem_listAdd (l₁ := x₁) (l₂ := x₂) hb (by grind) (by grind) x hx
      | inr hx => grind
    have h₂' : ∀ x ∈ y₁_add_y₂, x < b := by
      expose_names
      simp only [List.mem_append, List.mem_replicate, ne_eq, y₁_add_y₂, y₁_add_y₂_1]
      intro x hx
      cases hx with
      | inl hx =>
        apply lt_base_of_mem_listAdd (l₁ := y₁) (l₂ := y₂) hb (by grind) (by grind) x hx
      | inr hx => grind
    let x₁y₂_add_x₂y₁ := (← KaratsubaHelperProg b d' x₁_add_x₂ y₁_add_y₂ hb h₁' (by grind))
      - x₁y₁ - x₂y₂
    --final result
    return x₂y₂ + b^(2^d' + 1) * x₁y₂_add_x₂y₁ + (b^(2^d' + 1))^2 * x₁y₁

/--
`Karatsuba` implemented in Prog. This differs from the original implementation that
the multiplication of zeroes is directly handled here, because for the runtime proof
it was important that maxLength ≥ 1 holds.
-/
def KaratsubaProg (b x y : ℕ) (hb : 2 ≤ b) :
    Prog (mulQuery (b^3)) ℕ := do
  let l₁ := Nat.digits b x
  let l₂ := Nat.digits b y
  let maxLength := max l₁.length l₂.length
  if maxLength < 1
  then
    return 0
  let d := Nat.clog 2 (maxLength - 2)
  have h₁ : ∀ z ∈ (l₁ ++ List.replicate (2^d + 2 - l₁.length) 0), z < b := by
    intro z hz
    simp only [List.mem_append, List.mem_replicate, ne_eq] at hz
    cases hz with
    | inl hz => apply Nat.digits_lt_base (by grind) hz
    | inr hz => grind
  have h₂ : ∀ z ∈ (l₂ ++ List.replicate (2^d + 2 - l₂.length) 0), z < b := by
    intro z hz
    simp only [List.mem_append, List.mem_replicate, ne_eq] at hz
    cases hz with
    | inl hz => apply Nat.digits_lt_base (by grind) hz
    | inr hz => grind
  return ← (KaratsubaHelperProg b d (l₁ ++ List.replicate (2^d + 2 - l₁.length) 0)
    (l₂ ++ List.replicate (2^d + 2 - l₂.length) 0) hb h₁ h₂)

theorem KaratsubaHelperProg_eval {b d : ℕ} {l₁ l₂ : List ℕ} (hb : 2 ≤ b)
  (h₁ : ∀ x ∈ l₁, x < b) (h₂ : ∀ x ∈ l₂, x < b) :
    (KaratsubaHelperProg b d l₁ l₂ hb h₁ h₂).eval (mulModel (b^3)) = KaratsubaHelper b d l₁ l₂ := by
  fun_induction KaratsubaHelper with
  | case1 l₁ l₂ x y =>
    simp [KaratsubaHelperProg, x, y]
  | case2 =>
    expose_names
    simp only [KaratsubaHelperProg, bind_pure_comp, eval_bind, eval_map]
    rw [ih1, ih2, ih3]

theorem KaratsubaProg_eval (b x y : ℕ) (hb : 2 ≤ b) :
    (KaratsubaProg b x y hb).eval (mulModel (b^3)) = Karatsuba b x y := by
  simp only [KaratsubaProg, bind_pure, Karatsuba]
  split
  · rename_i h
    simp only [Order.lt_one_iff, max_eq_zero, List.length_eq_zero_iff,
      digits_eq_nil_iff_eq_zero] at h
    simp only [eval_pure, h.1, digits_zero, List.length_nil, h.2, max_self, zero_tsub,
      clog_zero_right, pow_zero, reduceAdd, tsub_zero, List.reduceReplicate, List.nil_append]
    rw [KaratsubaHelper_correct (hb := hb)]
    · simp [ofDigits]
    · decide
    · decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq]
      exact zero_lt_of_lt hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq]
      exact zero_lt_of_lt hb
  · simp only [pure_bind]
    rw [KaratsubaHelperProg_eval]

theorem KaratsubaHelperProg_time {b d : ℕ} {l₁ l₂ : List ℕ} (hb : 2 ≤ b)
  (h₁ : l₁.length = 2 ^ d + 2) (h₂ : l₂.length = 2 ^ d + 2)
  (h₃ : ∀ x ∈ l₁, x < b) (h₄ : ∀ x ∈ l₂, x < b) :
    (KaratsubaHelperProg b d l₁ l₂ hb h₃ h₄).time (mulModel (b^3)) = 3 ^ d := by
  fun_induction KaratsubaHelperProg with
  | case1 => simp
  | case2 =>
    expose_names
    have hl₁ : l₁_1 = x₂ ++ x₁ := by simp [x₂, x₁]
    have hl₂ : l₂_1 = y₂ ++ y₁ := by simp [y₂, y₁]
    have hx₁_length : x₁.length = 2^d' + 1 := by simp [x₁, h₁]; lia
    have hx₂_length : x₂.length = 2^d' + 1 := by simp [x₂, h₁]; lia
    have hy₁_length : y₁.length = 2^d' + 1 := by simp [y₁, h₂]; lia
    have hy₂_length : y₂.length = 2^d' + 1 := by simp [y₂, h₂]; lia
    have hx₁ : ∀ x ∈ x₁, x < b := by grind
    have hx₂ : ∀ x ∈ x₂, x < b := by grind
    have hy₁ : ∀ y ∈ y₁, y < b := by grind
    have hy₂ : ∀ y ∈ y₂, y < b := by grind
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
      Nat.add_right_cancel_iff, bind_pure_comp, time_bind, time_map,
      succ_eq_add_one] at ih1 ih2 ih3 ⊢
    rw [ih1, ih2, ih3]
    · lia
    · assumption
    · assumption
    · assumption
    · assumption
    · simp [x₁_add_x₂_1, x₁_add_x₂]
      have := length_listAdd hb hx₁ hx₂
      grind
    · simp [y₁_add_y₂_1, y₁_add_y₂]
      have := length_listAdd hb hy₁ hy₂
      grind

theorem _root_.Nat.clog_le_add_one_log_base_two (n : ℕ) : Nat.clog 2 n ≤ 1 + Nat.log 2 n := by
  rw [← Real.natFloor_logb_natCast, ← Real.natCeil_logb_natCast, add_comm]
  apply Nat.ceil_le_floor_add_one

theorem Karatsuba_time (b x y : ℕ) (hb : 2 ≤ b) :
    (KaratsubaProg b x y hb).time (mulModel (b^3)) ≤
      3 * ((max (digits b x).length (digits b y).length) : ℝ) ^ Real.logb 2 3 := by
  simp only [KaratsubaProg, bind_pure]
  let n := max (b.digits x).length (b.digits y).length
  have hn : n = max (b.digits x).length (b.digits y).length := by simp [n]
  have hn' : (n : ℝ) = max ((b.digits x).length : ℝ) ((b.digits y).length :ℝ) := by
    simp [n]
  split
  · simp only [time_pure, CharP.cast_eq_zero, ofNat_pos, mul_nonneg_iff_of_pos_left, ge_iff_le]
    positivity
  · simp only [pure_bind, ge_iff_le]
    rename_i h
    rw [← hn, Nat.not_lt] at h
    rw [KaratsubaHelperProg_time hb, ← hn, ← hn']
    · have : (((3 : ℕ ) ^ (Nat.clog 2 (n - 2)) : ℕ) : ℝ) ≤
        (((3 : ℕ) ^ (1 + log 2 (n-2)) : ℕ) : ℝ) := by
          rw [Nat.cast_le]
          apply Nat.pow_le_pow_right (n:= 3) (by simp) (clog_le_add_one_log_base_two (n - 2))
      apply le_trans this
      rw [Nat.add_comm 1, Nat.pow_add_one]
      simp only [cast_mul, cast_pow, cast_ofNat]
      rw [mul_comm _ 3]
      apply mul_le_mul (a:= 3) (b:= 3) (by simp) ?_ (by simp) (by simp)
      have : (3 : ℝ) ^ (log 2 (n-2)) ≤ (3 : ℝ) ^ (log 2 n) := by
        refine (Real.pow_le_iff_le_log (by simp) (by simp)).mpr ?_
        simp only [Real.log_pow]
        refine (mul_le_mul_iff_of_pos_right (by positivity)).mpr ?_
        rw [Nat.cast_le]
        refine log_mono (by simp) (by simp) (by simp)
      apply le_trans this
      conv =>
        lhs
        rw [← Real.rpow_logb (b:= 2) (x:=3) (by simp) (by simp) (by simp),
          ← Real.rpow_natCast, ← Real.rpow_mul (by simp),
            ← Real.natFloor_logb_natCast, mul_comm, Real.rpow_mul (by simp)]
      apply Real.rpow_le_rpow (by simp) ?_ (le_of_lt (Real.logb_pos (by simp) (by simp)))
      apply le_trans (b := 2 ^ (Real.logb 2 n))
      · refine (Real.rpow_le_rpow_left_iff (by simp)).mpr ?_
        apply le_trans (Nat.floor_le ?_)
        · simp
        · apply Real.logb_nonneg (by simp) (one_le_cast.mpr h)
      rw [Real.rpow_logb (by simp) (by simp)]
      exact cast_pos'.mpr h
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

end time

end Algolean.Algorithms
