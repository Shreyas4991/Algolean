/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Embed
public import QuantumInfo.Operators.Unitary

/-!
# Hadamard unitaries

The full-register Hadamard unitary `H^⊗n` and its entries.

`hadamardsUpToUnitary k` applies Hadamards to qubits `0, …, k − 1`. Proofs induct on `k`, using
`AgreeFrom` to track the qubits that are not yet transformed.

## Main definitions

- `hadamardsUnitary n`: the unitary `H^⊗n`.
- `hadamardScale k`: the normalization `(1/√2)^k`.
- `uniformKet n`: the uniform superposition `|s⟩`.

## Main results

- `hadamardsUnitary_apply`: the entries `(1/√2)^n · (−1)^{x·y}`.
- `hadamardsUnitary_mul_self`: `H^⊗n` is its own inverse.
- `unitaryKet_hadamardsUnitary_zero`: `H^⊗n |0…0⟩ = |s⟩`.
- `MState.uConj_one`, `MState.uConj_mul`, `MState.uConj_pure`: the unitary action on states.
-/

@[expose] public section

namespace Algolean.Algorithms

open Complex
open scoped MState ComplexOrder Matrix

noncomputable section

/-- Entries of the Hadamard gate: `(1/√2) · (−1)^{ab}`. -/
theorem _root_.Qubit.H_apply (a b : Fin 2) :
    Qubit.H a b = (√(1 / 2 : ℝ) : ℂ) * (-1 : ℂ) ^ (a.val * b.val) := by
  fin_cases a <;> fin_cases b <;> simp [Qubit.H]

/-- The action of a unitary on a ket: the matrix–vector product, which keeps the ket normalized. -/
def unitaryKet {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (ψ : Ket d) : Ket d where
  vec := U.val *ᵥ ψ.vec
  normalized' := by
    have hnorm : star (U.val *ᵥ ψ.vec) ⬝ᵥ (U.val *ᵥ ψ.vec) = 1 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        show U.val.conjTranspose * U.val = 1 from Matrix.UnitaryGroup.star_mul_self U,
        Matrix.one_mulVec]
      exact Braket.dot_self_eq_one ψ
    simp only [dotProduct, Pi.star_apply, RCLike.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum] at hnorm
    simp only [← Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_injective hnorm

/-- The vector of `U` applied to `ψ` is the matrix–vector product. -/
theorem unitaryKet_vec {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (ψ : Ket d) : (unitaryKet U ψ).vec = U.val *ᵥ ψ.vec := rfl

/-- The matrix of `U ◃ ρ` is `U ρ U†`. -/
theorem _root_.MState.uConj_m {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U : 𝐔[d]) : (U ◃ ρ).m = U.val * ρ.m * U.valᴴ :=
  HermitianMat.conj_apply_mat _ _

/-- The matrix of a pure state is the outer product `|ψ⟩⟨ψ|`. -/
theorem _root_.MState.pure_m {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    (MState.pure ψ).m = Matrix.vecMulVec ψ.vec (star ψ.vec) := rfl

/-- `U` applied to the basis ket `|b⟩` is column `b` of `U`. -/
@[simp]
theorem unitaryKet_basis_apply {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (b x : d) :
    unitaryKet U (Ket.basis b) x = U x b := by
  simp [Ket.apply, unitaryKet_vec, Ket.basis, Matrix.mulVec, dotProduct]

/-- Conjugating the pure state of `ψ` by `U` gives the pure state of `U` applied to `ψ`. -/
theorem _root_.MState.uConj_pure {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (ψ : Ket d) :
    U ◃ MState.pure ψ = MState.pure (unitaryKet U ψ) := by
  apply MState.ext_m
  rw [MState.uConj_m, MState.pure_m, MState.pure_m, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, unitaryKet_vec, Matrix.star_mulVec]

/-- Conjugating by the identity leaves a state unchanged. -/
@[simp] theorem _root_.MState.uConj_one {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) : (1 : 𝐔[d]) ◃ ρ = ρ := by
  ext1
  simp [MState.uConj]

/-- Conjugating by `U * V` conjugates by `V`, then by `U`. -/
theorem _root_.MState.uConj_mul {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U V : 𝐔[d]) : (U * V) ◃ ρ = U ◃ (V ◃ ρ) := by
  ext1
  simpa [MState.uConj] using (HermitianMat.conj_conj ρ.M V.val U.val).symm

/-- Entries of a single-qubit gate embedded at qubit `q`: zero unless the two bitstrings agree
away from `q`, and otherwise the gate's entry at their bits at `q`. -/
@[simp]
theorem embedQubitGate_apply {n : ℕ} (q : Fin (n + 1)) (U : 𝐔[Qubit])
    (x y : Fin (n + 1) → Fin 2) :
    embedQubitGate q U x y =
      if Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
          Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q y then
        U (x q) (y q)
      else
        0 := by
  by_cases h :
        Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
        Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q y <;>
    simp [embedQubitGate, unitaryReindex, h]

/-- On a register of any size, left multiplication by a gate on `q` combines the rows of `A`
obtained by changing that qubit, with coefficients from the gate's matrix. -/
theorem embedQubitGate_mul_apply {n : ℕ} (q : Fin n) (U : 𝐔[Qubit])
    (A : 𝐔[Fin n → Fin 2]) (x y : Fin n → Fin 2) :
    (embedQubitGate q U * A) x y =
      ∑ b : Fin 2, U (x q) b * A (Function.update x q b) y := by
  cases n with
  | zero => exact q.elim0
  | succ n =>
    rw [Matrix.UnitaryGroup.mul_apply, Matrix.mul_apply,
      ← (Fin.insertNthEquiv (fun _ => Fin 2) q).sum_comp
        (fun z => embedQubitGate q U x z * A z y),
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.sum_eq_single (Fin.removeNth q x)]
    · simp [Fin.insertNthEquiv, embedQubitGate_apply, Fin.insertNth_removeNth]
    · intro w hw
      simp [Fin.insertNthEquiv, embedQubitGate_apply, Ne.symm hw]

/-- `x` and `y` agree on qubits `k, k + 1, …`. -/
def AgreeFrom {n : ℕ} (k : ℕ) (x y : Fin n → Fin 2) : Prop :=
  ∀ i : Fin n, k ≤ i.val → x i = y i

/-- Agreement from qubit `k` on is decidable. -/
instance instDecidableAgreeFrom {n : ℕ} (k : ℕ) (x y : Fin n → Fin 2) :
    Decidable (AgreeFrom k x y) :=
  inferInstanceAs (Decidable (∀ i : Fin n, k ≤ i.val → x i = y i))

/-- Overwriting qubit `k` of `x` with `y`'s bit there turns agreement from `k + 1` into agreement
from `k`. -/
theorem agreeFrom_update_self {n k : ℕ} {x y : Fin n → Fin 2} {q : Fin n}
    (hq : q.val = k) :
    AgreeFrom k (Function.update x q (y q)) y ↔ AgreeFrom (k + 1) x y := by
  constructor
  · intro h i hi
    have hiq : i ≠ q := Fin.ne_of_val_ne (by omega)
    rw [← Function.update_of_ne hiq (y q) x]; exact h i (by omega)
  · intro h i hi
    rcases eq_or_ne i q with rfl | hiq
    · rw [Function.update_self]
    · have := Fin.val_ne_of_ne hiq
      rw [Function.update_of_ne hiq]; exact h i (by omega)

/-- Setting qubit `k` of `x` to a bit different from `y`'s breaks agreement from `k`. -/
theorem not_agreeFrom_update {n k : ℕ} {x y : Fin n → Fin 2} {q : Fin n}
    {b : Fin 2} (hq : q.val = k) (hb : b ≠ y q) :
    ¬ AgreeFrom k (Function.update x q b) y := fun h => by
  have hbq := h q hq.ge; rw [Function.update_self] at hbq; exact hb hbq

/-- The normalization `(1/√2)^k` of a product of `k` Hadamard gates. -/
def hadamardScale (k : ℕ) : ℂ :=
  (√(1 / 2 : ℝ) : ℂ) ^ k

/-- `hadamardScale 0 = 1`. -/
@[simp]
theorem hadamardScale_zero : hadamardScale 0 = 1 := rfl

/-- `hadamardScale (k + 1) = (1/√2) · hadamardScale k`. -/
@[simp]
theorem hadamardScale_succ (k : ℕ) :
    hadamardScale (k + 1) =
      (√(1 / 2 : ℝ) : ℂ) * hadamardScale k := by
  simp [hadamardScale, pow_succ, mul_comm]

/-- The product of Hadamard gates on qubits `0, …, k − 1`. -/
def hadamardsUpToUnitary {n : ℕ} :
    (k : ℕ) → k ≤ n → 𝐔[Fin n → Fin 2]
  | 0, _ => 1
  | k + 1, hk =>
    embedQubitGate ⟨k, Nat.lt_of_succ_le hk⟩ Qubit.H *
      hadamardsUpToUnitary k (Nat.le_of_succ_le hk)

/-- The full-register Hadamard unitary `H^⊗n`. -/
def hadamardsUnitary (n : ℕ) :
    𝐔[Fin n → Fin 2] :=
  hadamardsUpToUnitary n (Nat.le_refl n)

/-- The number of qubits below `k` at which both `x` and `y` are `1`: the sign exponent of a partial
Hadamard layer. -/
def hadamardExponentUpTo {n : ℕ} (k : ℕ) (x y : Fin n → Fin 2) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), (x i).val * (y i).val

/-- Changing a qubit at or beyond `k` leaves the exponent below `k` unchanged. -/
private theorem hadamardExponentUpTo_update {n k : ℕ} (x y : Fin n → Fin 2)
    (q : Fin n) (hq : k ≤ q.val) (b : Fin 2) :
    hadamardExponentUpTo k (Function.update x q b) y = hadamardExponentUpTo k x y := by
  apply Finset.sum_congr rfl
  intro i hi
  have hiq : i ≠ q := Fin.ne_of_val_ne (by
    have := (Finset.mem_filter.mp hi).2
    omega)
  rw [Function.update_of_ne hiq]

/-- Extending the exponent from `k` to `k + 1` adds the contribution of qubit `k`. -/
private theorem hadamardExponentUpTo_succ {n k : ℕ} (x y : Fin n → Fin 2)
    (q : Fin n) (hq : q.val = k) :
    hadamardExponentUpTo (k + 1) x y =
      (x q).val * (y q).val + hadamardExponentUpTo k x y := by
  have hs : Finset.univ.filter (fun i : Fin n => i.val < k + 1) =
      insert q (Finset.univ.filter (fun i : Fin n => i.val < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff, hq]
    omega
  have hqnot : q ∉ Finset.univ.filter (fun i : Fin n => i.val < k) := by simp [hq]
  simp only [hadamardExponentUpTo, hs, Finset.sum_insert hqnot]

/-- Entries of a partial Hadamard layer: zero unless `x` and `y` agree from `k` on, and otherwise
`hadamardScale k` times `−1` raised to the number of qubits below `k` at which both are `1`. -/
theorem hadamardsUpToUnitary_apply {n k : ℕ} (hk : k ≤ n)
    (x y : Fin n → Fin 2) :
    hadamardsUpToUnitary k hk x y =
      if AgreeFrom k x y then hadamardScale k * (-1 : ℂ) ^ hadamardExponentUpTo k x y
      else 0 := by
  induction k generalizing n x y with
  | zero =>
    have h0 : AgreeFrom 0 x y ↔ x = y :=
      ⟨fun h => funext fun i => h i (Nat.zero_le _), fun h _ _ => h ▸ rfl⟩
    simp [hadamardsUpToUnitary, hadamardExponentUpTo, Matrix.one_apply, h0]
  | succ k ih =>
    obtain _ | n := n
    · omega
    simp only [hadamardsUpToUnitary]
    set q : Fin (n + 1) := ⟨k, Nat.lt_of_succ_le hk⟩ with hq
    have hqk : q.val = k := by rw [hq]
    rw [embedQubitGate_mul_apply, Fintype.sum_eq_single (y q)]
    · rw [ih (Nat.le_of_succ_le hk)]
      by_cases h : AgreeFrom (k + 1) x y
      · have hp := (agreeFrom_update_self hqk).mpr h
        rw [ite_eq_left hp, ite_eq_left h, hadamardExponentUpTo_update x y q hqk.ge,
          Qubit.H_apply, hadamardExponentUpTo_succ x y q hqk, hadamardScale_succ,
          pow_add]
        ring
      · have hp : ¬ AgreeFrom k (Function.update x q (y q)) y :=
          fun hp => h ((agreeFrom_update_self hqk).mp hp)
        rw [ite_eq_right hp, ite_eq_right h, mul_zero]
    · intro b hb
      rw [ih (Nat.le_of_succ_le hk), ite_eq_right (not_agreeFrom_update hqk hb), mul_zero]

/-- Entries of `H^⊗n`: `(1/√2)^n · (−1)^{x·y}`, where `x·y = ∑ᵢ xᵢ yᵢ`. -/
theorem hadamardsUnitary_apply (n : ℕ) (x y : Fin n → Fin 2) :
    hadamardsUnitary n x y =
      hadamardScale n * (-1 : ℂ) ^ (∑ i, (x i).val * (y i).val) := by
  have hagree : AgreeFrom n x y := fun i hi => absurd hi (Nat.not_le_of_gt i.isLt)
  have hfilter : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp
  simpa [hadamardsUnitary, hagree, hadamardExponentUpTo, hfilter] using
    hadamardsUpToUnitary_apply (Nat.le_refl n) x y

/-- `H^⊗n` is self-adjoint. -/
@[simp]
theorem hadamardsUnitary_star (n : ℕ) : star (hadamardsUnitary n) = hadamardsUnitary n := by
  ext x y
  simp [Matrix.star_apply, hadamardsUnitary_apply, hadamardScale, mul_comm]

/-- `H^⊗n` is its own inverse. -/
@[simp]
theorem hadamardsUnitary_mul_self (n : ℕ) : hadamardsUnitary n * hadamardsUnitary n = 1 := by
  simpa only [hadamardsUnitary_star] using (Unitary.star_mul_self (hadamardsUnitary n))

/-- `hadamardScale n ^ 2 = 1/2^n`. -/
theorem hadamardScale_sq (n : ℕ) : hadamardScale n ^ 2 = (2 ^ n : ℂ)⁻¹ := by
  rw [hadamardScale, ← pow_mul, mul_comm, pow_mul, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num)]
  simp [one_div, inv_pow]

/-- `hadamardScale n = 1/√(2^n)`. -/
theorem hadamardScale_eq_inv_sqrt (n : ℕ) :
    hadamardScale n = ((√(2 ^ n : ℝ))⁻¹ : ℂ) := by
  have hs : √(1 / 2 : ℝ) = (√2)⁻¹ := by
    rw [one_div, Real.sqrt_inv]
  have hp : √(2 ^ n : ℝ) = (√2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  rw [hadamardScale, hs, hp, Complex.ofReal_inv, Complex.ofReal_pow, inv_pow]

/-- Row `0` of `H^⊗n` is constant, equal to `(1/√2)^n`. -/
@[simp]
theorem hadamardsUnitary_zero_left (n : ℕ) (y : Fin n → Fin 2) :
    hadamardsUnitary n 0 y = hadamardScale n := by
  simp [hadamardsUnitary_apply]

/-- Column `0` of `H^⊗n` is constant, equal to `(1/√2)^n`. -/
@[simp]
theorem hadamardsUnitary_zero_right (n : ℕ) (x : Fin n → Fin 2) :
    hadamardsUnitary n x 0 = hadamardScale n := by
  simp [hadamardsUnitary_apply]

/-- The uniform superposition `|s⟩`, with amplitude `1/√(2^n)` on every bitstring. -/
def uniformKet (n : ℕ) : Ket (Fin n → Fin 2) where
  vec := fun _ => hadamardScale n
  normalized' := by
    simpa only [← Ket.apply, unitaryKet_basis_apply, hadamardsUnitary_zero_right] using
      (unitaryKet (hadamardsUnitary n) (Ket.basis 0)).normalized'

/-- Every amplitude of the uniform superposition is `(1/√2)^n`. -/
@[simp]
theorem uniformKet_apply (n : ℕ) (x : Fin n → Fin 2) : uniformKet n x = hadamardScale n := rfl

/-- `H^⊗n` maps `|0…0⟩` to the uniform superposition. -/
theorem unitaryKet_hadamardsUnitary_zero (n : ℕ) :
    unitaryKet (hadamardsUnitary n) (Ket.basis 0) = uniformKet n := by
  apply Ket.ext
  intro x
  simp

end

end Algolean.Algorithms
