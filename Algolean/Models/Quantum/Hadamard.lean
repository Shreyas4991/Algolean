/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Oracle
public import Std.Tactic.Do

/-!
# Full-Register Hadamard Layers

Reusable helpers for applying Hadamard gates across an `n`-qubit register in
the quantum query model.

The program-level definitions live here rather than in individual algorithms
because the "Hadamard layer" pattern is shared by Deutsch-Jozsa,
Bernstein-Vazirani, Simon-style algorithms, and related oracle routines.
-/

@[expose] public section

noncomputable section

set_option mvcgen.warning false
attribute [local instance] Classical.propDecidable

namespace Algolean

namespace Algorithms

open Cslib Cslib.FreeM Std.Do
open scoped MState ComplexOrder

/-! ### Hadamard layers -/

/-- `x` is zero on qubits `0, ..., k - 1`. -/
def zeroBefore {n : ℕ} (k : ℕ) (x : Fin n → Fin 2) : Prop :=
  ∀ i : Fin n, i.val < k → x i = 0

/-- `x` and `y` agree on qubits `k, k + 1, ...`. -/
def agreeFrom {n : ℕ} (k : ℕ) (x y : Fin n → Fin 2) : Prop :=
  ∀ i : Fin n, k ≤ i.val → x i = y i

/-- Updating a zero-prefix tuple at a position `q` at or beyond the prefix
leaves it zero on the prefix. -/
theorem zeroBefore_update {n k : ℕ} {x : Fin n → Fin 2} {q : Fin n}
    (hq : k ≤ q.val) (hx : zeroBefore k x) (b : Fin 2) :
    zeroBefore k (Function.update x q b) := fun i hi => by
  have hiq : i ≠ q := Fin.ne_of_val_ne (by omega)
  rw [Function.update_of_ne hiq]; exact hx i hi

/-- Overwriting position `q` (at index `k`) with `y q` turns "agree from `k`"
into "agree from `k + 1`": position `k` then matches by construction. -/
theorem agreeFrom_update_self {n k : ℕ} {x y : Fin n → Fin 2} {q : Fin n}
    (hq : q.val = k) :
    agreeFrom k (Function.update x q (y q)) y ↔ agreeFrom (k + 1) x y := by
  constructor
  · intro h i hi
    have hiq : i ≠ q := Fin.ne_of_val_ne (by omega)
    rw [← Function.update_of_ne hiq (y q) x]; exact h i (by omega)
  · intro h i hi
    rcases eq_or_ne i q with rfl | hiq
    · rw [Function.update_self]
    · have := Fin.val_ne_of_ne hiq
      rw [Function.update_of_ne hiq]; exact h i (by omega)

/-- Overwriting position `q` (at index `k`) with a value other than `y q`
makes the tuples disagree at `k`, so they cannot "agree from `k`". -/
theorem not_agreeFrom_update {n k : ℕ} {x y : Fin n → Fin 2} {q : Fin n}
    {b : Fin 2} (hq : q.val = k) (hb : b ≠ y q) :
    ¬ agreeFrom k (Function.update x q b) y := fun h => by
  have hbq := h q hq.ge; rw [Function.update_self] at hbq; exact hb hbq

/-- Entry of a product of unitaries, as a sum over the shared index. -/
theorem unitaryGroup_mul_apply {d : Type*} [Fintype d] [DecidableEq d]
    (P Q : 𝐔[d]) (i j : d) :
    (P * Q) i j = ∑ k, P i k * Q k j := by
  rw [Submonoid.coe_mul, Matrix.mul_apply]

/-- Reading the `(x, y)` entry of `embedQubitGate q U * A` sums the gate over
the two possible values of qubit `q`, with the rest of the row fixed by `x`.
This is the workhorse for matrix entries of a Hadamard layer. -/
theorem embedQubitGate_mul_apply {n : ℕ} (q : Fin (n + 1)) (U : 𝐔[Qubit])
    (A : 𝐔[Fin (n + 1) → Fin 2]) (x y : Fin (n + 1) → Fin 2) :
    (embedQubitGate q U * A) x y =
      ∑ b : Fin 2, U (x q) b * A (Function.update x q b) y := by
  rw [unitaryGroup_mul_apply,
    ← (Fin.insertNthEquiv (fun _ => Fin 2) q).sum_comp
      (fun z => embedQubitGate q U x z * A z y),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single (Fin.removeNth q x)]
  · simp [Fin.insertNthEquiv, embedQubitGate_apply, Fin.insertNth_removeNth]
  · intro w _ hw
    simp [Fin.insertNthEquiv, embedQubitGate_apply, Ne.symm hw]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The positive scalar contributed by `k` Hadamard gates along a zero row
or column. -/
noncomputable def hadamardScale (k : ℕ) : ℂ :=
  (Real.sqrt (1 / 2 : ℝ) : ℂ) ^ k

@[simp]
theorem hadamardScale_zero : hadamardScale 0 = 1 := rfl

@[simp]
theorem hadamardScale_succ (k : ℕ) :
    hadamardScale (k + 1) =
      (Real.sqrt (1 / 2 : ℝ) : ℂ) * hadamardScale k := by
  simp [hadamardScale, pow_succ, mul_comm]

@[simp]
theorem qubit_H_zero_left (b : Fin 2) :
    Qubit.H 0 b = (Real.sqrt (1 / 2 : ℝ) : ℂ) := by
  fin_cases b <;> simp [Qubit.H]

@[simp]
theorem qubit_H_zero_right (b : Fin 2) :
    Qubit.H b 0 = (Real.sqrt (1 / 2 : ℝ) : ℂ) := by
  fin_cases b <;> simp [Qubit.H]

/-- The all-zero computational-basis state as a density matrix. -/
noncomputable def zeroRegisterState (n : ℕ) :
    MState (Fin n → Fin 2) :=
  MState.pure (Ket.basis 0)

/-- Apply Hadamards to qubits `0, ..., k - 1`, viewed as qubits of an
`n`-qubit register. -/
noncomputable def applyHadamardsUpTo {n : ℕ} :
    (k : ℕ) → k ≤ n → MState (Fin n → Fin 2) →
      Prog (QuantumQuery n) (MState (Fin n → Fin 2))
  | 0, _, ρ => pure ρ
  | k + 1, hk, ρ => do
      let ρ ← applyHadamardsUpTo k (Nat.le_of_succ_le hk) ρ
      applyGate (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) ρ

/-- The pure state transformer corresponding to `applyHadamardsUpTo`. -/
noncomputable def hadamardsUpToModelResult {n : ℕ} (M : Model (QuantumQuery n) Cost) :
    (k : ℕ) → k ≤ n → MState (Fin n → Fin 2) →
      MState (Fin n → Fin 2)
  | 0, _, ρ => ρ
  | k + 1, hk, ρ =>
      M.evalQuery (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) ◃
        hadamardsUpToModelResult M k (Nat.le_of_succ_le hk) ρ

/-- The quantum-model state transformer corresponding to `applyHadamardsUpTo`. -/
noncomputable def hadamardsUpToResult {n : ℕ} :
    (k : ℕ) → k ≤ n → MState (Fin n → Fin 2) →
      MState (Fin n → Fin 2)
  | 0, _, ρ => ρ
  | k + 1, hk, ρ =>
      embedQubitGate ⟨k, Nat.lt_of_succ_le hk⟩ Qubit.H ◃
        hadamardsUpToResult k (Nat.le_of_succ_le hk) ρ

/-- The product unitary denoted by `applyHadamardsUpTo`. -/
noncomputable def hadamardsUpToUnitary {n : ℕ} :
    (k : ℕ) → k ≤ n → 𝐔[Fin n → Fin 2]
  | 0, _ => 1
  | k + 1, hk =>
      embedQubitGate ⟨k, Nat.lt_of_succ_le hk⟩ Qubit.H *
        hadamardsUpToUnitary k (Nat.le_of_succ_le hk)

/-- Apply Hadamards to every qubit in the register. -/
noncomputable def applyHadamards {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) :=
  applyHadamardsUpTo n (Nat.le_refl n) ρ

/-- The pure state transformer corresponding to `applyHadamards`. -/
noncomputable def hadamardsModelResult {n : ℕ}
    (M : Model (QuantumQuery n) Cost)
    (ρ : MState (Fin n → Fin 2)) :
    MState (Fin n → Fin 2) :=
  hadamardsUpToModelResult M n (Nat.le_refl n) ρ

/-- The quantum-model state transformer corresponding to `applyHadamards`. -/
noncomputable def hadamardsResult {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) :
    MState (Fin n → Fin 2) :=
  hadamardsUpToResult n (Nat.le_refl n) ρ

/-- The full-register Hadamard unitary. -/
noncomputable def hadamardsUnitary (n : ℕ) :
    𝐔[Fin n → Fin 2] :=
  hadamardsUpToUnitary n (Nat.le_refl n)

@[simp]
theorem U_conj_one {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) :
    (1 : 𝐔[d]) ◃ ρ = ρ := by
  ext1
  simp [MState.U_conj]

theorem U_conj_mul {d : Type*} [Fintype d] [DecidableEq d]
    (ρ : MState d) (U V : 𝐔[d]) :
    (U * V) ◃ ρ = U ◃ (V ◃ ρ) := by
  ext1
  simpa [MState.U_conj] using
    (HermitianMat.conj_conj ρ.M V.val U.val).symm

@[simp]
theorem hadamardsUpToResult_eq_unitary {n k : ℕ} (hk : k ≤ n)
    (ρ : MState (Fin n → Fin 2)) :
    hadamardsUpToResult k hk ρ =
      hadamardsUpToUnitary k hk ◃ ρ := by
  induction k generalizing ρ with
  | zero =>
      simp [hadamardsUpToResult, hadamardsUpToUnitary]
  | succ k ih =>
      simp [hadamardsUpToResult, hadamardsUpToUnitary, ih, U_conj_mul]

@[simp]
theorem hadamardsResult_eq_unitary {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) :
    hadamardsResult ρ = hadamardsUnitary n ◃ ρ := by
  simp [hadamardsResult, hadamardsUnitary]

/-- Matrix entries of the first `k` Hadamards from a row that is zero on
those `k` qubits. The suffix not acted on by the gates must agree exactly. -/
theorem hadamardsUpToUnitary_zeroBefore_left {n k : ℕ} (hk : k ≤ n)
    {x y : Fin n → Fin 2} (hx : zeroBefore k x) :
    hadamardsUpToUnitary k hk x y =
      if agreeFrom k x y then hadamardScale k else 0 := by
  induction k generalizing n x y with
  | zero =>
    have h0 : agreeFrom 0 x y ↔ x = y :=
      ⟨fun h => funext fun i => h i (Nat.zero_le _), fun h _ _ => h ▸ rfl⟩
    simp [hadamardsUpToUnitary, Matrix.one_apply, h0]
  | succ k ih =>
    obtain _ | n := n
    · omega
    have hxk : zeroBefore k x := fun i hi => hx i (by omega)
    simp only [hadamardsUpToUnitary]
    set q : Fin (n + 1) := ⟨k, Nat.lt_of_succ_le hk⟩ with hq
    have hqk : (q : ℕ) = k := by rw [hq]
    rw [embedQubitGate_mul_apply, Finset.sum_eq_single (y q)]
    · rw [hx q (by omega), qubit_H_zero_left,
        ih (Nat.le_of_succ_le hk) (zeroBefore_update hqk.ge hxk (y q)),
        agreeFrom_update_self hqk]
      by_cases h : agreeFrom (k + 1) x y <;> simp [h, hadamardScale_succ]
    · intro b _ hb
      rw [ih (Nat.le_of_succ_le hk) (zeroBefore_update hqk.ge hxk b),
        if_neg (not_agreeFrom_update hqk hb), mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h

@[simp]
theorem hadamardsUnitary_zero_left (n : ℕ)
    (x : Fin n → Fin 2) :
    hadamardsUnitary n 0 x = hadamardScale n := by
  have hzero : zeroBefore n (0 : Fin n → Fin 2) := by
    intro i _
    rfl
  have hagree : agreeFrom n (0 : Fin n → Fin 2) x := by
    intro i hi
    exact absurd hi (Nat.not_le_of_gt i.isLt)
  simpa [hadamardsUnitary, hagree] using
    (hadamardsUpToUnitary_zeroBefore_left (Nat.le_refl n)
      (x := (0 : Fin n → Fin 2)) (y := x) hzero)

/-- Matrix entries of the first `k` Hadamards into a column that is zero on
those `k` qubits. The suffix not acted on by the gates must agree exactly. -/
theorem hadamardsUpToUnitary_zeroBefore_right {n k : ℕ} (hk : k ≤ n)
    {x y : Fin n → Fin 2} (hy : zeroBefore k y) :
    hadamardsUpToUnitary k hk x y =
      if agreeFrom k x y then hadamardScale k else 0 := by
  induction k generalizing n x y with
  | zero =>
    have h0 : agreeFrom 0 x y ↔ x = y :=
      ⟨fun h => funext fun i => h i (Nat.zero_le _), fun h _ _ => h ▸ rfl⟩
    simp [hadamardsUpToUnitary, Matrix.one_apply, h0]
  | succ k ih =>
    obtain _ | n := n
    · omega
    have hyk : zeroBefore k y := fun i hi => hy i (by omega)
    simp only [hadamardsUpToUnitary]
    set q : Fin (n + 1) := ⟨k, Nat.lt_of_succ_le hk⟩ with hq
    have hqk : (q : ℕ) = k := by rw [hq]
    rw [embedQubitGate_mul_apply, Finset.sum_eq_single (y q)]
    · rw [ih (Nat.le_of_succ_le hk) hyk, agreeFrom_update_self hqk,
        hy q (by omega), qubit_H_zero_right]
      by_cases h : agreeFrom (k + 1) x y <;> simp [h, hadamardScale_succ]
    · intro b _ hb
      rw [ih (Nat.le_of_succ_le hk) hyk, if_neg (not_agreeFrom_update hqk hb),
        mul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h

@[simp]
theorem hadamardsUnitary_zero_right (n : ℕ)
    (x : Fin n → Fin 2) :
    hadamardsUnitary n x 0 = hadamardScale n := by
  have hzero : zeroBefore n (0 : Fin n → Fin 2) := by
    intro i _
    rfl
  have hagree : agreeFrom n x (0 : Fin n → Fin 2) := by
    intro i hi
    exact absurd hi (Nat.not_le_of_gt i.isLt)
  simpa [hadamardsUnitary, hagree] using
    (hadamardsUpToUnitary_zeroBefore_right (Nat.le_refl n)
      (x := x) (y := (0 : Fin n → Fin 2)) hzero)

@[simp]
theorem hadamardsUpToModelResult_quantumModel {n k : ℕ} (hk : k ≤ n)
    (ρ : MState (Fin n → Fin 2)) (f : (Fin n → Fin 2) → Bool) :
    hadamardsUpToModelResult (quantumModel n f) k hk ρ =
      hadamardsUpToResult k hk ρ := by
  induction k generalizing ρ with
  | zero =>
      rfl
  | succ k ih =>
      simp only [hadamardsUpToModelResult, hadamardsUpToResult, quantumModel, unitaryOf]
      exact congrArg (fun σ => embedQubitGate ⟨k, Nat.lt_of_succ_le hk⟩ Qubit.H ◃ σ)
        (ih (Nat.le_of_succ_le hk) ρ)

@[simp]
theorem hadamardsModelResult_quantumModel {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) (f : (Fin n → Fin 2) → Bool) :
    hadamardsModelResult (quantumModel n f) ρ = hadamardsResult ρ := by
  simp [hadamardsModelResult, hadamardsResult]

@[simp]
theorem applyHadamardsUpTo_eval {n k : ℕ} (hk : k ≤ n)
    (ρ : MState (Fin n → Fin 2)) (M : Model (QuantumQuery n) Cost)
    (hM : ∀ q : Fin n, M.evalQuery (.hadamard q) = embedQubitGate q Qubit.H) :
    (applyHadamardsUpTo k hk ρ).eval M =
      hadamardsUpToResult k hk ρ := by
  induction k generalizing ρ with
  | zero =>
      rfl
  | succ k ih =>
      simp [applyHadamardsUpTo, hadamardsUpToResult, ih, hM]

@[simp]
theorem applyHadamards_eval {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) (M : Model (QuantumQuery n) Cost)
    (hM : ∀ q : Fin n, M.evalQuery (.hadamard q) = embedQubitGate q Qubit.H) :
    (applyHadamards ρ).eval M = hadamardsResult ρ := by
  simp [applyHadamards, hadamardsResult, applyHadamardsUpTo_eval, hM]

@[simp]
theorem applyHadamardsUpTo_liftM {n k : ℕ} (hk : k ≤ n)
    (ρ : MState (Fin n → Fin 2)) (M : Model (QuantumQuery n) Cost) :
    (applyHadamardsUpTo k hk ρ).liftM
        (fun {_} q => (M.evalQuery q : Id _)) =
      hadamardsUpToModelResult M k hk ρ := by
  induction k generalizing ρ with
  | zero =>
      rfl
  | succ k ih =>
      simp only [applyHadamardsUpTo, hadamardsUpToModelResult, FreeM.bind_eq_bind]
      calc
        (FreeM.bind (applyHadamardsUpTo k (Nat.le_of_succ_le hk) ρ)
            (fun ρ => applyGate (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) ρ)).liftM
            (fun {_} q => (M.evalQuery q : Id _))
            = (do
                let σ ← (applyHadamardsUpTo k (Nat.le_of_succ_le hk) ρ).liftM
                  (fun {_} q => (M.evalQuery q : Id _))
                (applyGate (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) σ).liftM
                  (fun {_} q => (M.evalQuery q : Id _))) := by
                exact FreeM.liftM_bind
                  (interp := fun {_} q => (M.evalQuery q : Id _))
                  (x := applyHadamardsUpTo k (Nat.le_of_succ_le hk) ρ)
                  (f := fun ρ => applyGate (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) ρ)
        _ = M.evalQuery (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩) ◃
              hadamardsUpToModelResult M k (Nat.le_of_succ_le hk) ρ := by
                rw [ih (Nat.le_of_succ_le hk) ρ]
                unfold applyGate
                rfl

@[simp]
theorem applyHadamards_liftM {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) (M : Model (QuantumQuery n) Cost) :
    (applyHadamards ρ).liftM (fun {_} q => (M.evalQuery q : Id _)) =
      hadamardsModelResult M ρ := by
  simp [applyHadamards, hadamardsModelResult, applyHadamardsUpTo_liftM]

namespace Spec

@[spec]
theorem applyHadamardsUpTo_spec [HasModel (QuantumQuery n) Cost]
    {k : ℕ} (hk : k ≤ n) (ρ : MState (Fin n → Fin 2))
    {Q : PostCond (MState (Fin n → Fin 2)) .pure} :
    Triple (Algorithms.applyHadamardsUpTo k hk ρ)
      (Q.1 (hadamardsUpToModelResult
        (HasModel.model : Model (QuantumQuery n) Cost) k hk ρ)) Q := by
  induction k generalizing ρ Q with
  | zero =>
      simpa [Algorithms.applyHadamardsUpTo, hadamardsUpToModelResult] using
        (pure_FreeM (F := QuantumQuery n) ρ (Q' := Q))
  | succ k ih =>
      simp only [Algorithms.applyHadamardsUpTo, hadamardsUpToModelResult]
      mvcgen [ih]

@[spec]
theorem applyHadamards_spec [HasModel (QuantumQuery n) Cost]
    (ρ : MState (Fin n → Fin 2))
    {Q : PostCond (MState (Fin n → Fin 2)) .pure} :
    Triple (Algorithms.applyHadamards ρ)
      (Q.1 (hadamardsModelResult
        (HasModel.model : Model (QuantumQuery n) Cost) ρ)) Q := by
  simpa [Algorithms.applyHadamards, hadamardsModelResult] using
    (applyHadamardsUpTo_spec (n := n) (Cost := Cost) (Nat.le_refl n) ρ (Q := Q))

end Spec

@[simp]
theorem applyHadamardsUpTo_time {n k : ℕ} [AddCommMonoid Cost]
    (hk : k ≤ n) (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) Cost)
    (hM : ∀ q : Fin n, M.cost (.hadamard q) = 0) :
    (applyHadamardsUpTo k hk ρ).time M = 0 := by
  induction k generalizing ρ with
  | zero =>
      rfl
  | succ k ih =>
      simp [applyHadamardsUpTo, ih, hM]

@[simp]
theorem applyHadamards_time {n : ℕ} [AddCommMonoid Cost]
    (ρ : MState (Fin n → Fin 2)) (M : Model (QuantumQuery n) Cost)
    (hM : ∀ q : Fin n, M.cost (.hadamard q) = 0) :
    (applyHadamards ρ).time M = 0 := by
  simp [applyHadamards, applyHadamardsUpTo_time, hM]

end Algorithms

end Algolean
