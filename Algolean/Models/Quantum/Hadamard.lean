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
  classical
  induction k generalizing n x y with
  | zero =>
      by_cases hxy : x = y
      · subst y
        simp [hadamardsUpToUnitary]
        intro i _
        rfl
      · have hnot : ¬ agreeFrom 0 x y := by
          intro h
          apply hxy
          ext i
          exact congrArg Fin.val (h i (Nat.zero_le i.val))
        simp [hadamardsUpToUnitary, hxy]
        exact hnot
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
          let q : Fin (n + 1) := ⟨k, Nat.lt_of_succ_le hk⟩
          let z₀ : Fin (n + 1) → Fin 2 := Function.update x q (y q)
          have hrem_z₀ :
              Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z₀ := by
            ext i
            simp [z₀, Fin.removeNth]
          have hz₀_before : zeroBefore k z₀ := by
            intro i hi
            have hiq : i ≠ q := by
              intro h
              have hval : i.val = k := by
                simpa [q] using congrArg Fin.val h
              omega
            dsimp [z₀]
            rw [Function.update_of_ne hiq]
            exact hx i (Nat.lt_trans hi (Nat.lt_succ_self k))
          have hagree_z₀ :
              agreeFrom k z₀ y ↔ agreeFrom (k + 1) x y := by
            constructor
            · intro h i hi
              have hiq : i ≠ q := by
                intro hiq
                have hval : i.val = k := by
                  simpa [q] using congrArg Fin.val hiq
                omega
              have hz₀i : z₀ i = x i := by
                dsimp [z₀]
                rw [Function.update_of_ne hiq]
              rw [← hz₀i]
              exact h i (Nat.le_trans (Nat.le_succ k) hi)
            · intro h i hi
              by_cases hiq : i = q
              · subst i
                simp [z₀]
              · have hz₀i : z₀ i = x i := by
                  dsimp [z₀]
                  rw [Function.update_of_ne hiq]
                rw [hz₀i]
                have hsucc : k + 1 ≤ i.val := by
                  have hne : i.val ≠ k := by
                    intro hval
                    apply hiq
                    ext
                    simp [q, hval]
                  omega
                exact h i hsucc
          have hz_eq_z₀ {z : Fin (n + 1) → Fin 2}
              (hrem :
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                  Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z)
              (hzagree : agreeFrom k z y) :
              z = z₀ := by
            ext i
            by_cases hiq : i = q
            · subst i
              have hzq : z q = y q := hzagree q (by simp [q])
              simp [z₀, hzq]
            · rcases Fin.exists_succAbove_eq hiq with ⟨j, hj⟩
              have hremj := congr_fun hrem j
              have hzx : z i = x i := by
                simpa [Fin.removeNth, hj] using hremj.symm
              have hxz₀ : x i = z₀ i := by
                dsimp [z₀]
                rw [Function.update_of_ne hiq]
              exact congrArg Fin.val (hzx.trans hxz₀)
          have hxq : x q = 0 := hx q (by simp [q])
          simp only [hadamardsUpToUnitary]
          change ((embedQubitGate q Qubit.H).val *
              (hadamardsUpToUnitary k (Nat.le_of_succ_le hk)).val) x y =
            if agreeFrom (k + 1) x y then hadamardScale (k + 1) else 0
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single z₀]
          · have hgate :
                embedQubitGate q Qubit.H x z₀ = Qubit.H (x q) (z₀ q) := by
              rw [embedQubitGate_apply]
              simp [hrem_z₀]
            calc
              embedQubitGate q Qubit.H x z₀ *
                  hadamardsUpToUnitary k (Nat.le_of_succ_le hk) z₀ y
                  = Qubit.H (x q) (z₀ q) *
                      (if agreeFrom k z₀ y then hadamardScale k else 0) := by
                    rw [hgate, ih (Nat.le_of_succ_le hk) hz₀_before]
              _ = if agreeFrom (k + 1) x y then hadamardScale (k + 1) else 0 := by
                    by_cases h : agreeFrom (k + 1) x y
                    · have hz : agreeFrom k z₀ y := hagree_z₀.mpr h
                      simp [h, hz, hxq, z₀, hadamardScale_succ]
                    · have hz : ¬ agreeFrom k z₀ y := fun hz => h (hagree_z₀.mp hz)
                      simp [h, hz]
          · intro z _ hz_ne
            by_cases hrem :
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                  Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z
            · have hz_before : zeroBefore k z := by
                intro i hi
                have hiq : i ≠ q := by
                  intro h
                  have hval : i.val = k := by
                    simpa [q] using congrArg Fin.val h
                  omega
                rcases Fin.exists_succAbove_eq hiq with ⟨j, hj⟩
                have hremj := congr_fun hrem j
                have hzx : z i = x i := by
                  simpa [Fin.removeNth, hj] using hremj.symm
                rw [hzx]
                exact hx i (Nat.lt_trans hi (Nat.lt_succ_self k))
              have hnotagree : ¬ agreeFrom k z y := by
                intro hzagree
                exact hz_ne (hz_eq_z₀ hrem hzagree)
              rw [embedQubitGate_apply]
              simp [hrem, ih (Nat.le_of_succ_le hk) hz_before, hnotagree]
            · rw [embedQubitGate_apply]
              simp [hrem]
          · intro h
            exact absurd (Finset.mem_univ z₀) h

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
  classical
  induction k generalizing n x y with
  | zero =>
      by_cases hxy : x = y
      · subst y
        simp [hadamardsUpToUnitary]
        intro i _
        rfl
      · have hnot : ¬ agreeFrom 0 x y := by
          intro h
          apply hxy
          ext i
          exact congrArg Fin.val (h i (Nat.zero_le i.val))
        simp [hadamardsUpToUnitary, hxy]
        exact hnot
  | succ k ih =>
      cases n with
      | zero => omega
      | succ n =>
          let q : Fin (n + 1) := ⟨k, Nat.lt_of_succ_le hk⟩
          let z₀ : Fin (n + 1) → Fin 2 := Function.update x q (y q)
          have hrem_z₀ :
              Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z₀ := by
            ext i
            simp [z₀, Fin.removeNth]
          have hy_before : zeroBefore k y := by
            intro i hi
            exact hy i (Nat.lt_trans hi (Nat.lt_succ_self k))
          have hagree_z₀ :
              agreeFrom k z₀ y ↔ agreeFrom (k + 1) x y := by
            constructor
            · intro h i hi
              have hiq : i ≠ q := by
                intro hiq
                have hval : i.val = k := by
                  simpa [q] using congrArg Fin.val hiq
                omega
              have hz₀i : z₀ i = x i := by
                dsimp [z₀]
                rw [Function.update_of_ne hiq]
              rw [← hz₀i]
              exact h i (Nat.le_trans (Nat.le_succ k) hi)
            · intro h i hi
              by_cases hiq : i = q
              · subst i
                simp [z₀]
              · have hz₀i : z₀ i = x i := by
                  dsimp [z₀]
                  rw [Function.update_of_ne hiq]
                rw [hz₀i]
                have hsucc : k + 1 ≤ i.val := by
                  have hne : i.val ≠ k := by
                    intro hval
                    apply hiq
                    ext
                    simp [q, hval]
                  omega
                exact h i hsucc
          have hz_eq_z₀ {z : Fin (n + 1) → Fin 2}
              (hrem :
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                  Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z)
              (hzagree : agreeFrom k z y) :
              z = z₀ := by
            ext i
            by_cases hiq : i = q
            · subst i
              have hzq : z q = y q := hzagree q (by simp [q])
              simp [z₀, hzq]
            · rcases Fin.exists_succAbove_eq hiq with ⟨j, hj⟩
              have hremj := congr_fun hrem j
              have hzx : z i = x i := by
                simpa [Fin.removeNth, hj] using hremj.symm
              have hxz₀ : x i = z₀ i := by
                dsimp [z₀]
                rw [Function.update_of_ne hiq]
              exact congrArg Fin.val (hzx.trans hxz₀)
          have hyq : y q = 0 := hy q (by simp [q])
          simp only [hadamardsUpToUnitary]
          change ((embedQubitGate q Qubit.H).val *
              (hadamardsUpToUnitary k (Nat.le_of_succ_le hk)).val) x y =
            if agreeFrom (k + 1) x y then hadamardScale (k + 1) else 0
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single z₀]
          · have hgate :
                embedQubitGate q Qubit.H x z₀ = Qubit.H (x q) (z₀ q) := by
              rw [embedQubitGate_apply]
              simp [hrem_z₀]
            calc
              embedQubitGate q Qubit.H x z₀ *
                  hadamardsUpToUnitary k (Nat.le_of_succ_le hk) z₀ y
                  = Qubit.H (x q) (z₀ q) *
                      (if agreeFrom k z₀ y then hadamardScale k else 0) := by
                    rw [hgate, ih (Nat.le_of_succ_le hk) hy_before]
              _ = if agreeFrom (k + 1) x y then hadamardScale (k + 1) else 0 := by
                    by_cases h : agreeFrom (k + 1) x y
                    · have hz : agreeFrom k z₀ y := hagree_z₀.mpr h
                      have hz' : agreeFrom k (Function.update x q 0) y := by
                        simpa [z₀, hyq] using hz
                      simp [h, hz', hyq, z₀, hadamardScale_succ]
                    · have hz : ¬ agreeFrom k z₀ y := fun hz => h (hagree_z₀.mp hz)
                      simp [h, hz]
          · intro z _ hz_ne
            by_cases hrem :
                Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q x =
                  Fin.removeNth (α := fun _ : Fin (n + 1) => Fin 2) q z
            · have hnotagree : ¬ agreeFrom k z y := by
                intro hzagree
                exact hz_ne (hz_eq_z₀ hrem hzagree)
              rw [embedQubitGate_apply]
              simp [hrem, ih (Nat.le_of_succ_le hk) hy_before, hnotagree]
            · rw [embedQubitGate_apply]
              simp [hrem]
          · intro h
            exact absurd (Finset.mem_univ z₀) h

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
