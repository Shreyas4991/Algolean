/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Hadamard
public import Std.Tactic.Do

/-!
# Deutsch-Jozsa Algorithm

The Deutsch-Jozsa query algorithm in the phase-oracle model. The program
starts in `|0...0⟩`, applies Hadamard gates to the whole register, queries
the phase oracle once, applies Hadamard gates again, and then measurement is
performed outside the program using `measureRegisterPOVM`.
-/

@[expose] public section

noncomputable section

set_option mvcgen.warning false

namespace Algolean

namespace Algorithms

open Cslib Cslib.FreeM Std.Do
open scoped MState ComplexOrder

/-! ### Program and readout -/

/-- The ±1 phase contributed by the Boolean phase oracle. -/
def oracleSign {n : ℕ} (f : (Fin n → Fin 2) → Bool)
    (x : Fin n → Fin 2) : ℂ :=
  if f x then (-1 : ℂ) else 1

/-- A Boolean oracle is constant when all inputs have the same value. -/
def IsConstant {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Prop :=
  ∃ b : Bool, ∀ x, f x = b

/-- A Boolean oracle is balanced when exactly half the inputs are true and
half are false. -/
def IsBalanced {n : ℕ} (f : (Fin n → Fin 2) → Bool) : Prop :=
  ((Finset.univ.filter fun x : Fin n → Fin 2 => f x).card =
    (Finset.univ.filter fun x : Fin n → Fin 2 => ¬ f x).card)

theorem oracleSign_sum_eq_zero_of_balanced {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsBalanced f) :
    (∑ x, oracleSign f x) = 0 := by
  classical
  calc
    (∑ x, oracleSign f x)
        = (∑ x ∈ (Finset.univ.filter (fun x : Fin n → Fin 2 => f x)), (-1 : ℂ)) +
            (∑ x ∈ (Finset.univ.filter (fun x : Fin n → Fin 2 => ¬ f x)), (1 : ℂ)) := by
          rw [← Finset.sum_filter_add_sum_filter_not
            (s := Finset.univ) (p := fun x : Fin n → Fin 2 => f x)
            (f := oracleSign f)]
          congr 1
          · apply Finset.sum_congr rfl
            intro x hx
            have hfx : f x = true := (Finset.mem_filter.mp hx).2
            simp [oracleSign, hfx]
          · apply Finset.sum_congr rfl
            intro x hx
            have hfx : f x = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hx).2
            simp [oracleSign, hfx]
    _ = 0 := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [hf]
          ring

theorem oracleSign_sum_of_constant {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsConstant f) :
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ (∑ x, oracleSign f x) =
      (Fintype.card (Fin n → Fin 2) : ℂ) * s := by
  classical
  rcases hf with ⟨b, hb⟩
  refine ⟨if b then (-1 : ℂ) else 1, ?_, ?_⟩
  · cases b <;> simp
  · simp [oracleSign, hb]

/-- Deutsch-Jozsa state-preparation program. Measurement is deliberately
outside the program, so this returns the final density matrix. -/
noncomputable def deutschJozsa (n : ℕ) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) := do
  let ρ ← applyHadamards (zeroRegisterState n)
  let ρ ← applyGate .oracle ρ
  applyHadamards ρ

/-- The final density matrix under a Boolean phase oracle `f`. -/
noncomputable def deutschJozsaState (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    MState (Fin n → Fin 2) :=
  (deutschJozsa n).eval (quantumModel n f)

/-- Full-register computational-basis measurement of the Deutsch-Jozsa output. -/
noncomputable def deutschJozsaDistribution (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    ProbDistribution (Fin n → Fin 2) :=
  (measureRegisterPOVM n).measure (deutschJozsaState n f)

/-- Probability that the full-register measurement returns the all-zero
bitstring, the textbook Deutsch-Jozsa acceptance condition for "constant". -/
noncomputable def deutschJozsaZeroProbability (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) : Prob :=
  deutschJozsaDistribution n f 0

/-- The denotational state transformer computed by the Deutsch-Jozsa program
under oracle `f`. -/
noncomputable def deutschJozsaResult (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    MState (Fin n → Fin 2) :=
  hadamardsResult (gateOracle f ◃ hadamardsResult (zeroRegisterState n))

@[simp]
theorem deutschJozsa_liftM (n : ℕ) (M : Model (QuantumQuery n) Cost) :
    (deutschJozsa n).liftM (fun {_} q => (M.evalQuery q : Id _)) =
      hadamardsModelResult M
        (M.evalQuery QuantumQuery.oracle ◃ hadamardsModelResult M (zeroRegisterState n)) := by
  unfold deutschJozsa
  simp only [FreeM.bind_eq_bind, FreeM.liftM_bind_id]
  simp

@[simp]
theorem deutschJozsa_liftM_quantumModel (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    (deutschJozsa n).liftM
        (fun {_} q => ((quantumModel n f).evalQuery q : Id _)) =
      deutschJozsaResult n f := by
  rw [deutschJozsa_liftM]
  simp [deutschJozsaResult]

@[simp]
theorem deutschJozsa_liftM_quantumModel_run (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    Id.run ((deutschJozsa n).liftM
        (fun {_} q => ((quantumModel n f).evalQuery q : Id _))) =
      deutschJozsaResult n f := by
  rw [deutschJozsa_liftM_quantumModel]
  rfl

private theorem deutschJozsa_wp_result (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    ((Cslib.FreeM.wpH (quantumModel n f).handler (deutschJozsa n)).apply
      (PostCond.noThrow fun ρ => ⌜ρ = deutschJozsaResult n f⌝)).down := by
  rw [(quantumModel n f).wp_eq_wp_interp (deutschJozsa n)]
  simp [wp, Id.run, deutschJozsaResult]

/-- Hoare-style correctness of the state-preparation program under the
oracle `f`, discharged through the query-model `mvcgen` interface. -/
theorem deutschJozsa_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    letI : HasModel (QuantumQuery n) ℕ := ⟨quantumModel n f⟩
    ⦃⌜True⌝⦄ deutschJozsa n
      ⦃⇓ ρ => ⌜ρ = deutschJozsaResult n f⌝⦄ := by
  letI : HasModel (QuantumQuery n) ℕ := ⟨quantumModel n f⟩
  mvcgen [deutschJozsa, Spec.applyHadamards_spec]
  exact deutschJozsa_wp_result n f

/-- Evaluation of the Deutsch-Jozsa program as a final density matrix. -/
theorem deutschJozsa_eval (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaState n f = deutschJozsaResult n f := by
  letI : HasModel (QuantumQuery n) ℕ := ⟨quantumModel n f⟩
  exact eval_of_triple (deutschJozsa_spec n f)

/-- The measured output distribution is the full-register measurement of the
state certified by `deutschJozsa_spec`. -/
theorem deutschJozsaDistribution_eval (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaDistribution n f =
      (measureRegisterPOVM n).measure (deutschJozsaResult n f) := by
  ext x
  simp [deutschJozsaDistribution, deutschJozsa_eval]

/-- The zero-string acceptance probability is computed by measuring the
state certified by `deutschJozsa_spec`. -/
theorem deutschJozsaZeroProbability_eval (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaZeroProbability n f =
      (measureRegisterPOVM n).measure (deutschJozsaResult n f) 0 := by
  simp [deutschJozsaZeroProbability, deutschJozsaDistribution_eval]

/-- Concrete acceptance-probability form: measuring the all-zero string reads
the all-zero diagonal entry of the final density matrix certified by
`deutschJozsa_spec`. -/
theorem deutschJozsaZeroProbability_coe (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    (deutschJozsaZeroProbability n f : ℝ) =
      ((deutschJozsaResult n f).m 0 0).re := by
  rw [deutschJozsaZeroProbability_eval]
  simp

/-! ### Zero-string measurement probability -/

/-- The concrete unitary denoted by the non-measurement Deutsch-Jozsa circuit. -/
noncomputable def deutschJozsaUnitary (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    𝐔[Fin n → Fin 2] :=
  (hadamardsUnitary n * gateOracle f) * hadamardsUnitary n

/-- The state transformer computed by the program is equivalently conjugation
by the product unitary `H O_f H` applied to the all-zero basis state. This
packages the two free Hadamard layers and the one oracle query into the usual
closed-form circuit unitary used for the measurement calculation. -/
theorem deutschJozsaResult_eq_unitary (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaResult n f =
      deutschJozsaUnitary n f ◃ zeroRegisterState n := by
  simp [deutschJozsaResult, deutschJozsaUnitary, U_conj_mul]

/-- Conjugating a computational-basis pure state by `U` produces the outer
product of the `b`-th column of `U`: the `(i,j)` entry is
`U i b * star (U j b)`. -/
theorem U_conj_pure_basis_apply {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (b i j : d) :
    (U ◃ MState.pure (Ket.basis b)).m i j =
      U i b * star (U j b) := by
  change ((MState.pure (Ket.basis b)).M.conj U.val).mat i j =
    U i b * star (U j b)
  rw [HermitianMat.conj_apply_mat]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, MState.pure,
    HermitianMat.mat_mk, Matrix.vecMulVec_apply, Ket.basis, Bra.eq_conj]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single b]
    · simp [Ket.apply]
    · intro x _ hx
      simp [Ket.apply, Ne.symm hx]
    · intro h
      exact absurd (Finset.mem_univ b) h
  · intro x _ hx
    simp [Ket.apply, Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- The all-zero amplitude of the Deutsch-Jozsa unitary is the normalized
signed sum of oracle phases. The two `hadamardScale n` factors are the first
and last Hadamard layers; `oracleSign f x` is the phase contributed by the
oracle on basis state `x`. -/
theorem deutschJozsaUnitary_zero_zero (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaUnitary n f 0 0 =
      hadamardScale n * hadamardScale n * ∑ x, oracleSign f x := by
  classical
  simp [deutschJozsaUnitary, Matrix.mul_apply, gateOracle_apply, hadamardScale,
    oracleSign, Finset.mul_sum, mul_assoc, mul_comm]

/-- The probability of measuring the all-zero string is the norm square of
the all-zero amplitude, hence the norm square of the normalized signed oracle
sum. This is the bridge from the `mvcgen`-certified final state to the
Deutsch-Jozsa decision rule. -/
theorem deutschJozsaZeroProbability_eq_normSq_signedSum (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    (deutschJozsaZeroProbability n f : ℝ) =
      Complex.normSq (hadamardScale n * hadamardScale n * ∑ x, oracleSign f x) := by
  rw [deutschJozsaZeroProbability_coe, deutschJozsaResult_eq_unitary]
  rw [zeroRegisterState, U_conj_pure_basis_apply, deutschJozsaUnitary_zero_zero]
  set z : ℂ := hadamardScale n * hadamardScale n * ∑ x, oracleSign f x
  rw [show z * star z = (Complex.normSq z : ℂ) by
    simpa [RCLike.star_def] using Complex.mul_conj z]
  simp

/-- The two zero-row Hadamard scale factors normalize the full register:
`(sqrt(1/2)^n)^2 * 2^n = 1`, with `2^n` written as the cardinality of
`Fin n → Fin 2`. -/
theorem hadamardScale_mul_self_mul_card (n : ℕ) :
    hadamardScale n * hadamardScale n *
      (Fintype.card (Fin n → Fin 2) : ℂ) = 1 := by
  let a : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)
  have ha : a * a = (1 / 2 : ℂ) := by
    have hs : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      rw [← sq, Real.sq_sqrt]
      norm_num
    dsimp [a]
    rw [← Complex.ofReal_mul, hs]
    norm_num
  have hpow : ∀ n : ℕ, a ^ n * a ^ n * (2 : ℂ) ^ n = 1 := by
    intro n
    induction n with
    | zero =>
        simp
    | succ n ih =>
        simp only [pow_succ]
        calc
          (a ^ n * a) * (a ^ n * a) * ((2 : ℂ) ^ n * 2)
              = (a * a * 2) * (a ^ n * a ^ n * (2 : ℂ) ^ n) := by
                ring
          _ = 1 := by
                rw [ih, ha]
                norm_num
  simpa [hadamardScale, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, a] using hpow n

/-- If the oracle is balanced, the signed oracle phases cancel, so the
all-zero measurement probability is zero. -/
theorem deutschJozsaZeroProbability_eq_zero_of_balanced {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsBalanced f) :
    (deutschJozsaZeroProbability n f : ℝ) = 0 := by
  rw [deutschJozsaZeroProbability_eq_normSq_signedSum,
    oracleSign_sum_eq_zero_of_balanced hf]
  simp

/-- If the oracle is constant, every oracle phase has the same sign. The
signed sum has magnitude equal to the register size, exactly canceling the
Hadamard normalization, so the all-zero measurement probability is one. -/
theorem deutschJozsaZeroProbability_eq_one_of_constant {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsConstant f) :
    (deutschJozsaZeroProbability n f : ℝ) = 1 := by
  rw [deutschJozsaZeroProbability_eq_normSq_signedSum]
  rcases oracleSign_sum_of_constant hf with ⟨s, hs, hsum⟩
  rw [hsum]
  have hscale := hadamardScale_mul_self_mul_card n
  have hamp :
      hadamardScale n * hadamardScale n *
          ((Fintype.card (Fin n → Fin 2) : ℂ) * s) = s := by
    calc
      hadamardScale n * hadamardScale n *
          ((Fintype.card (Fin n → Fin 2) : ℂ) * s)
          = (hadamardScale n * hadamardScale n *
              (Fintype.card (Fin n → Fin 2) : ℂ)) * s := by
              ring
      _ = s := by
              rw [hscale]
              simp
  rw [hamp]
  rcases hs with rfl | rfl <;> simp [Complex.normSq_neg]

/-- Deutsch-Jozsa makes exactly one oracle query; Hadamard gates are free in
the query-complexity cost model. -/
theorem deutschJozsa_time (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (deutschJozsa n).time (quantumModel n f) = 1 := by
  simp [deutschJozsa, quantumModel, applyHadamards_time]

end Algorithms

end Algolean
