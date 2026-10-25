/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Algorithms.Quantum.BoolFun
public import Algolean.Algorithms.Quantum.HadamardLayer

/-!
# Deutsch–Jozsa algorithm

Deutsch–Jozsa decides with no error whether a function `f : {0,1}ⁿ → Bool`, promised to be
constant or balanced, is constant. The program applies a Hadamard layer, makes one oracle call,
applies a second Hadamard layer, measures the register, and returns whether the outcome is all
zeros. Before the measurement, the amplitude of `|0…0⟩` is `(1/2^n) ∑ₓ (−1)^{f(x)}`, which is `±1`
for constant `f` and `0` for balanced `f`.

## Main definitions

- `deutschJozsaPrepare n`, `deutschJozsa n`: the preparation and decision programs.
- `deutschJozsaKet n f`: the state before measurement.
- `deutschJozsaOutput n f`: the distribution of the returned answer.

## Main results

- `deutschJozsa_spec`: a `Std.Do` triple: from `|0…0⟩`, under the promise, every possible answer
  is `decide (IsConstant f)`.
- `deutschJozsaPrepare_spec`: a `Std.Do` triple for the state before measurement.
- `deutschJozsaOutput_eq_pure`: under the promise, the answer distribution is the point mass at
  the correct answer.
- `deutschJozsa_cost`: every run makes exactly one oracle call.
- `deutschJozsa_correct`: under the promise, every possible answer is `true` exactly when `f` is
  constant.

## References

* D. Deutsch, R. Jozsa, *Rapid solution of problems by quantum computation*, Proc. R. Soc.
  Lond. A 439 (1992).
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Complex Std.Do
open scoped MState ComplexOrder

noncomputable section

/-! ### Program and readout -/

/-- The all-zero computational-basis register state. -/
def zeroState (n : ℕ) : QState n := MState.pure (Ket.basis 0)

/-- The sign contributed to a basis state by the phase oracle. -/
def oracleSign {n : ℕ} (f : (Fin n → Fin 2) → Bool) (x : Fin n → Fin 2) : ℂ :=
  if f x then -1 else 1

/-- The phase oracle between two Hadamard layers, `H^⊗n · O_f · H^⊗n`, used by Deutsch–Jozsa. -/
def hadamardOracleUnitary (n : ℕ) (f : (Fin n → Fin 2) → Bool) : 𝐔[Fin n → Fin 2] :=
  hadamardsUnitary n * gateOracle f * hadamardsUnitary n

/-- The measurement-free part of Deutsch–Jozsa: one oracle call between two Hadamard layers. -/
def deutschJozsaPrepare (n : ℕ) : Prog (QuantumQuery n) Unit := do
  applyHadamards n
  applyGate .oracle
  applyHadamards n

/-- Deutsch–Jozsa: prepare the state, measure the register, and return whether the outcome is all
zeros. The answer `true` means constant. -/
def deutschJozsa (n : ℕ) : Prog (QuantumQuery n) Bool :=
  (fun x => decide (x = 0)) <$>
    (deutschJozsaPrepare n >>= fun _ => measureRegister n)

/-- The state before measurement, starting from `|0…0⟩`. -/
def deutschJozsaKet (n : ℕ) (f : (Fin n → Fin 2) → Bool) : Ket (Fin n → Fin 2) :=
  unitaryKet (hadamardOracleUnitary n f) (Ket.basis 0)

/-- The distribution of the answer returned by `deutschJozsa n`, run from `|0…0⟩`. -/
def deutschJozsaOutput (n : ℕ) (f : (Fin n → Fin 2) → Bool) : PMF Bool :=
  Prod.fst <$> ((deutschJozsa n).evalM (quantumModel n f)).run (zeroState n)

/-- The preparation stage contains no measurements. -/
theorem measurementFree_deutschJozsaPrepare (n : ℕ) :
    MeasurementFree (deutschJozsaPrepare n) := by
  exact (measurementFree_applyHadamards n).bind fun _ =>
    (measurementFree_applyGate .oracle).bind fun _ => measurementFree_applyHadamards n

/-- Under the deterministic semantics, the preparation stage conjugates the register by
`H^⊗n · O_f · H^⊗n`. -/
theorem deutschJozsaPrepare_evalM_unitaryModel (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((deutschJozsaPrepare n).evalM (unitaryModel n f)).run ρ =
      ((), hadamardOracleUnitary n f ◃ ρ) := by
  simp only [deutschJozsaPrepare, Prog.evalM_bind, StateT.run_bind,
    applyHadamards_evalM_unitaryModel, applyGate_evalM_unitaryModel,
    unitaryOf, hadamardOracleUnitary, MState.uConj_mul]
  rfl

/-- Run from `|0…0⟩` in the quantum model, the preparation stage leaves the register in the pure
state `deutschJozsaKet n f` with probability one. -/
theorem deutschJozsaPrepare_pure (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    ((deutschJozsaPrepare n).evalM (quantumModel n f)).run (zeroState n) =
      PMF.pure ((), MState.pure (deutschJozsaKet n f)) := by
  rw [evalM_quantumModel_of_measurementFree (measurementFree_deutschJozsaPrepare n),
    deutschJozsaPrepare_evalM_unitaryModel, zeroState, MState.uConj_pure, ← deutschJozsaKet]

/-- The three preparation actions send the zero state to `deutschJozsaKet`. -/
private theorem deutschJozsaPrepare_wp_result (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) (hρ : ρ = zeroState n) :
    hadamardsUnitary n ◃ (gateOracle f ◃ (hadamardsUnitary n ◃ ρ)) =
      MState.pure (deutschJozsaKet n f) := by
  rw [deutschJozsaKet, hadamardOracleUnitary, hρ, ← MState.uConj_mul,
    ← MState.uConj_mul, zeroState, MState.uConj_pure]

set_option linter.deprecated.syntax false in
/-- The state before measurement, as a `Std.Do` triple: from `|0…0⟩`, the preparation stage leaves
the register in `deutschJozsaKet n f`. -/
theorem deutschJozsaPrepare_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    letI := quantumWP n f
    ⦃fun ρ => ⌜ρ = zeroState n⌝⦄
      deutschJozsaPrepare n
    ⦃⇓ _ ρ => ⌜ρ = MState.pure (deutschJozsaKet n f)⌝⦄ := by
  mvcgen [deutschJozsaPrepare]
  case vc1 =>
    simp only [evolveState_eq]
    exact deutschJozsaPrepare_wp_result n f _ ‹_›

/-- The answer distribution is the measurement distribution of `deutschJozsaKet n f`, mapped
through the test `x = 0`. -/
theorem deutschJozsaOutput_eq_map_bornPMF (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaOutput n f =
      (bornPMF (measureRegisterPOVM n) (MState.pure (deutschJozsaKet n f))).map
        (fun x => decide (x = 0)) := by
  simp only [deutschJozsaOutput, deutschJozsa, Prog.evalM_map, StateT.run_map,
    Prog.evalM_bind, StateT.run_bind, deutschJozsaPrepare_pure]
  simp only [PMF.monad_map_eq_map, bind, PMF.pure_bind, measureRegister,
    Prog.evalM_lift, quantumModel_evalQuery_measureAll, measureRegisterM,
    StateT.run, PMF.map_comp, Function.comp_def]

/-! ### Zero-string measurement probability -/

/-- The oracle signs sum to `2^n − 2t`, where `t` is the number of marked inputs. -/
theorem sum_oracleSign {n : ℕ} (f : (Fin n → Fin 2) → Bool) :
    (∑ x, oracleSign f x) = (2 ^ n : ℂ) - 2 * markedCount f := by
  simp_rw [oracleSign]
  rw [sum_ite_marked]
  ring

/-- `(1/√2)^n · (1/√2)^n · 2^n = 1`. -/
theorem hadamardScale_mul_self_mul_card (n : ℕ) :
    hadamardScale n * hadamardScale n *
      (Fintype.card (Fin n → Fin 2) : ℂ) = 1 := by
  rw [← pow_two, hadamardScale_sq]
  simp

/-- Entries of `H^⊗n · O_f · H^⊗n`, as a signed sum over the middle index. -/
theorem hadamardOracleUnitary_apply (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (x y : Fin n → Fin 2) :
    hadamardOracleUnitary n f x y = hadamardScale n ^ 2 *
      ∑ z, oracleSign f z * (-1 : ℂ) ^
        ((∑ i, (x i).val * (z i).val) + ∑ i, (z i).val * (y i).val) := by
  simp only [hadamardOracleUnitary, Matrix.UnitaryGroup.mul_apply, Matrix.mul_apply,
    gateOracle_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [hadamardsUnitary_apply, oracleSign, pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

/-- The `(0, 0)` entry of `H^⊗n · O_f · H^⊗n` is `(1/2^n) ∑ₓ (−1)^{f(x)}`. -/
theorem hadamardOracleUnitary_zero_zero (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    hadamardOracleUnitary n f 0 0 =
      hadamardScale n * hadamardScale n * ∑ x, oracleSign f x := by
  simp [hadamardOracleUnitary_apply, pow_two]

/-- For balanced `f`, the oracle signs cancel. -/
theorem sum_oracleSign_eq_zero_of_isBalanced {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsBalanced f) :
    (∑ x, oracleSign f x) = 0 := by
  have h := isBalanced_iff.mp hf
  rw [sum_oracleSign]
  exact sub_eq_zero.mpr (by exact_mod_cast h.symm)

/-- For constant `f`, the oracle signs sum to `±2^n`. -/
theorem sum_oracleSign_of_isConstant {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsConstant f) :
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ (∑ x, oracleSign f x) = (2 ^ n : ℂ) * s := by
  rcases hf with ⟨b, hb⟩
  refine ⟨if b then (-1 : ℂ) else 1, ?_, ?_⟩
  · cases b <;> simp
  · simp [oracleSign, hb]

/-- The probability of answering `true` is `|U₀₀|²` for `U = H^⊗n · O_f · H^⊗n`. -/
theorem deutschJozsaOutput_true (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaOutput n f true =
      ENNReal.ofReal (Complex.normSq (hadamardOracleUnitary n f 0 0)) := by
  rw [deutschJozsaOutput_eq_map_bornPMF]
  have hcond (x : Fin n → Fin 2) : (true = decide (x = 0)) ↔ x = 0 := by simp
  simp only [PMF.map_apply, hcond, tsum_ite_eq, bornPMF_apply,
    measureRegisterPOVM_measure_pure_apply_coe, deutschJozsaKet,
    unitaryKet_basis_apply]

/-- Without any promise, the probability of answering `true` is `(1 − 2t/2^n)²`, where `t` is the
number of marked inputs. -/
theorem deutschJozsaOutput_true_eq_markedCount (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) :
    deutschJozsaOutput n f true =
      ENNReal.ofReal ((1 - 2 * (markedCount f : ℝ) / 2 ^ n) ^ 2) := by
  have h : hadamardOracleUnitary n f 0 0 =
      ((1 - 2 * (markedCount f : ℝ) / 2 ^ n : ℝ) : ℂ) := by
    rw [hadamardOracleUnitary_zero_zero, ← pow_two, hadamardScale_sq, sum_oracleSign]
    push_cast
    field_simp
  rw [deutschJozsaOutput_true, h, Complex.normSq_ofReal, pow_two]

/-- For balanced `f`, Deutsch–Jozsa answers `true` with probability `0`. -/
theorem deutschJozsaOutput_true_eq_zero_of_isBalanced {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsBalanced f) :
    deutschJozsaOutput n f true = 0 := by
  rw [deutschJozsaOutput_true, hadamardOracleUnitary_zero_zero,
    sum_oracleSign_eq_zero_of_isBalanced hf]
  simp

/-- For constant `f`, Deutsch–Jozsa answers `true` with probability `1`. -/
theorem deutschJozsaOutput_true_eq_one_of_isConstant {n : ℕ}
    {f : (Fin n → Fin 2) → Bool} (hf : IsConstant f) :
    deutschJozsaOutput n f true = 1 := by
  rw [deutschJozsaOutput_true, hadamardOracleUnitary_zero_zero]
  rcases sum_oracleSign_of_isConstant hf with ⟨s, hs, hsum⟩
  rw [hsum, ← mul_assoc, show (2 ^ n : ℂ) = Fintype.card (Fin n → Fin 2) by simp,
    hadamardScale_mul_self_mul_card, one_mul]
  rcases hs with rfl | rfl <;> simp

/-- Correctness of Deutsch–Jozsa: when `f` is constant or balanced, every answer with positive
probability is `true` exactly when `f` is constant. -/
theorem deutschJozsa_correct {n : ℕ} {f : (Fin n → Fin 2) → Bool}
    (hf : IsConstant f ∨ IsBalanced f) (b : Bool)
    (hb : b ∈ (deutschJozsaOutput n f).support) : b = true ↔ IsConstant f := by
  rcases hf with hc | hbal
  · have hsupport := (PMF.apply_eq_one_iff (deutschJozsaOutput n f) true).mp
      (deutschJozsaOutput_true_eq_one_of_isConstant hc)
    have hbtrue : b = true := by simpa only [hsupport, Set.mem_singleton_iff] using hb
    exact ⟨fun _ => hc, fun _ => hbtrue⟩
  · have hzero := deutschJozsaOutput_true_eq_zero_of_isBalanced hbal
    have hbfalse : b ≠ true := by
      intro h
      subst b
      exact hb hzero
    exact iff_of_false hbfalse (fun hc => not_isConstant_and_isBalanced f ⟨hc, hbal⟩)

/-- A probability-one outcome determines the entire distribution. -/
private theorem pmf_eq_pure_of_apply_eq_one {α : Type*} {p : PMF α} {a : α}
    (h : p a = 1) : p = PMF.pure a := by
  ext b
  by_cases hb : b = a
  · subst hb
    simp [h]
  · simp only [PMF.pure_apply, hb, ↓reduceIte]
    exact (PMF.apply_eq_zero_iff p b).mpr (by
      rw [(PMF.apply_eq_one_iff p a).mp h]
      exact hb)

/-- Under the promise, Deutsch–Jozsa answers deterministically: its answer distribution is the
point mass at `decide (IsConstant f)`. -/
theorem deutschJozsaOutput_eq_pure {n : ℕ} {f : (Fin n → Fin 2) → Bool}
    (hf : IsConstant f ∨ IsBalanced f) :
    deutschJozsaOutput n f = PMF.pure (decide (IsConstant f)) := by
  rcases hf with hc | hbal
  · rw [decide_eq_true hc]
    exact pmf_eq_pure_of_apply_eq_one (deutschJozsaOutput_true_eq_one_of_isConstant hc)
  · rw [decide_eq_false fun hc => not_isConstant_and_isBalanced f ⟨hc, hbal⟩]
    apply pmf_eq_pure_of_apply_eq_one
    simpa [tsum_bool, deutschJozsaOutput_true_eq_zero_of_isBalanced hbal] using
      (deutschJozsaOutput n f).tsum_coe

/-- Under the promise, every bitstring that measuring `deutschJozsaKet n f` can return gives the
correct answer. -/
theorem decide_eq_of_mem_support_deutschJozsaKet {n : ℕ} {f : (Fin n → Fin 2) → Bool}
    (hf : IsConstant f ∨ IsBalanced f) {x : Fin n → Fin 2}
    (hx : x ∈ (bornPMF (measureRegisterPOVM n) (MState.pure (deutschJozsaKet n f))).support) :
    decide (x = 0) = decide (IsConstant f) := by
  have hmem : decide (x = 0) ∈ (deutschJozsaOutput n f).support := by
    rw [deutschJozsaOutput_eq_map_bornPMF]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩
  rwa [deutschJozsaOutput_eq_pure hf, PMF.mem_support_pure_iff] at hmem

set_option linter.deprecated.syntax false in
/-- Correctness of Deutsch–Jozsa as a `Std.Do` triple: from `|0…0⟩`, under the promise, every
possible answer is `decide (IsConstant f)`. -/
theorem deutschJozsa_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (hf : IsConstant f ∨ IsBalanced f) :
    letI := quantumWP n f
    ⦃fun ρ => ⌜ρ = zeroState n⌝⦄
      deutschJozsa n
    ⦃⇓ b => ⌜b = decide (IsConstant f)⌝⦄ := by
  simp only [deutschJozsa, map_eq_pure_bind]
  mvcgen [deutschJozsaPrepare]
  case vc1 ρ hρ x _ hx =>
    simp only [evolveState_eq] at hx
    rw [unitaryOf, deutschJozsaPrepare_wp_result n f ρ hρ] at hx
    exact decide_eq_of_mem_support_deutschJozsaKet hf hx.1

/-! ### Query cost -/

/-- Monadic sequencing of distributions is `PMF.bind`. -/
private theorem pmf_bind {α β : Type} (p : PMF α) (k : α → PMF β) :
    p >>= k = p.bind k := rfl

/-- Monadic return of a value is its point mass. -/
private theorem pmf_pure {α : Type*} (a : α) : (Pure.pure a : PMF α) = PMF.pure a := rfl

/-- Preparation applies the circuit unitary with exactly one oracle call. -/
private theorem deutschJozsaPrepare_runM (n : ℕ) (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((deutschJozsaPrepare n).runM (quantumModel n f)).run.run ρ =
      PMF.pure ((⟨(), 1⟩ : AddWriter ℕ Unit),
        hadamardOracleUnitary n f ◃ ρ) := by
  simp only [deutschJozsaPrepare, Prog.runM_bind, AddWriterT.run_bind, StateT.run_bind,
    applyHadamards, applyHadamardsUpTo_runM, applyGate_runM, pmf_bind, PMF.pure_bind,
    StateT.run_pure, pmf_pure]
  simp only [hadamardOracleUnitary, quantumModel_cost_oracle, MState.uConj_mul, unitaryOf]
  rfl

/-- Measuring has zero cost and leaves the observed basis state. -/
private theorem measureRegister_runM (n : ℕ) (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((measureRegister n).runM (quantumModel n f)).run.run ρ =
      (bornPMF (measureRegisterPOVM n) ρ).map fun x =>
        ((⟨x, 0⟩ : AddWriter ℕ (Fin n → Fin 2)), MState.pure (Ket.basis x)) := by
  rw [measureRegister, Prog.runM_lift]
  simp only [ModelM.runQuery, AddWriterT.run_mk, StateT.run_map]
  simp only [quantumModel_evalQuery_measureAll, quantumModel_cost_measureAll,
    measureRegisterM, StateT.run, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]

/-- Deutsch–Jozsa costs one query. -/
theorem deutschJozsa_cost (n : ℕ) (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    Prod.fst <$> ((deutschJozsa n).costM (quantumModel n f)).run ρ = PMF.pure 1 := by
  rw [deutschJozsa, Prog.costM_map]
  simp only [Prog.costM, AddWriterT.cost, StateT.run_map, Prog.runM_bind,
    AddWriterT.run_bind, StateT.run_bind, deutschJozsaPrepare_runM, pmf_bind, PMF.pure_bind,
    measureRegister_runM, StateT.run_pure, pmf_pure, PMF.monad_map_eq_map, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_apply, Nat.add_zero]
  exact PMF.bind_const _ _

end

end Algolean.Algorithms
