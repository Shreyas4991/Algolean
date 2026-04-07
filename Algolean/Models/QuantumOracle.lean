/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.BitOps
public import Algolean.QueryModel
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Analysis.Complex.Trigonometric

@[expose] public section

/-!
# Quantum Oracle Query Model

A query model for quantum oracle complexity. Programs are sequences of
quantum gates and oracle queries, evaluated deterministically on pure
state vectors. Measurement is applied only at the end, outside the
program.

## Main definitions

- `QState`: Pure quantum state vector over `n` qubits.
- `QuantumQuery`: Query type returning state transformations (functions).
- `quantumModel`: Model assigning cost 1 to oracle queries and 0 to gates.
- `measureDistribution`: Born rule measurement distribution as a `PMF`.
- `QState.initial`: The all-zeros state `|0⟩^⊗n`.

## Design

Queries return functions `QState n → QState n` rather than carrying state
directly. This keeps `Prog` construction computable — the program is a
pure syntax tree of instructions. State threading is handled by a thin
wrapper `applyGate`, and noncomputability only enters during `Prog.eval`.

The oracle applies the phase kickback unitary `O_f : |x⟩ ↦ (-1)^{f(x)} |x⟩`.
The oracle function `f` is provided by the model, mirroring how the
comparison function `le` is provided by the sort model.
-/

namespace Algolean

namespace Algorithms

open Complex Prog Cslib

/-! ### Quantum state -/

/-- Amplitude vector over `n` qubits. -/
abbrev QState (n : ℕ) := Fin (2 ^ n) → ℂ

/-- A state is normalized when amplitudes squared sum to 1. -/
def QState.IsNormalized (s : QState n) : Prop :=
  ∑ i, normSq (s i) = 1

/-- The all-zeros computational basis state `|0⟩^⊗n`. -/
noncomputable def QState.initial (n : ℕ) : QState n :=
  fun i => if i = 0 then 1 else 0

theorem QState.initial_isNormalized :
    (QState.initial n).IsNormalized := by
  simp only [QState.IsNormalized, QState.initial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-! ### Gate implementations -/

/-- Hadamard gate on qubit `q`.
`H|0⟩ = (|0⟩ + |1⟩)/√2`, `H|1⟩ = (|0⟩ - |1⟩)/√2`. -/
noncomputable def gateHadamard (q : Fin n) : QState n → QState n :=
  fun s i =>
    let j := flipBit i q
    if getBit i q
    then (s j - s i) / ↑(Real.sqrt 2)
    else (s j + s i) / ↑(Real.sqrt 2)

/-- Pauli-X (NOT) gate on qubit `q`. Flips `|0⟩ ↔ |1⟩`. -/
def gatePauliX (q : Fin n) : QState n → QState n :=
  fun s i => s (flipBit i q)

/-- Pauli-Z gate on qubit `q`. `Z|0⟩ = |0⟩`, `Z|1⟩ = -|1⟩`. -/
noncomputable def gatePauliZ (q : Fin n) : QState n → QState n :=
  fun s i => if getBit i q then -s i else s i

/-- CNOT gate with given control and target qubits.
Flips the target when the control is `|1⟩`. -/
def gateCNOT (control target : Fin n) : QState n → QState n :=
  fun s i => if getBit i control then s (flipBit i target) else s i

/-- Phase gate `R(θ)` on qubit `q`.
`R(θ)|0⟩ = |0⟩`, `R(θ)|1⟩ = e^{iθ}|1⟩`. -/
noncomputable def gatePhase (q : Fin n) (θ : ℝ) : QState n → QState n :=
  fun s i => if getBit i q then Complex.exp (↑θ * I) * s i else s i

/-- Phase oracle for function `f`.
`O_f|x⟩ = (-1)^{f(x)}|x⟩`. -/
noncomputable def gateOracle (f : Fin (2 ^ n) → Bool) : QState n → QState n :=
  fun s i => if f i then -s i else s i

/-! ### Unitarity -/

/-- A quantum gate preserves norms: applying it does not change the
sum of squared amplitudes. For linear maps on finite-dimensional
state spaces this is equivalent to unitarity; when bridging to
QuantumInfo, each `IsUnitary` gate corresponds to a `𝐔[Fin (2^n)]`. -/
def IsUnitary (f : QState n → QState n) : Prop :=
  ∀ s : QState n, ∑ i, normSq (f s i) = ∑ i, normSq (s i)

/-- A unitary gate preserves normalization of quantum states. -/
theorem IsUnitary.preserves_normalized {f : QState n → QState n}
    (hf : IsUnitary f) {s : QState n}
    (hs : s.IsNormalized) : (f s).IsNormalized := by
  simp only [QState.IsNormalized] at *; rw [hf]; exact hs

/-- The identity gate is unitary. -/
theorem isUnitary_id : IsUnitary (id : QState n → QState n) :=
  fun _ => rfl

/-- Composition of unitary gates is unitary. -/
theorem IsUnitary.comp {f g : QState n → QState n}
    (hf : IsUnitary f) (hg : IsUnitary g) :
    IsUnitary (f ∘ g) :=
  fun s => by simp only [Function.comp]; rw [hf, hg]

/-! ### Gate unitarity -/

theorem gatePauliX_isUnitary (q : Fin n) : IsUnitary (gatePauliX q) := by
  intro s; unfold gatePauliX
  exact Finset.sum_nbij (fun i => flipBit i q)
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => by simpa using congr_arg (flipBit · q) h)
    (fun b _ => ⟨flipBit b q, Finset.mem_univ _, by simp⟩)
    (fun _ _ => rfl)

theorem gatePauliZ_isUnitary (q : Fin n) : IsUnitary (gatePauliZ q) := by
  intro s; unfold gatePauliZ
  exact Finset.sum_congr rfl fun i _ => by
    cases getBit i q <;> simp [normSq_neg]

theorem gatePhase_isUnitary (q : Fin n) (θ : ℝ) :
    IsUnitary (gatePhase q θ) := by
  intro s; unfold gatePhase
  exact Finset.sum_congr rfl fun i _ => by
    cases h : getBit i q
    · simp
    · simp only [ite_true]
      rw [map_mul]
      have : normSq (Complex.exp (↑θ * I)) = 1 := by
        rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
      rw [this]; ring

theorem gateOracle_isUnitary (f : Fin (2 ^ n) → Bool) :
    IsUnitary (gateOracle f) := by
  intro s; unfold gateOracle
  exact Finset.sum_congr rfl fun i _ => by
    cases f i <;> simp [normSq_neg]

/-- CNOT is unitary when control and target differ. When `c = t`,
the gate is a projection (sets bit `c` to 0) and does not preserve norms. -/
theorem gateCNOT_isUnitary (c t : Fin n) (hct : c ≠ t) :
    IsUnitary (gateCNOT c t) := by
  intro s; unfold gateCNOT
  let σ : Fin (2 ^ n) → Fin (2 ^ n) :=
    fun i => if getBit i c then flipBit i t else i
  have hσ_inv : ∀ i, σ (σ i) = i := fun i => by
    simp only [σ]
    cases h : getBit i c
    · simp [h]
    · simp [h, getBit_flipBit_ne i t c hct.symm, flipBit_flipBit]
  rw [show ∑ i, normSq (if getBit i c then s (flipBit i t) else s i) =
      ∑ i, normSq (s (σ i)) from
    Finset.sum_congr rfl fun i _ => by
      simp only [σ]; cases getBit i c <;> rfl]
  exact Finset.sum_nbij σ
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ hab => by
      have := congr_arg σ hab; rwa [hσ_inv, hσ_inv] at this)
    (fun b _ => ⟨σ b, Finset.mem_univ _, hσ_inv b⟩)
    (fun _ _ => rfl)

/-- `‖(a+b)/√2‖² + ‖(a-b)/√2‖² = ‖a‖² + ‖b‖²`. -/
private theorem normSq_hadamard_pair (a b : ℂ) :
    normSq ((b + a) / ↑(Real.sqrt 2)) +
    normSq ((a - b) / ↑(Real.sqrt 2)) = normSq a + normSq b := by
  simp only [normSq_div, normSq_ofReal,
    Real.mul_self_sqrt (show (2 : ℝ) ≥ 0 by norm_num), normSq_add, normSq_sub]
  have hre : (b * starRingEnd ℂ a).re = (a * starRingEnd ℂ b).re := by
    rw [show b * starRingEnd ℂ a = starRingEnd ℂ (a * starRingEnd ℂ b) from by
      simp [map_mul, mul_comm]]
    exact Complex.conj_re _
  field_simp
  linarith

theorem gateHadamard_isUnitary (q : Fin n) :
    IsUnitary (gateHadamard q) := by
  intro s; unfold gateHadamard
  let F := Finset.univ.filter (fun i : Fin (2 ^ n) => getBit i q = false)
  let T := Finset.univ.filter (fun i : Fin (2 ^ n) => getBit i q = true)
  have hFT : Disjoint F T :=
    Finset.disjoint_filter.mpr fun _ _ h1 h2 => by simp_all
  have hunion : F ∪ T = Finset.univ := by
    ext i; simp only [F, T, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases getBit i q <;> simp
  have hmem : ∀ b, ∀ i ∈ Finset.univ.filter
      (fun i => getBit i q = b), flipBit i q ∈
      Finset.univ.filter (fun i => getBit i q = !b) := fun b i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [getBit_flipBit_self, hi]
  have flipBij (S₁ S₂ : Finset (Fin (2 ^ n)))
      (h₁ : ∀ i ∈ S₁, flipBit i q ∈ S₂) (h₂ : ∀ i ∈ S₂, flipBit i q ∈ S₁)
      (f : Fin (2 ^ n) → ℝ) : ∑ i ∈ S₁, f (flipBit i q) = ∑ i ∈ S₂, f i :=
    Finset.sum_nbij (flipBit · q) h₁
      (fun _ _ _ _ h => by simpa using congr_arg (flipBit · q) h)
      (fun b hb => ⟨flipBit b q, h₂ b hb, by simp⟩) (fun _ _ => rfl)
  rw [← hunion, Finset.sum_union hFT, Finset.sum_union hFT,
    show ∑ i ∈ T, _ = ∑ i ∈ F, normSq ((s i - s (flipBit i q)) / ↑(Real.sqrt 2)) from
      flipBij T F (hmem true) (hmem false) _ ▸
        Finset.sum_congr rfl fun i hi => by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          simp [hi, flipBit_flipBit],
    show ∑ i ∈ F, _ = ∑ i ∈ F, normSq ((s (flipBit i q) + s i) / ↑(Real.sqrt 2)) from
      Finset.sum_congr rfl fun i hi => by
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hi; simp [hi],
    ← Finset.sum_add_distrib,
    show ∑ i ∈ F, _ = ∑ i ∈ F, (normSq (s i) + normSq (s (flipBit i q))) from
      Finset.sum_congr rfl fun i _ => normSq_hadamard_pair (s i) (s (flipBit i q)),
    Finset.sum_add_distrib]
  congr 1; exact flipBij F T (hmem false) (hmem true) (normSq ∘ s)

/-! ### Gates preserve normalization -/

theorem gatePauliX_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gatePauliX q s).IsNormalized :=
  (gatePauliX_isUnitary q).preserves_normalized hs

theorem gatePauliZ_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gatePauliZ q s).IsNormalized :=
  (gatePauliZ_isUnitary q).preserves_normalized hs

theorem gatePhase_preserves (q : Fin n) (θ : ℝ) (s : QState n)
    (hs : s.IsNormalized) : (gatePhase q θ s).IsNormalized :=
  (gatePhase_isUnitary q θ).preserves_normalized hs

theorem gateCNOT_preserves (c t : Fin n) (hct : c ≠ t) (s : QState n)
    (hs : s.IsNormalized) : (gateCNOT c t s).IsNormalized :=
  (gateCNOT_isUnitary c t hct).preserves_normalized hs

theorem gateOracle_preserves (f : Fin (2 ^ n) → Bool) (s : QState n)
    (hs : s.IsNormalized) : (gateOracle f s).IsNormalized :=
  (gateOracle_isUnitary f).preserves_normalized hs

theorem gateHadamard_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gateHadamard q s).IsNormalized :=
  (gateHadamard_isUnitary q).preserves_normalized hs

/-! ### Query type -/

/-- Quantum oracle query type over `n` qubits. Each query returns a
state transformation `QState n → QState n`. Gates are free operations;
the oracle query is the counted resource. -/
inductive QuantumQuery (n : ℕ) : Type → Type where
  /-- Hadamard gate on a single qubit. -/
  | hadamard (qubit : Fin n) : QuantumQuery n (QState n → QState n)
  /-- Pauli-X (NOT) gate on a single qubit. -/
  | pauliX (qubit : Fin n) : QuantumQuery n (QState n → QState n)
  /-- Pauli-Z gate on a single qubit. -/
  | pauliZ (qubit : Fin n) : QuantumQuery n (QState n → QState n)
  /-- Controlled-NOT gate. -/
  | cnot (control target : Fin n) : QuantumQuery n (QState n → QState n)
  /-- Phase rotation gate. -/
  | phase (qubit : Fin n) (θ : ℝ) : QuantumQuery n (QState n → QState n)
  /-- Oracle query: applies the phase oracle `O_f`. -/
  | oracle : QuantumQuery n (QState n → QState n)

/-- Evaluate a single quantum gate given an oracle unitary. -/
noncomputable def evalGate (oracle : QState n → QState n) :
    QuantumQuery n (QState n → QState n) → QState n → QState n
  | .hadamard q => gateHadamard q
  | .pauliX q => gatePauliX q
  | .pauliZ q => gatePauliZ q
  | .cnot c t => gateCNOT c t
  | .phase q θ => gatePhase q θ
  | .oracle => oracle

/-- Apply a quantum gate to a state, threading state through `Prog`. -/
def applyGate (q : QuantumQuery n (QState n → QState n)) (s : QState n) :
    Prog (QuantumQuery n) (QState n) :=
  FreeM.liftBind q fun f => pure (f s)

@[simp]
theorem applyGate_eval (q : QuantumQuery n (QState n → QState n)) (s : QState n)
    (M : Model (QuantumQuery n) Cost) :
    (applyGate q s).eval M = M.evalQuery q s := by
  simp [applyGate]

@[simp]
theorem applyGate_time [AddZeroClass Cost] (q : QuantumQuery n (QState n → QState n))
    (s : QState n) (M : Model (QuantumQuery n) Cost) :
    (applyGate q s).time M = M.cost q := by
  simp [applyGate]

/-! ### Model -/

/-- Quantum oracle model parameterized by the oracle function `f`.
Gates are free (cost 0); oracle queries cost 1. -/
noncomputable def quantumModel (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Model (QuantumQuery n) ℕ where
  evalQuery
    | .hadamard q => gateHadamard q
    | .pauliX q => gatePauliX q
    | .pauliZ q => gatePauliZ q
    | .cnot c t => gateCNOT c t
    | .phase q θ => gatePhase q θ
    | .oracle => gateOracle f
  cost
    | .oracle => 1
    | _ => 0

@[simp]
theorem quantumModel_evalQuery_hadamard (q : Fin n) :
    (quantumModel n f).evalQuery (.hadamard q) = gateHadamard q := rfl

@[simp]
theorem quantumModel_evalQuery_oracle :
    (quantumModel n f).evalQuery .oracle = gateOracle f := rfl

@[simp]
theorem quantumModel_cost_hadamard (q : Fin n) :
    (quantumModel n f).cost (.hadamard q) = 0 := rfl

@[simp]
theorem quantumModel_cost_oracle :
    (quantumModel n f).cost (QuantumQuery.oracle) = 1 := rfl

/-! ### Measurement -/

/-- The measurement distribution of a normalized state as a `PMF`.
The Born rule assigns probability `‖s j‖²` to each outcome `j`. -/
noncomputable def measureDistribution (s : QState n)
    (hs : s.IsNormalized) : PMF (Fin (2 ^ n)) :=
  ⟨fun j => ENNReal.ofReal (normSq (s j)), by
    have hfin := hasSum_fintype (fun j => ENNReal.ofReal (normSq (s j)))
    rwa [show ∑ j, ENNReal.ofReal (normSq (s j)) =
      ENNReal.ofReal (∑ j, normSq (s j)) from
        (ENNReal.ofReal_sum_of_nonneg fun _ _ => normSq_nonneg _).symm,
      hs, ENNReal.ofReal_one] at hfin⟩

/-! ### Helpers -/

/-- Apply Hadamard to qubits `k, k+1, ..., n-1`. -/
def hadamardFrom (k : ℕ) (s : QState n) : Prog (QuantumQuery n) (QState n) :=
  if h : k < n then do
    let s' ← applyGate (.hadamard ⟨k, h⟩) s
    hadamardFrom (k + 1) s'
  else
    pure s

/-- Apply Hadamard to all qubits sequentially. -/
def hadamardAll (s : QState n) : Prog (QuantumQuery n) (QState n) :=
  hadamardFrom 0 s

end Algorithms

end Algolean
