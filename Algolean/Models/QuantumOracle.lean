/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

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

/-! ### Bit manipulation for qubit indexing -/

/-- Extract bit `q` from basis state index `i`. -/
def getBit (i : Fin (2 ^ n)) (q : Fin n) : Bool :=
  (i.val / 2 ^ q.val) % 2 = 1

/-- Flip bit `q` in basis state index `i`. -/
def flipBit (i : Fin (2 ^ n)) (q : Fin n) : Fin (2 ^ n) :=
  ⟨i.val ^^^ (2 ^ q.val), by
    apply Nat.xor_lt_two_pow
    · exact i.isLt
    · exact Nat.pow_lt_pow_right (by omega) q.isLt⟩

/-! ### Bit manipulation lemmas -/

@[simp]
theorem getBit_zero_zero (h : 0 < n) :
    getBit (0 : Fin (2 ^ n)) ⟨0, h⟩ = false := by
  simp [getBit]

/-- `getBit` of 0 is always false. -/
theorem getBit_zero_of (q : Fin n) :
    getBit (⟨0, by positivity⟩ : Fin (2 ^ n)) q = false := by
  simp [getBit]

/-- Flipping bit `q` twice is the identity. -/
@[simp]
theorem flipBit_flipBit (i : Fin (2 ^ n)) (q : Fin n) :
    flipBit (flipBit i q) q = i := by
  ext
  simp [flipBit, Nat.xor_assoc, Nat.xor_self]

/-- `flipBit` on different qubits commutes. -/
theorem flipBit_comm (i : Fin (2 ^ n)) (q₁ q₂ : Fin n) :
    flipBit (flipBit i q₁) q₂ = flipBit (flipBit i q₂) q₁ := by
  ext
  simp [flipBit, Nat.xor_assoc, Nat.xor_comm (2 ^ q₁.val)]

/-- `getBit` agrees with `Nat.testBit`. -/
theorem getBit_eq_testBit (i : Fin (2 ^ n)) (q : Fin n) :
    getBit i q = i.val.testBit q.val := by
  unfold getBit Nat.testBit
  simp only [Nat.shiftRight_eq_div_pow]
  have hmod : i.val / 2 ^ q.val % 2 = 0 ∨ i.val / 2 ^ q.val % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h]

/-- `getBit` is unchanged by `flipBit` on a different qubit. -/
theorem getBit_flipBit_ne (i : Fin (2 ^ n)) (q₁ q₂ : Fin n) (h : q₁ ≠ q₂) :
    getBit (flipBit i q₁) q₂ = getBit i q₂ := by
  simp only [getBit_eq_testBit, flipBit]
  rw [Nat.testBit_xor]
  simp [Fin.val_ne_of_ne h]

/-- `getBit` sees the flipped value after `flipBit` on the same qubit. -/
theorem getBit_flipBit_self (i : Fin (2 ^ n)) (q : Fin n) :
    getBit (flipBit i q) q = !getBit i q := by
  simp only [getBit_eq_testBit, flipBit]
  rw [Nat.testBit_xor]
  simp

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

/-! ### Gates preserve normalization -/

theorem gatePauliX_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gatePauliX q s).IsNormalized := by
  simp only [QState.IsNormalized, gatePauliX]
  rw [show ∑ i, normSq (s (flipBit i q)) = ∑ i, normSq (s i) from
    Finset.sum_nbij (fun i => flipBit i q)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => by simpa using congr_arg (flipBit · q) h)
      (fun b _ => ⟨flipBit b q, Finset.mem_univ _, by simp⟩)
      (fun _ _ => rfl)]
  exact hs

theorem gatePauliZ_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gatePauliZ q s).IsNormalized := by
  unfold QState.IsNormalized gatePauliZ at *
  rw [show ∑ i, normSq (if getBit i q then -s i else s i) =
    ∑ i, normSq (s i) from Finset.sum_congr rfl fun i _ => by
      split <;> simp [normSq_neg]]
  exact hs

theorem gatePhase_preserves (q : Fin n) (θ : ℝ) (s : QState n)
    (hs : s.IsNormalized) : (gatePhase q θ s).IsNormalized := by
  unfold QState.IsNormalized gatePhase at *
  rw [show ∑ i, normSq (if getBit i q then Complex.exp (↑θ * I) * s i
    else s i) = ∑ i, normSq (s i) from Finset.sum_congr rfl fun i _ => by
      split
      · rw [map_mul]
        have : normSq (Complex.exp (↑θ * I)) = 1 := by
          rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
          simp
        rw [this]; ring
      · rfl]
  exact hs

theorem gateCNOT_preserves (c t : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gateCNOT c t s).IsNormalized := by
  sorry

theorem gateOracle_preserves (f : Fin (2 ^ n) → Bool) (s : QState n)
    (hs : s.IsNormalized) : (gateOracle f s).IsNormalized := by
  unfold QState.IsNormalized gateOracle at *
  rw [show ∑ i, normSq (if f i then -s i else s i) =
    ∑ i, normSq (s i) from Finset.sum_congr rfl fun i _ => by
      split <;> simp [normSq_neg]]
  exact hs

theorem gateHadamard_preserves (q : Fin n) (s : QState n)
    (hs : s.IsNormalized) : (gateHadamard q s).IsNormalized := by
  sorry

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

/-! ### Circuit cost model -/

/-- Cost structure for quantum circuits, tracking gate count, circuit depth,
and oracle queries separately. -/
@[ext]
structure CircuitCost where
  /-- Total number of gates (excluding oracle). -/
  gates : ℕ
  /-- Circuit depth (longest path from input to output). -/
  depth : ℕ
  /-- Number of oracle queries. -/
  oracleQueries : ℕ
  deriving DecidableEq

namespace CircuitCost

/-- Equivalence between `CircuitCost` and a product type. -/
def equivProd : CircuitCost ≃ ℕ × ℕ × ℕ where
  toFun c := (c.gates, c.depth, c.oracleQueries)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by obtain ⟨a, b, c⟩ := p; rfl

instance : Zero CircuitCost := ⟨0, 0, 0⟩

instance : Add CircuitCost where
  add c₁ c₂ := ⟨c₁.gates + c₂.gates, c₁.depth + c₂.depth,
    c₁.oracleQueries + c₂.oracleQueries⟩

instance : SMul ℕ CircuitCost where
  smul n c := ⟨n * c.gates, n * c.depth, n * c.oracleQueries⟩

instance : AddCommMonoid CircuitCost :=
  equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance : LE CircuitCost where
  le c₁ c₂ := c₁.gates ≤ c₂.gates ∧ c₁.depth ≤ c₂.depth ∧
    c₁.oracleQueries ≤ c₂.oracleQueries

instance : Preorder CircuitCost where
  le_refl a := ⟨le_refl _, le_refl _, le_refl _⟩
  le_trans a b c h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₁.2.1 h₂.2.1,
    le_trans h₁.2.2 h₂.2.2⟩

end CircuitCost

/-- Quantum circuit model: counts gates, depth, and oracle queries.
Each single-qubit gate costs 1 gate and 1 depth. CNOT costs 1 gate
and 1 depth. The oracle costs 1 depth and 1 oracle query. -/
noncomputable def circuitModel (n : ℕ) (f : Fin (2 ^ n) → Bool) :
    Model (QuantumQuery n) CircuitCost where
  evalQuery
    | .hadamard q => gateHadamard q
    | .pauliX q => gatePauliX q
    | .pauliZ q => gatePauliZ q
    | .cnot c t => gateCNOT c t
    | .phase q θ => gatePhase q θ
    | .oracle => gateOracle f
  cost
    | .hadamard _ => ⟨1, 1, 0⟩
    | .pauliX _ => ⟨1, 1, 0⟩
    | .pauliZ _ => ⟨1, 1, 0⟩
    | .cnot _ _ => ⟨1, 1, 0⟩
    | .phase _ _ => ⟨1, 1, 0⟩
    | .oracle => ⟨0, 1, 1⟩

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
