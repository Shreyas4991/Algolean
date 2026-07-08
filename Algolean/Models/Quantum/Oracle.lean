/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.QueryModel
public import Algolean.Models.Quantum.Embed
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.Measurements.POVM

/-!
# Quantum Oracle Query Model

A query model for quantum oracle complexity. Each query is a syntactic
description of a gate on an `n`-qubit register (indices in `Fin n`, rational
phase parameters). Semantics maps each query to its honest unitary
`𝐔[Fin n → Fin 2]` from `QuantumInfo`; the density-matrix evolution and
measurement are supplied by `QuantumInfo.MState` / `POVM`.

## Main definitions

- `QuantumQuery n`: syntactic query type. Constructors are single-qubit gates
  (`hadamard`, `pauliX`, `pauliZ`, rational `phase`), `cnot` with a proof
  that control and target differ, and a Boolean-function-parameterized
  `oracle`. Each query's output type is `𝐔[Fin n → Fin 2]`.
- `unitaryOf`: syntax-to-semantics — each syntactic constructor maps to its
  honest unitary via `embedQubitGate`, `cnotUnitary`, `phaseGate`, or the
  oracle phase-flip.
- `quantumModel`: cost model assigning `1` to `oracle` queries, `0` to
  all others.
- `applyGate`: state-threading wrapper that lifts a query into a `Prog`
  returning the transformed `MState`.
- `measureQubitPOVM`: computational-basis projective measurement on a
  single qubit, as a `POVM (Fin 2) (Fin n → Fin 2)`.
- `measureRegisterPOVM`: computational-basis projective measurement on
  the full register, as a `POVM (Fin n → Fin 2) (Fin n → Fin 2)`.

## Design notes

Queries carry only finite syntactic data (tags, `Fin n` indices, `ℚ` phase
parameters). This is required for uniform BQP: a classical Turing machine
can output values of `QuantumQuery n`, but cannot output complex matrices.
The unitaries that queries denote are produced by the `unitaryOf` semantic
layer, not stored in the query itself.

Phase parameters are rational (`θ : ℚ`). The semantic interpretation is
`exp(2πi·θ)`, so "quarter turn" is `θ = 1/4`. This keeps the syntax
uniformity-compatible without restricting expressive power for algorithms.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog Complex
open scoped MState ComplexOrder

/-! ### Query type -/

/-- Syntactic description of a single quantum gate on `n` qubits. Each
constructor produces a value whose output-type index is the full
`n`-qubit unitary; the unitary itself is produced by `unitaryOf` via the
`Model` semantics. -/
inductive QuantumQuery (n : ℕ) : Type → Type where
  /-- Hadamard gate on qubit `q`. -/
  | hadamard (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Pauli-X (NOT) gate on qubit `q`. -/
  | pauliX (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Pauli-Z gate on qubit `q`. -/
  | pauliZ (q : Fin n) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Controlled-NOT with distinct control and target. -/
  | cnot (control target : Fin n) (h : control ≠ target) :
      QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Phase gate `R(θ)` with rational parameter; semantics uses `exp(2πi·θ)`. -/
  | phase (q : Fin n) (θ : ℚ) : QuantumQuery n (𝐔[Fin n → Fin 2])
  /-- Oracle query: applies the phase oracle `|x⟩ ↦ (-1)^{f(x)}|x⟩`. -/
  | oracle : QuantumQuery n (𝐔[Fin n → Fin 2])

/-! ### Phase oracle -/

/-- Phase oracle unitary for a Boolean function:
`|x⟩ ↦ (-1)^{f(x)} |x⟩`, constructed as a diagonal matrix with ±1 entries. -/
noncomputable def gateOracle {n : ℕ} (f : (Fin n → Fin 2) → Bool) :
    𝐔[Fin n → Fin 2] :=
  ⟨Matrix.diagonal fun x => if f x then (-1 : ℂ) else 1, by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.diagonal,
        Matrix.of_apply, Matrix.one_apply_eq]
      rw [Finset.sum_eq_single i]
      · by_cases hi : f i <;> simp [hi]
      · intro k _ hk; simp [Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [Matrix.mul_apply]
      simp only [Matrix.diagonal, Matrix.star_apply, Matrix.of_apply,
        Matrix.one_apply_ne hij]
      rw [Finset.sum_eq_zero]
      intro k _
      by_cases hik : i = k
      · subst hik
        simp [Ne.symm hij]
      · simp only [RCLike.star_def, ite_mul, neg_mul, one_mul, zero_mul, ite_eq_right_iff]
        aesop⟩

@[simp]
theorem gateOracle_apply {n : ℕ} (f : (Fin n → Fin 2) → Bool)
    (x y : Fin n → Fin 2) :
    gateOracle f x y = if x = y then (if f x then (-1 : ℂ) else 1) else 0 := by
  by_cases hxy : x = y <;> simp [gateOracle, Matrix.diagonal, hxy]

/-! ### Semantic interpretation -/

/-- Interpret a syntactic query as its semantic unitary on the full `n`-qubit
register. The `oracle` case uses the supplied oracle unitary; all other
cases delegate to gate-embedding helpers.

Defined generically in the output-type index `ι` so that Lean can use it
as `evalQuery` in a `Model (QuantumQuery n) Cost`. Each constructor forces
`ι = 𝐔[Fin n → Fin 2]`. -/
noncomputable def unitaryOf {n : ℕ} (oracle : 𝐔[Fin n → Fin 2]) :
    {ι : Type} → QuantumQuery n ι → ι
  | _, .hadamard q => embedQubitGate q Qubit.H
  | _, .pauliX q => embedQubitGate q Qubit.X
  | _, .pauliZ q => embedQubitGate q Qubit.Z
  | _, .cnot c t h => cnotUnitary c t h
  | _, .phase q θ => embedQubitGate q (phaseGate (2 * Real.pi * (θ : ℝ)))
  | _, .oracle => oracle

/-! ### Oracle families -/

/-- A per-size family of oracle unitaries, used by `QuantumCircuit.toCPTP`
to interpret oracle queries across different register sizes (needed
for the `par` case where subcircuits have smaller sizes). -/
abbrev OracleFamily := (m : ℕ) → 𝐔[Fin m → Fin 2]

/-- Lift a single-size oracle to an `OracleFamily` that is the identity
at other sizes. -/
noncomputable def extendOracle {n : ℕ} (oracle : 𝐔[Fin n → Fin 2]) :
    OracleFamily :=
  fun m => if h : m = n then h ▸ oracle else 1

/-! ### Cost model -/

/-- Cost model for `QuantumQuery`. Gates are free (cost `0`); oracle queries
cost `1`. Matches the operational-query-count semantics used in
complexity classes like `BQP` relative to an oracle. -/
noncomputable def quantumModel (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    Model (QuantumQuery n) ℕ where
  evalQuery q := unitaryOf (gateOracle f) q
  cost
    | .oracle => 1
    | _ => 0

@[simp]
theorem quantumModel_evalQuery_oracle (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (quantumModel n f).evalQuery .oracle = gateOracle f := rfl

@[simp]
theorem quantumModel_cost_oracle (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (quantumModel n f).cost (QuantumQuery.oracle) = 1 := rfl

/-! ### Prog helpers -/

/-- Apply a gate to a density matrix, threading the result through `Prog`.
The user writes `let ρ' ← applyGate q ρ` in `do` notation. -/
noncomputable def applyGate {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2)) :
    Prog (QuantumQuery n) (MState (Fin n → Fin 2)) :=
  FreeM.liftBind q fun U => pure (U ◃ ρ)

@[simp]
theorem applyGate_eval {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) Cost) :
    (applyGate q ρ).eval M = M.evalQuery q ◃ ρ := by
  simp [applyGate]

@[simp]
theorem applyGate_liftM {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) Cost) :
    (applyGate q ρ).liftM (fun {_} q => (M.evalQuery q : Id _)) =
      M.evalQuery q ◃ ρ := by
  unfold applyGate
  rfl

@[simp]
theorem applyGate_time [AddZeroClass Cost] {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) Cost) :
    (applyGate q ρ).time M = M.cost q := by
  simp [applyGate]

/-! ### State-entry lemmas -/

theorem complex_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  rw [RCLike.star_def, Complex.mul_conj]

theorem complex_mul_star_re_eq_normSq (z : ℂ) :
    (z * star z).re = Complex.normSq z := by
  rw [complex_mul_star_eq_normSq]
  simp

/-- Conjugating a computational-basis pure state by `U` produces the outer
product of the `b`-th column of `U`: the `(i,j)` entry is
`U i b * star (U j b)`. -/
theorem U_conj_pure_basis_apply {d : Type*} [Fintype d] [DecidableEq d]
    (U : 𝐔[d]) (b i j : d) :
    (U ◃ MState.pure (Ket.basis b)).m i j =
      U i b * star (U j b) := by
  simp only [MState.U_conj, MState.m, HermitianMat.conj_apply_mat]
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

/-! ### Measurement -/

/-- Indicator function on bitstrings: `1` if qubit `q` is in state `v`, else `0`. -/
def qubitIndicator {n : ℕ} (q : Fin n) (v : Fin 2) :
    (Fin n → Fin 2) → ℝ :=
  fun x => if x q = v then 1 else 0

/-- Computational-basis projector for "qubit `q` is in state `v`":
`∑_{x : x q = v} |x⟩⟨x|` as a diagonal real-valued `HermitianMat`. -/
noncomputable def computationalProjector {n : ℕ} (q : Fin n) (v : Fin 2) :
    HermitianMat (Fin n → Fin 2) ℂ :=
  HermitianMat.diagonal ℂ (qubitIndicator q v)

/-- Computational-basis measurement of a single qubit. Outcomes are indexed
by `Fin 2`; the projectors are diagonal matrices selecting the
computational basis states with that bit value. -/
noncomputable def measureQubitPOVM {n : ℕ} (q : Fin n) :
    POVM (Fin 2) (Fin n → Fin 2) where
  mats v := computationalProjector q v
  nonneg v := by
    simp only [computationalProjector, HermitianMat.zero_le_iff,
      HermitianMat.diagonal_mat]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro x
    rw [RCLike.nonneg_iff]
    simp only [qubitIndicator]
    split_ifs <;> simp
  normalized := by
    simp only [computationalProjector, Fin.sum_univ_two]
    rw [← HermitianMat.diagonal_add_apply]
    have heq : (fun x : Fin n → Fin 2 =>
        qubitIndicator q 0 x + qubitIndicator q 1 x) = (1 : (Fin n → Fin 2) → ℝ) := by
      funext x
      simp only [qubitIndicator, Pi.one_apply]
      have hq : x q = 0 ∨ x q = 1 := by
        have : (x q).val = 0 ∨ (x q).val = 1 := by omega
        rcases this with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hq with hq | hq <;> simp [hq]
    rw [heq]
    exact HermitianMat.diagonal_one

/-- Indicator function on bitstrings: `1` at `x`, else `0`. -/
def basisIndicator {n : ℕ} (x : Fin n → Fin 2) :
    (Fin n → Fin 2) → ℝ :=
  fun y => if y = x then 1 else 0

@[simp]
theorem basisIndicator_self {n : ℕ} (x : Fin n → Fin 2) :
    basisIndicator x x = 1 := by
  simp [basisIndicator]

theorem basisIndicator_eq_zero_of_ne {n : ℕ} {x y : Fin n → Fin 2}
    (h : y ≠ x) : basisIndicator x y = 0 := by
  simp [basisIndicator, h]

/-- Computational-basis projector for the full-register basis state `|x⟩`:
`|x⟩⟨x|` as a diagonal real-valued `HermitianMat`. -/
noncomputable def computationalBasisProjector {n : ℕ} (x : Fin n → Fin 2) :
    HermitianMat (Fin n → Fin 2) ℂ :=
  HermitianMat.diagonal ℂ (basisIndicator x)

theorem computationalBasisProjector_mat_apply {n : ℕ}
    (x y z : Fin n → Fin 2) :
    (computationalBasisProjector x).mat y z =
      if y = z then (basisIndicator x y : ℂ) else 0 := by
  unfold computationalBasisProjector
  rw [HermitianMat.diagonal_mat]
  by_cases hyz : y = z <;> simp [Matrix.diagonal, hyz]

@[simp]
theorem computationalBasisProjector_apply {n : ℕ}
    (x y z : Fin n → Fin 2) :
    computationalBasisProjector x y z =
      if y = z then (basisIndicator x y : ℂ) else 0 := by
  rw [← HermitianMat.mat_apply]
  exact computationalBasisProjector_mat_apply x y z

/-- The full-register computational-basis projectors resolve the identity. -/
theorem computationalBasisProjector_sum_mat {n : ℕ} :
    (∑ x : Fin n → Fin 2, (computationalBasisProjector x).mat) =
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) := by
  ext y z
  rw [Matrix.sum_apply]
  by_cases hyz : y = z
  · subst z
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hx
      simp [basisIndicator_eq_zero_of_ne (Ne.symm hx)]
    · intro h
      exact absurd (Finset.mem_univ y) h
  · simp [hyz]

/-- The full-register computational-basis projectors resolve the identity. -/
theorem computationalBasisProjector_sum {n : ℕ} :
    (∑ x : Fin n → Fin 2, computationalBasisProjector x) =
      (1 : HermitianMat (Fin n → Fin 2) ℂ) := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_finset_sum, computationalBasisProjector_sum_mat]
  rfl

/-- Computational-basis measurement of the whole register. Outcomes are
indexed by bitstrings, and the projector for outcome `x` is `|x⟩⟨x|`. -/
noncomputable def measureRegisterPOVM (n : ℕ) :
    POVM (Fin n → Fin 2) (Fin n → Fin 2) where
  mats x := computationalBasisProjector x
  nonneg x := by
    simp only [computationalBasisProjector, HermitianMat.zero_le_iff,
      HermitianMat.diagonal_mat]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro y
    rw [RCLike.nonneg_iff]
    simp only [basisIndicator]
    split_ifs <;> simp
  normalized := computationalBasisProjector_sum

theorem measureRegisterPOVM_measure_pure_apply_coe {n : ℕ}
    (ψ : Ket (Fin n → Fin 2)) (x : Fin n → Fin 2) :
    (((measureRegisterPOVM n).measure (MState.pure ψ)) x : ℝ) =
      Complex.normSq (ψ x) := by
  simp only [measureRegisterPOVM, POVM.measure, ProbDistribution.mk',
    ProbDistribution.funlike_apply]
  rw [HermitianMat.inner_eq_re_trace]
  simp only [computationalBasisProjector_mat_apply, MState.mat_M, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, MState.pure_apply]
  rw [Finset.sum_eq_single x]
  · simp [basisIndicator, Complex.normSq]
  · intro y _ hy
    simp [basisIndicator_eq_zero_of_ne hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

@[simp]
theorem measureRegisterPOVM_measure_apply_coe {n : ℕ}
    (ρ : MState (Fin n → Fin 2)) (x : Fin n → Fin 2) :
    (((measureRegisterPOVM n).measure ρ) x : ℝ) = (ρ.m x x).re := by
  simp only [measureRegisterPOVM, POVM.measure, ProbDistribution.mk',
    ProbDistribution.funlike_apply]
  rw [HermitianMat.inner_eq_re_trace]
  simp only [computationalBasisProjector_mat_apply, MState.mat_M, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · simp [basisIndicator]
  · intro y _ hy
    simp [basisIndicator_eq_zero_of_ne hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

end Algorithms

end Algolean
