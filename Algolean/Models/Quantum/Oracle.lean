/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.ModelM
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Algolean.Models.Quantum.Embed
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.Measurements.POVM

/-!
# Quantum Oracle Query Model

A query model for quantum oracle complexity. The register's density matrix is the model's hidden
state: gates and oracle calls act on it and return `Unit`, and computational-basis measurements
return their classical outcome and collapse it. A program observes only measurement outcomes, as a
physical algorithm does, and can branch on them in the middle of a computation.

## Main definitions

- `QuantumGate n`: gate syntax. Constructors are single-qubit gates (`hadamard`, `pauliX`,
  `pauliZ`, rational `phase`), `cnot` with a proof that control and target differ, and the phase
  `oracle`.
- `QuantumQuery n`: the query type. `gate g` applies a gate, `measure q` measures qubit `q`, and
  `measureAll` measures the whole register.
- `unitaryOf`: syntax-to-semantics map sending each gate to its unitary on the full register via
  `embedQubitGate`, `cnotUnitary`, `phaseGate`, or the oracle phase flip.
- `measureQubitPOVM`, `measureRegisterPOVM`: computational-basis measurements as POVMs.
- `bornPMF`: the outcome distribution of a POVM on a state, as a `PMF`.
- `collapse`: the normalized post-measurement state for a measurement operator.
- `QuantumM n`: the execution monad `StateT (MState (Fin n → Fin 2)) PMF`.
- `quantumModel n f`: the model for the oracle function `f`. Oracle calls cost `1`; all other
  queries cost `0`.
- `MeasurementFree`, `unitaryModel`: programs without measurements and their deterministic
  semantics. `evalM_quantumModel_of_measurementFree` says such programs run deterministically.

## Design notes

No query returns a unitary or the register state, and the oracle function is a parameter of the
model rather than data in the program, so a program learns about `f` only through oracle calls
followed by measurements. The oracle is the phase oracle on the whole register, which cannot
distinguish `f` from `!f`: `gateOracle (!f) = -gateOracle f` differs by a global phase. The model
therefore suits problems that are unchanged when `f` is complemented, such as search and
Deutsch–Jozsa, and query lower bounds proved in it do not carry over to the standard bit-oracle
model.

Gates form their own non-indexed type. Pattern matching on `QuantumQuery n Unit` cannot exclude
the measurement constructors, because Lean cannot refute `Fin 2 = Unit`, so `unitaryOf` and the
circuit leaves of `QuantumCircuit` take a `QuantumGate`.

Gates carry only finite syntactic data (tags, `Fin n` indices, `ℚ` phase parameters). This is
required for uniform BQP: a classical Turing machine can output values of `QuantumGate n`, but
cannot output complex matrices. The unitaries that gates denote are produced by the `unitaryOf`
semantic layer, not stored in the gate itself.

Phase parameters are rational (`θ : ℚ`). The semantic interpretation is
`exp(2πi·θ)`, so "quarter turn" is `θ = 1/4`. This keeps the syntax
uniformity-compatible without restricting expressive power for algorithms.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog Complex
open scoped MState ComplexOrder

/-! ### Gates and queries -/

/-- Syntactic description of a single quantum gate on `n` qubits. The unitary it denotes is
produced by `unitaryOf`. -/
inductive QuantumGate (n : ℕ) : Type where
  /-- Hadamard gate on qubit `q`. -/
  | hadamard (q : Fin n)
  /-- Pauli-X (NOT) gate on qubit `q`. -/
  | pauliX (q : Fin n)
  /-- Pauli-Z gate on qubit `q`. -/
  | pauliZ (q : Fin n)
  /-- Controlled-NOT with distinct control and target. -/
  | cnot (control target : Fin n) (h : control ≠ target)
  /-- Phase gate `R(θ)` with rational parameter; semantics uses `exp(2πi·θ)`. -/
  | phase (q : Fin n) (θ : ℚ)
  /-- Oracle query: applies the phase oracle `|x⟩ ↦ (-1)^{f(x)}|x⟩`. -/
  | oracle

/-- Quantum queries on an `n`-qubit register. Gates act on the hidden register state and return
`Unit`; measurements return their classical outcome. -/
inductive QuantumQuery (n : ℕ) : Type → Type where
  /-- Apply a gate to the register. -/
  | gate (g : QuantumGate n) : QuantumQuery n Unit
  /-- Measure qubit `q` in the computational basis. -/
  | measure (q : Fin n) : QuantumQuery n (Fin 2)
  /-- Measure the whole register in the computational basis. -/
  | measureAll : QuantumQuery n (Fin n → Fin 2)

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

/-- Interpret a gate as its unitary on the full `n`-qubit register. The `oracle` case uses the
supplied oracle unitary; all other cases delegate to gate-embedding helpers. -/
noncomputable def unitaryOf {n : ℕ} (oracle : 𝐔[Fin n → Fin 2]) :
    QuantumGate n → 𝐔[Fin n → Fin 2]
  | .hadamard q => embedQubitGate q Qubit.H
  | .pauliX q => embedQubitGate q Qubit.X
  | .pauliZ q => embedQubitGate q Qubit.Z
  | .cnot c t h => cnotUnitary c t h
  | .phase q θ => embedQubitGate q (phaseGate (2 * Real.pi * (θ : ℝ)))
  | .oracle => oracle

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

/-! ### Prog helpers -/

/-- Apply a gate to the register. -/
def applyGate {n : ℕ} (g : QuantumGate n) : Prog (QuantumQuery n) Unit :=
  FreeM.lift (.gate g)

/-- Measure qubit `q`, returning its outcome. -/
def measureQubit {n : ℕ} (q : Fin n) : Prog (QuantumQuery n) (Fin 2) :=
  FreeM.lift (.measure q)

/-- Measure the whole register, returning the observed bitstring. -/
def measureRegister (n : ℕ) : Prog (QuantumQuery n) (Fin n → Fin 2) :=
  FreeM.lift .measureAll

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
  simp only [MState.uConj, MState.m, HermitianMat.conj_apply_mat]
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

/-! ### Born-rule distributions and collapse -/

/-- The outcome distribution of measuring `ρ` with `Λ`, as a `PMF`. QuantumInfo's `POVM.measure`
produces its own `ProbDistribution`; the conversion to `PMF` happens here, once per measurement. -/
noncomputable def bornPMF {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (ρ : MState d) : PMF X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (Λ.measure ρ x : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (Λ.measure ρ x).2.1)]
    simp)

@[simp]
theorem bornPMF_apply {X d : Type*} [Fintype X] [Fintype d] [DecidableEq d]
    (Λ : POVM X d) (ρ : MState d) (x : X) :
    bornPMF Λ ρ x = ENNReal.ofReal (Λ.measure ρ x : ℝ) := rfl

/-- The post-measurement state for the measurement operator `K`: `K ρ K† / tr(K ρ K†)`. When
the outcome has probability zero the state is returned unchanged; `bornPMF` gives that branch no
mass, so the choice does not affect any run. -/
noncomputable def collapse {d : Type*} [Fintype d] [DecidableEq d]
    (K : Matrix d d ℂ) (ρ : MState d) : MState d :=
  if h : 0 < ((ρ.M.conj K).trace : ℝ) then
    { M := ((ρ.M.conj K).trace : ℝ)⁻¹ • ρ.M.conj K
      nonneg := smul_nonneg (inv_nonneg.mpr h.le) (HermitianMat.conj_nonneg K ρ.nonneg)
      tr := by rw [HermitianMat.trace_smul, inv_mul_cancel₀ h.ne'] }
  else ρ

/-! ### The execution model -/

/-- The register state: a density matrix on `n` qubits. -/
abbrev QState (n : ℕ) := MState (Fin n → Fin 2)

/-- Execution monad: a distribution over results paired with post-execution register states. -/
abbrev QuantumM (n : ℕ) := StateT (QState n) PMF

/-- Measure qubit `q`: sample the outcome by the Born rule, then collapse the register onto it. -/
noncomputable def measureQubitM {n : ℕ} (q : Fin n) : QuantumM n (Fin 2) := fun ρ =>
  (bornPMF (measureQubitPOVM q) ρ).map fun b => (b, collapse (computationalProjector q b).mat ρ)

/-- Measure the whole register: sample a bitstring by the Born rule. The register is left in the
observed basis state. -/
noncomputable def measureRegisterM (n : ℕ) : QuantumM n (Fin n → Fin 2) := fun ρ =>
  (bornPMF (measureRegisterPOVM n) ρ).map fun x => (x, MState.pure (Ket.basis x))

/-- The quantum query model for the oracle function `f`. Gates and oracle calls conjugate the
register by their unitary; measurements sample and collapse. Oracle calls cost `1`, all other
queries `0`. -/
noncomputable def quantumModel (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    ModelM (QuantumQuery n) (QuantumM n) ℕ where
  evalQuery
    | .gate g => modify (unitaryOf (gateOracle f) g ◃ ·)
    | .measure q => measureQubitM q
    | .measureAll => measureRegisterM n
  cost
    | .gate .oracle => 1
    | _ => 0

@[simp]
theorem quantumModel_evalQuery_gate (n : ℕ) (f : (Fin n → Fin 2) → Bool) (g : QuantumGate n) :
    (quantumModel n f).evalQuery (.gate g) = modify (unitaryOf (gateOracle f) g ◃ ·) := rfl

@[simp]
theorem quantumModel_evalQuery_measure (n : ℕ) (f : (Fin n → Fin 2) → Bool) (q : Fin n) :
    (quantumModel n f).evalQuery (.measure q) = measureQubitM q := rfl

@[simp]
theorem quantumModel_evalQuery_measureAll (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (quantumModel n f).evalQuery .measureAll = measureRegisterM n := rfl

@[simp]
theorem quantumModel_cost_oracle (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (quantumModel n f).cost (.gate .oracle) = 1 := rfl

theorem quantumModel_cost_gate_of_ne_oracle (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    {g : QuantumGate n} (hg : g ≠ .oracle) :
    (quantumModel n f).cost (.gate g) = 0 := by
  cases g <;> first | rfl | exact absurd rfl hg

@[simp]
theorem quantumModel_cost_measure (n : ℕ) (f : (Fin n → Fin 2) → Bool) (q : Fin n) :
    (quantumModel n f).cost (.measure q) = 0 := rfl

@[simp]
theorem quantumModel_cost_measureAll (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    (quantumModel n f).cost .measureAll = 0 := rfl

/-- Measuring qubit `q` returns each outcome with its Born-rule probability. -/
theorem measureQubitM_outcome {n : ℕ} (q : Fin n) (ρ : QState n) :
    Prod.fst <$> (measureQubitM q).run ρ = bornPMF (measureQubitPOVM q) ρ := by
  simp only [measureQubitM, StateT.run, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- Measuring the register returns each bitstring with its Born-rule probability. -/
theorem measureRegisterM_outcome (n : ℕ) (ρ : QState n) :
    Prod.fst <$> (measureRegisterM n).run ρ = bornPMF (measureRegisterPOVM n) ρ := by
  simp only [measureRegisterM, StateT.run, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- Measuring the register in the basis state `|x⟩` returns `x` with probability one. -/
theorem bornPMF_measureRegister_basis {n : ℕ} (x : Fin n → Fin 2) :
    bornPMF (measureRegisterPOVM n) (MState.pure (Ket.basis x)) = PMF.pure x := by
  ext y
  rw [bornPMF_apply, measureRegisterPOVM_measure_pure_apply_coe, PMF.pure_apply]
  by_cases h : y = x
  · subst h
    simp [Ket.basis, Ket.apply]
  · simp [Ket.basis, Ket.apply, h, Ne.symm h]

/-! ### Programs without measurements -/

/-- A program that applies only gates. -/
inductive MeasurementFree {n : ℕ} {α : Type} : Prog (QuantumQuery n) α → Prop where
  | pure (a : α) : MeasurementFree (FreeM.pure a)
  | gate (g : QuantumGate n) {k : Unit → Prog (QuantumQuery n) α} :
      MeasurementFree (k ()) → MeasurementFree (FreeM.liftBind (.gate g) k)

/-- Deterministic gate semantics in `StateM`. Measurements get placeholder results; the model
is meant for `MeasurementFree` programs, which never measure. -/
noncomputable def unitaryModel (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    ModelM (QuantumQuery n) (StateM (QState n)) ℕ where
  evalQuery
    | .gate g => modify (unitaryOf (gateOracle f) g ◃ ·)
    | .measure _ => pure 0
    | .measureAll => pure 0
  cost := (quantumModel n f).cost

/-- A program without measurements runs deterministically: its distribution is a point mass at
the result of applying its gates in order. -/
theorem evalM_quantumModel_of_measurementFree {n : ℕ} {f : (Fin n → Fin 2) → Bool}
    {α : Type} {P : Prog (QuantumQuery n) α} (hP : MeasurementFree P) (ρ : QState n) :
    (P.evalM (quantumModel n f)).run ρ = PMF.pure ((P.evalM (unitaryModel n f)).run ρ) := by
  induction hP generalizing ρ with
  | pure a => rfl
  | gate g _ ih =>
    have := ih ((unitaryOf (gateOracle f) g) ◃ ρ)
    simpa [Prog.evalM, FreeM.liftM, unitaryModel] using this

end Algorithms

end Algolean
