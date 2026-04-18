/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Algolean.QueryModel
import Algolean.Models.Quantum.Embed
import QuantumInfo.Finite.MState
import QuantumInfo.Finite.POVM

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
theorem applyGate_time [AddZeroClass Cost] {n : ℕ}
    (q : QuantumQuery n (𝐔[Fin n → Fin 2]))
    (ρ : MState (Fin n → Fin 2))
    (M : Model (QuantumQuery n) Cost) :
    (applyGate q ρ).time M = M.cost q := by
  simp [applyGate]

/-! ### Measurement -/

/-- Indicator function on bitstrings: `1` if qubit `q` is in state `v`, else `0`. -/
private def qubitIndicator {n : ℕ} (q : Fin n) (v : Fin 2) :
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

end Algorithms

end Algolean
