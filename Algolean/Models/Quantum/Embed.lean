/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

import Algolean.Models.Quantum.Indexing
import QuantumInfo.Finite.Qubit.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Gate unitaries on `Fin n → Fin 2`

Construction of the concrete `𝐔[Fin n → Fin 2]` matrices corresponding to
each gate of the `QuantumQuery` syntax. Three strategies appear:

- **Dense single-qubit gates** (`H`, `X`, `Z`, phase): tensor a `𝐔[Qubit]`
  unitary with identity on the other qubits and relabel through
  `Fin.insertNthEquiv`. Implemented by `embedQubitGate`.

- **Permutation gates** (CNOT): construct the underlying permutation of
  `Fin n → Fin 2` directly; unitarity is free from
  `Equiv.Perm.permMatrix_mem_unitaryGroup`. Avoids the two-qubit
  index gymnastics.

- **Parametric gates** (phase `R(θ)`): supplied here because QuantumInfo
  only ships fixed-phase gates (`S`, `T`).

## Main definitions

- `unitaryReindex e U` : `𝐔[d] → 𝐔[d₂]` along `e : d ≃ d₂`.
- `phaseGate θ : 𝐔[Qubit]` : parametric phase gate.
- `embedQubitGate q U : 𝐔[Fin n → Fin 2]` : single-qubit gate on position `q`.
- `cnotUnitary c t h : 𝐔[Fin n → Fin 2]` : CNOT with `control ≠ target`.
-/

namespace Algolean

namespace Algorithms

open scoped Matrix

/-! ### Transport of unitaries along index equivalences -/

/-- Transport a unitary through a type equivalence. For `e : d ≃ d₂` and
`U : 𝐔[d]`, returns the unitary on `d₂` whose `(i₂, j₂)` entry is
`U (e.symm i₂) (e.symm j₂)`.

Implemented via `Matrix.submatrix` composed with `e.symm` on both
sides; unitarity is preserved because `submatrix` with a bijection commutes
with matrix multiplication and the conjugate transpose. -/
def unitaryReindex {d d₂ : Type*} [Fintype d] [Fintype d₂]
    [DecidableEq d] [DecidableEq d₂] (e : d ≃ d₂) (U : 𝐔[d]) : 𝐔[d₂] :=
  ⟨U.val.submatrix e.symm e.symm, by
    rw [Matrix.mem_unitaryGroup_iff]
    have hU : U.val * star U.val = 1 := Matrix.mem_unitaryGroup_iff.mp U.2
    have hstar :
        star (U.val.submatrix e.symm e.symm) = (star U.val).submatrix e.symm e.symm :=
      (Matrix.conjTranspose_submatrix _ _ _).symm
    rw [hstar, Matrix.submatrix_mul_equiv, hU, Matrix.submatrix_one_equiv]⟩

/-! ### Parametric phase gate -/

/-- The parametric phase gate `R(θ)` on a single qubit:
`R(θ)|0⟩ = |0⟩`, `R(θ)|1⟩ = exp(iθ)|1⟩`. -/
noncomputable def phaseGate (θ : ℝ) : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, Complex.exp (↑θ * Complex.I)], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        ← Complex.exp_conj, mul_comm, ← Complex.exp_add, Complex.conj_I]⟩

/-! ### Single-qubit gate embedding -/

/-- Embed a single-qubit unitary `U : 𝐔[Qubit]` as an n-qubit unitary acting
as `U` on qubit `q` and identity on the other qubits.

The `Fin 0` case is vacuous (no qubit to act on); `q : Fin 0` triggers
`Fin.elim0`. For `n = n' + 1`, the implementation tensors `U ⊗ᵤ 1` on
`Qubit × (Fin n' → Qubit)` and transports through `Fin.insertNthEquiv`
to land in `Fin (n' + 1) → Qubit = Fin n → Fin 2`. -/
noncomputable def embedQubitGate :
    {n : ℕ} → (q : Fin n) → 𝐔[Qubit] → 𝐔[Fin n → Fin 2]
  | 0, q, _ => q.elim0
  | _ + 1, q, U =>
      unitaryReindex (Fin.insertNthEquiv (fun _ => Qubit) q)
        (U ⊗ᵤ (1 : 𝐔[Fin _ → Qubit]))

/-! ### CNOT unitary -/

/-- In `Fin 2`, subtracting twice from `1` is the identity. -/
private lemma fin2_sub_sub_self (b : Fin 2) : (1 : Fin 2) - (1 - b) = b := by
  fin_cases b <;> rfl

/-- Action of the CNOT gate on bitstrings: flip the target bit iff control is 1. -/
private def cnotAction {n : ℕ} (c t : Fin n) : (Fin n → Fin 2) → (Fin n → Fin 2) :=
  fun x => if x c = 1 then Function.update x t (1 - x t) else x

/-- `cnotAction c t` is an involution when control and target differ. -/
private lemma cnotAction_involutive {n : ℕ} {c t : Fin n} (h : c ≠ t) :
    Function.Involutive (cnotAction c t) := by
  intro x
  unfold cnotAction
  by_cases hxc : x c = 1
  · rw [if_pos hxc]
    have hc : Function.update x t (1 - x t) c = 1 := by
      rw [Function.update_of_ne h]; exact hxc
    rw [if_pos hc, Function.update_self, Function.update_idem, fin2_sub_sub_self]
    exact Function.update_eq_self t x
  · rw [if_neg hxc, if_neg hxc]

/-- The CNOT gate on `Fin n → Fin 2` as a permutation unitary. Flips the
target qubit whenever the control qubit is `1`. Control and target must
differ for the action to be a bijection (hence unitary); with `c = t` the
action would collapse basis states. -/
noncomputable def cnotUnitary {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    𝐔[Fin n → Fin 2] :=
  let σ : Equiv.Perm (Fin n → Fin 2) := (cnotAction_involutive h).toPerm
  ⟨σ.permMatrix ℂ, σ.permMatrix_mem_unitaryGroup⟩

end Algorithms

end Algolean
