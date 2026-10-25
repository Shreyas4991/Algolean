/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Algorithms.Quantum.HadamardLayer

/-!
# Hadamard layer examples

Concrete entries of the one- and two-qubit Hadamard layers, their action on the zero register,
and verification through a register measurement.

## Main definitions

- `hadamardsMeasureGate`: apply a layer, measure the register, and apply a gate.

## Main results

- `hadamards_one_entry`, `hadamards_two_entry`: concrete Hadamard matrix entries.
- `applyHadamards_two_zero`: the layer prepares a uniform superposition.
- `hadamards_measure_gate_spec`: `mvcgen` continues through measurement to a subsequent gate.
-/

@[expose] public section

namespace AlgoleanTests.HadamardExamples

open Algolean.Algorithms Cslib Std.Do
open scoped MState

noncomputable section

/-- The lower-right entry of the one-qubit Hadamard is `−1/√2`. -/
theorem hadamards_one_entry :
    hadamardsUnitary 1 (fun _ => 1) (fun _ => 1) = -(√(1 / 2 : ℝ) : ℂ) := by
  simp [hadamardsUnitary_apply, hadamardScale]

/-- The entry at the all-ones row and column of the two-qubit Hadamard is `1/2`. -/
theorem hadamards_two_entry :
    hadamardsUnitary 2 (fun _ => 1) (fun _ => 1) = (1 / 2 : ℂ) := by
  simp [hadamardsUnitary_apply, hadamardScale, ← Complex.ofReal_pow]

/-- Applying a two-qubit Hadamard layer to the zero register prepares the uniform state. -/
theorem applyHadamards_two_zero (f : (Fin 2 → Fin 2) → Bool) :
    ((applyHadamards 2).evalM (unitaryModel 2 f)).run (MState.pure (Ket.basis 0)) =
      ((), MState.pure (uniformKet 2)) := by
  rw [applyHadamards_evalM_unitaryModel, MState.uConj_pure,
    unitaryKet_hadamardsUnitary_zero]

/-- Apply a layer, measure the register, then apply another Hadamard to the measured state. -/
def hadamardsMeasureGate : Prog (QuantumQuery 1) (Fin 1 → Fin 2) := do
  applyHadamards 1
  let x ← measureRegister 1
  applyGate (.hadamard 0)
  pure x

set_option linter.deprecated.syntax false in
/-- A Hadamard layer, register measurement, and subsequent gate can be verified with `mvcgen`. -/
theorem hadamards_measure_gate_spec (f : (Fin 1 → Fin 2) → Bool) :
    letI := quantumWP 1 f
    ⦃fun ρ => ⌜ρ = MState.pure (Ket.basis 0)⌝⦄
      hadamardsMeasureGate
    ⦃⇓ x ρ => ⌜ρ = evolveState (embedQubitGate 0 Qubit.H)
      (MState.pure (Ket.basis x))⌝⦄ := by
  mvcgen [hadamardsMeasureGate]
  simp_all [unitaryOf]

end

end AlgoleanTests.HadamardExamples
