/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Algorithms.Quantum.HadamardLayer

/-!
# Hadamard layer examples

A concrete entry of the one-qubit Hadamard layer, and verification through a register
measurement.

## Main definitions

- `hadamardsMeasureGate`: apply a layer, measure the register, and apply a gate.

## Main results

- `hadamards_one_entry`: the sign and normalization of the Hadamard matrix.
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
