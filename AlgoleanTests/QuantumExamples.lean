/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Oracle

/-! # Quantum query model examples -/

@[expose] public section

namespace AlgoleanTests.QuantumExamples

open Algolean.Algorithms Cslib
open scoped MState

/-- Flip a qubit and flip it back. -/
noncomputable def flipTwice : Prog (QuantumQuery 1) Unit := do
  applyGate (.pauliX 0)
  applyGate (.pauliX 0)

theorem flipTwice_measurementFree : MeasurementFree flipTwice :=
  .gate _ (.gate _ (.pure _))

-- Without measurements, a run is a point mass at the deterministic gate semantics.
example (f : (Fin 1 → Fin 2) → Bool) (ρ : QState 1) :
    (flipTwice.evalM (quantumModel 1 f)).run ρ =
      PMF.pure ((flipTwice.evalM (unitaryModel 1 f)).run ρ) :=
  evalM_quantumModel_of_measurementFree flipTwice_measurementFree ρ

-- Measuring a basis state returns it with probability one and leaves the register in place.
example (f : (Fin 2 → Fin 2) → Bool) (x : Fin 2 → Fin 2) :
    ((measureRegister 2).evalM (quantumModel 2 f)).run (MState.pure (Ket.basis x)) =
      PMF.pure (x, MState.pure (Ket.basis x)) := by
  simp [measureRegister, measureRegisterM, StateT.run, bornPMF_measureRegister_basis, PMF.pure_map]

-- Only oracle calls are charged.
example (f : (Fin 3 → Fin 2) → Bool) : (quantumModel 3 f).cost (.gate .oracle) = 1 := by simp
example (f : (Fin 3 → Fin 2) → Bool) : (quantumModel 3 f).cost (.gate (.hadamard 0)) = 0 := rfl
example (f : (Fin 3 → Fin 2) → Bool) : (quantumModel 3 f).cost (.measure 1) = 0 := by simp

/-- Classical control on a mid-circuit measurement: measure a qubit in superposition and flip
it back to `|0⟩` when the outcome is `1`. -/
noncomputable def measureAndReset : Prog (QuantumQuery 1) (Fin 2) := do
  applyGate (.hadamard 0)
  let b ← measureQubit 0
  if b = 1 then applyGate (.pauliX 0)
  measureQubit 0

end AlgoleanTests.QuantumExamples
