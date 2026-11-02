/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Algorithms.Quantum.DeutschJozsa

/-!
# Deutsch–Jozsa examples

Concrete constant and balanced instances of Deutsch–Jozsa on two qubits.

## Main definitions

- `constantTwo`: the constant-false oracle on two qubits.
- `balancedTwo`: the oracle that reads the first bit of a two-qubit input.

## Main results

- `deutschJozsaOutput_two_constant`: a constant function gives the answer `true`.
- `deutschJozsaOutput_two_balanced`: a balanced function gives the answer `false`.
-/

@[expose] public section

namespace AlgoleanTests.DeutschJozsaExamples

open Algolean.Algorithms

/-- The constant-false oracle on two qubits. -/
def constantTwo : (Fin 2 → Fin 2) → Bool := fun _ => false

/-- The balanced oracle that is true exactly when the first bit is one. -/
def balancedTwo : (Fin 2 → Fin 2) → Bool := fun x => decide (x 0 = 1)

/-- On two qubits, Deutsch–Jozsa answers `true` for a constant function. -/
theorem deutschJozsaOutput_two_constant :
    deutschJozsaOutput 2 constantTwo = PMF.pure true := by
  have hc : IsConstant constantTwo := ⟨false, fun _ => rfl⟩
  simpa only [decide_eq_true hc] using deutschJozsaOutput_eq_pure (Or.inl hc)

/-- On two qubits, Deutsch–Jozsa answers `false` for a balanced function. -/
theorem deutschJozsaOutput_two_balanced :
    deutschJozsaOutput 2 balancedTwo = PMF.pure false := by
  have hbal : IsBalanced balancedTwo := by decide
  simpa only [decide_eq_false (fun hc =>
    not_isConstant_and_isBalanced _ ⟨hc, hbal⟩)] using
    deutschJozsaOutput_eq_pure (Or.inr hbal)

end AlgoleanTests.DeutschJozsaExamples
