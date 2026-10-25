/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Hadamard
public import Algolean.Models.Quantum.Spec

/-!
# Hadamard layer programs

Apply one Hadamard gate to each qubit of the hidden register.

## Main definitions

- `applyHadamardsUpTo k`: the Hadamard gates on qubits `0, …, k − 1`.
- `applyHadamards n`: a Hadamard gate on every qubit.

## Main results

- `measurementFree_applyHadamards`: the layer contains no measurements.
- `applyHadamards_evalM_unitaryModel`: its deterministic action is `hadamardsUnitary n`.
- `applyHadamards_cost`: the layer has zero oracle cost.
- `applyHadamards_spec`: the `mvcgen` rule for the layer.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Std.Do
open scoped MState

noncomputable section

/-- Apply Hadamard gates to qubits `0, …, k − 1`, in increasing order. -/
def applyHadamardsUpTo {n : ℕ} : (k : ℕ) → k ≤ n → Prog (QuantumQuery n) Unit
  | 0, _ => pure ()
  | k + 1, hk => do
    applyHadamardsUpTo k (Nat.le_of_succ_le hk)
    applyGate (.hadamard ⟨k, Nat.lt_of_succ_le hk⟩)

/-- Apply a Hadamard gate to every qubit. -/
def applyHadamards (n : ℕ) : Prog (QuantumQuery n) Unit :=
  applyHadamardsUpTo n (Nat.le_refl n)

/-- A partial Hadamard layer contains no measurements. -/
theorem measurementFree_applyHadamardsUpTo {n k : ℕ} (hk : k ≤ n) :
    MeasurementFree (applyHadamardsUpTo k hk) := by
  induction k with
  | zero => exact .pure ()
  | succ k ih =>
    exact (ih (Nat.le_of_succ_le hk)).bind fun _ => measurementFree_applyGate _

/-- The Hadamard layer contains no measurements. -/
theorem measurementFree_applyHadamards (n : ℕ) : MeasurementFree (applyHadamards n) :=
  measurementFree_applyHadamardsUpTo (Nat.le_refl n)

/-- A partial layer conjugates the register by `hadamardsUpToUnitary k hk`. -/
@[simp]
theorem applyHadamardsUpTo_evalM_unitaryModel {n k : ℕ} (hk : k ≤ n)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((applyHadamardsUpTo k hk).evalM (unitaryModel n f)).run ρ =
      ((), hadamardsUpToUnitary k hk ◃ ρ) := by
  induction k generalizing ρ with
  | zero => simp [applyHadamardsUpTo, hadamardsUpToUnitary, StateT.run]
  | succ k ih =>
    simp only [applyHadamardsUpTo, Prog.evalM_bind, StateT.run_bind, ih,
      applyGate_evalM_unitaryModel, unitaryOf, hadamardsUpToUnitary,
      MState.uConj_mul]
    rfl

/-- The Hadamard layer conjugates the register by `hadamardsUnitary n`. -/
@[simp]
theorem applyHadamards_evalM_unitaryModel (n : ℕ)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((applyHadamards n).evalM (unitaryModel n f)).run ρ =
      ((), hadamardsUnitary n ◃ ρ) :=
  applyHadamardsUpTo_evalM_unitaryModel (Nat.le_refl n) f ρ

/-- A partial Hadamard layer runs with zero cost and its deterministic final state. -/
@[simp]
theorem applyHadamardsUpTo_runM {n k : ℕ} (hk : k ≤ n)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((applyHadamardsUpTo k hk).runM (quantumModel n f)).run.run ρ =
      PMF.pure ((⟨(), 0⟩ : AddWriter ℕ Unit), hadamardsUpToUnitary k hk ◃ ρ) := by
  induction k generalizing ρ with
  | zero =>
    simp only [applyHadamardsUpTo, hadamardsUpToUnitary, MState.uConj_one]
    rfl
  | succ k ih =>
    simp only [applyHadamardsUpTo, Prog.runM_bind, AddWriterT.run_bind, StateT.run_bind, ih]
    change (PMF.pure _).bind _ = _
    rw [PMF.pure_bind]
    simp only [applyGate_runM]
    change (PMF.pure _).bind _ = _
    rw [PMF.pure_bind]
    simp only [hadamardsUpToUnitary, MState.uConj_mul, unitaryOf]
    rfl

/-- The partial layer has zero oracle cost. -/
theorem applyHadamardsUpTo_cost {n k : ℕ} (hk : k ≤ n)
    (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((applyHadamardsUpTo k hk).costM (quantumModel n f)).run ρ =
      PMF.pure (0, hadamardsUpToUnitary k hk ◃ ρ) := by
  simp only [Prog.costM, AddWriterT.cost, StateT.run_map, applyHadamardsUpTo_runM,
    PMF.monad_map_eq_map, PMF.pure_map]

/-- The Hadamard layer has zero oracle cost on every run. -/
@[simp]
theorem applyHadamards_cost (n : ℕ) (f : (Fin n → Fin 2) → Bool) (ρ : QState n) :
    ((applyHadamards n).costM (quantumModel n f)).run ρ =
      PMF.pure (0, hadamardsUnitary n ◃ ρ) :=
  applyHadamardsUpTo_cost (Nat.le_refl n) f ρ

/-- `mvcgen` rule for the Hadamard layer: conjugation by `hadamardsUnitary n`. -/
@[spec]
theorem applyHadamards_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (post : PostCond Unit (.arg (QState n) .pure)) :
    letI := quantumWP n f
    Triple (applyHadamards n)
      (fun ρ => post.1 () (evolveState (hadamardsUnitary n) ρ)) post := by
  simpa only [evolveState_eq, applyHadamards_evalM_unitaryModel] using
    (measurementFree_applyHadamards n).spec f post

end

end Algolean.Algorithms
