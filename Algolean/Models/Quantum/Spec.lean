/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Oracle
public import Algolean.Models.RandomSample

/-!
# Quantum program specifications

Hoare triples for the hidden-state quantum model, under the handler `(quantumModel n f).hasHandler`.
A triple asserts that its postcondition holds of every result and final state in the support of
the program's execution. The rules for gates and measurements are stated in weakest-precondition
form, so `vcgen` continues through subsequent queries.

## Main definitions

- `evolveState`: conjugation of a register state, kept opaque during verification.

## Main results

- `MeasurementFree.spec`: specifications from deterministic gate semantics.
- `applyGate_spec`, `measureRegister_spec`, `measureQubit_spec`: query rules for `vcgen`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Std.WP
open scoped MState

noncomputable section

set_option experimental.vcgen true

/-- Sequencing two programs without measurements gives a program without measurements. -/
theorem MeasurementFree.bind {n : ℕ} {α β : Type} {P : Prog (QuantumQuery n) α}
    {k : α → Prog (QuantumQuery n) β} (hP : MeasurementFree P)
    (hk : ∀ a, MeasurementFree (k a)) : MeasurementFree (P >>= k) := by
  induction hP with
  | pure a => exact hk a
  | gate g _ ih => exact .gate g ih

/-- Applying a gate performs no measurement. -/
theorem measurementFree_applyGate {n : ℕ} (g : QuantumGate n) :
    MeasurementFree (applyGate g) := .gate g (.pure ())

/-- Under deterministic semantics a gate conjugates the register by its unitary. -/
@[simp] theorem applyGate_evalM_unitaryModel {n : ℕ} (f : (Fin n → Fin 2) → Bool)
    (g : QuantumGate n) (ρ : QState n) :
    ((applyGate g).evalM (unitaryModel n f)).run ρ =
      ((), unitaryOf (gateOracle f) g ◃ ρ) := by
  rw [applyGate, Prog.evalM_lift]
  rfl

/-- The joint semantics of a gate applies the unitary and records its query cost. -/
theorem applyGate_runM {n : ℕ} (f : (Fin n → Fin 2) → Bool) (g : QuantumGate n) (ρ : QState n) :
    ((applyGate g).runM (quantumModel n f)).run.run ρ =
      PMF.pure ((⟨(), (quantumModel n f).cost (.gate g)⟩ : AddWriter ℕ Unit),
        unitaryOf (gateOracle f) g ◃ ρ) := by
  rw [applyGate, Prog.runM_lift]
  simp only [ModelM.runQuery, AddWriterT.run_mk, StateT.run_map,
    quantumModel_evalQuery_gate, StateT.run_modify]
  exact PMF.pure_map _ _

/-- A program without measurements satisfies any postcondition that holds of its deterministic
result and final state. -/
theorem MeasurementFree.spec {n : ℕ} {α : Type} {P : Prog (QuantumQuery n) α}
    (hP : MeasurementFree P) (f : (Fin n → Fin 2) → Bool) (post : α → QState n → Prop) :
    letI := (quantumModel n f).hasHandler
    ⦃ fun ρ => post ((P.evalM (unitaryModel n f)).run ρ).1 ((P.evalM (unitaryModel n f)).run ρ).2 ⦄
      P ⦃ post ⦄ := by
  let _ := (quantumModel n f).hasHandler
  induction hP with
  | pure a => exact Triple.intro fun _ h => h
  | gate g _ ih =>
    apply Triple.intro
    intro ρ h p hp
    rw [(PMF.mem_support_pure_iff _ _).1 hp]
    exact ih.le_wp _ h

/-- Conjugate a register by a unitary, keeping matrix internals opaque to verification tactics. -/
@[irreducible] def evolveState {n : ℕ} (U : 𝐔[Fin n → Fin 2]) (ρ : QState n) : QState n :=
  U ◃ ρ

/-- The state update used by specifications is unitary conjugation. -/
theorem evolveState_eq {n : ℕ} (U : 𝐔[Fin n → Fin 2]) (ρ : QState n) :
    evolveState U ρ = U ◃ ρ := by
  unfold evolveState
  rfl

/-- A gate updates the hidden register by its unitary. -/
@[spec] theorem applyGate_spec {n : ℕ} (f : (Fin n → Fin 2) → Bool) (g : QuantumGate n)
    (post : Unit → QState n → Prop) :
    letI := (quantumModel n f).hasHandler
    ⦃ fun ρ => post () (evolveState (unitaryOf (gateOracle f) g) ρ) ⦄ applyGate g ⦃ post ⦄ := by
  simpa only [evolveState_eq, applyGate_evalM_unitaryModel] using
    (measurementFree_applyGate g).spec f post

/-- Measuring the register yields an outcome `x` in its Born support and leaves the register in
the basis state `x`. -/
@[spec] theorem measureRegister_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool)
    (post : (Fin n → Fin 2) → QState n → Prop) :
    letI := (quantumModel n f).hasHandler
    ⦃ fun ρ => ∀ x ∈ (bornPMF (measureRegisterPOVM n) ρ).support,
        post x (MState.pure (Ket.basis x)) ⦄ measureRegister n ⦃ post ⦄ := by
  let _ := (quantumModel n f).hasHandler
  vcgen [measureRegister]
  rename_i ρ h
  change ∀ p ∈ (((quantumModel n f).evalQuery .measureAll).run ρ).support, post p.1 p.2
  intro p hp
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff ..).mp hp
  exact h x hx

/-- Measuring qubit `q` yields an outcome `b` in its Born support and collapses the register onto
that outcome. -/
@[spec] theorem measureQubit_spec {n : ℕ} (f : (Fin n → Fin 2) → Bool) (q : Fin n)
    (post : Fin 2 → QState n → Prop) :
    letI := (quantumModel n f).hasHandler
    ⦃ fun ρ => ∀ b ∈ (bornPMF (measureQubitPOVM q) ρ).support,
        post b (collapse ((measureQubitPOVM q).mats b).mat ρ) ⦄ measureQubit q ⦃ post ⦄ := by
  let _ := (quantumModel n f).hasHandler
  vcgen [measureQubit]
  rename_i ρ h
  change ∀ p ∈ (((quantumModel n f).evalQuery (.measure q)).run ρ).support, post p.1 p.2
  intro p hp
  obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff ..).mp hp
  exact h b hb

end

end Algolean.Algorithms
