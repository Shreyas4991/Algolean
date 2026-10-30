/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Oracle
public import Std.Tactic.Do

/-!
# Quantum program specifications

Support-based specifications for the hidden-state quantum model. The `Std.Do` interpretation
`quantumWP` supplies `mvcgen` support alongside the model's `Std.WP` infrastructure. A triple
asserts that its postcondition holds for each result and final state in the program's support.
Measurement rules start from a fixed state and record both the observed outcome and the final
state, allowing verification to continue through subsequent queries.

## Main definitions

- `quantumWP`: the `Std.Do` interpretation of quantum programs.
- `evolveState`: conjugation of a register state, kept opaque during verification.

## Main results

- `quantumModel_spec_iff`: the support interpretation of a quantum program specification.
- `MeasurementFree.spec`: specifications from deterministic gate semantics.
- `applyGate_spec`, `measureRegister_spec`, `measureQubit_spec`: query rules for `mvcgen`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Std.Do
open scoped MState

noncomputable section

/-- The `Std.Do` weakest precondition of a distribution quantifies over its support. -/
instance instDoWPPMF : WP PMF .pure where
  wp x :=
    { trans := fun Q => ⟨∀ a ∈ x.support, (Q.1 a).down⟩
      conjunctiveRaw := by
        intro Q₁ Q₂
        simp only [SPred.bientails_nil, SPred.and_nil]
        grind }

/-- The support interpretation preserves pure computations and monadic sequencing. -/
instance instDoWPMonadPMF : WPMonad PMF .pure where
  wp_pure a := by
    apply PredTrans.ext
    intro Q
    rw [PredTrans.apply_Pure_pure]
    apply ULift.ext
    change (∀ b ∈ (PMF.pure a).support, (Q.1 b).down) = (Q.1 a).down
    simp only [PMF.mem_support_pure_iff, forall_eq]
  wp_bind x f := by
    apply PredTrans.ext
    intro Q
    rw [PredTrans.apply_Bind_bind]
    apply ULift.ext
    change (∀ b ∈ (x.bind f).support, (Q.1 b).down) =
      (∀ a ∈ x.support, ∀ b ∈ (f a).support, (Q.1 b).down)
    simp only [PMF.mem_support_bind_iff]
    grind

/-- Interpret quantum syntax through its hidden-state execution for `Std.Do` verification. -/
@[reducible] def quantumWP (n : ℕ) (f : (Fin n → Fin 2) → Bool) :
    WPMonad (Prog (QuantumQuery n)) (.arg (QState n) .pure) where
  wp P := wp (P.evalM (quantumModel n f))
  wp_pure a := by
    simpa only [Prog.evalM_pure] using (WPMonad.wp_pure (m := QuantumM n) a)
  wp_bind P k := by
    simpa only [Prog.evalM_bind] using
      (WPMonad.wp_bind (P.evalM (quantumModel n f)) (fun a => (k a).evalM (quantumModel n f)))

/-- A triple holds exactly when its postcondition holds for every result and final state in the
support of the program's execution from an initial state satisfying its precondition. -/
theorem quantumModel_spec_iff {n : ℕ} {α : Type} (f : (Fin n → Fin 2) → Bool)
    (P : Prog (QuantumQuery n) α) (pre : Assertion (.arg (QState n) .pure))
    (post : PostCond α (.arg (QState n) .pure)) :
    (letI := quantumWP n f; Triple P pre post) ↔
      ∀ ρ, (pre ρ).down → ∀ p ∈ (P.evalM (quantumModel n f)).run ρ |>.support,
        (post.1 p.1 p.2).down := Iff.rfl

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
    (hP : MeasurementFree P) (f : (Fin n → Fin 2) → Bool)
    (post : PostCond α (.arg (QState n) .pure)) :
    letI := quantumWP n f
    Triple P (fun ρ =>
      post.1 ((P.evalM (unitaryModel n f)).run ρ).1
        ((P.evalM (unitaryModel n f)).run ρ).2) post := by
  apply (quantumModel_spec_iff f _ _ _).mpr
  intro ρ h p hp
  have hp' : p = (P.evalM (unitaryModel n f)).run ρ := by
    simpa only [evalM_quantumModel_of_measurementFree hP,
      PMF.mem_support_pure_iff] using hp
  simpa only [hp'] using h

/-- Conjugate a register by a unitary, keeping matrix internals opaque to verification tactics. -/
@[irreducible] def evolveState {n : ℕ} (U : 𝐔[Fin n → Fin 2]) (ρ : QState n) : QState n :=
  U ◃ ρ

/-- The state update used by specifications is unitary conjugation. -/
theorem evolveState_eq {n : ℕ} (U : 𝐔[Fin n → Fin 2]) (ρ : QState n) :
    evolveState U ρ = U ◃ ρ := by
  unfold evolveState
  rfl

/-- A gate's verification rule updates the hidden register by its unitary. -/
@[spec] theorem applyGate_spec {n : ℕ} (f : (Fin n → Fin 2) → Bool) (g : QuantumGate n)
    (post : PostCond Unit (.arg (QState n) .pure)) :
    letI := quantumWP n f
    Triple (applyGate g)
      (fun ρ => post.1 () (evolveState (unitaryOf (gateOracle f) g) ρ)) post := by
  simpa only [evolveState_eq, applyGate_evalM_unitaryModel] using
    (measurementFree_applyGate g).spec f post

/-- Measuring the register from `ρ₀` yields an outcome in its Born support and leaves the
register in the corresponding basis state. -/
@[spec] theorem measureRegister_spec (n : ℕ) (f : (Fin n → Fin 2) → Bool) (ρ₀ : QState n) :
    letI := quantumWP n f
    ⦃fun ρ => ⌜ρ = ρ₀⌝⦄ measureRegister n
    ⦃⇓ x ρ => ⌜x ∈ (bornPMF (measureRegisterPOVM n) ρ₀).support ∧
        ρ = MState.pure (Ket.basis x)⌝⦄ := by
  apply (quantumModel_spec_iff f _ _ _).mpr
  intro ρ h p hp
  simp only [measureRegister, Prog.evalM_lift, quantumModel_evalQuery_measureAll,
    measureRegisterM, StateT.run] at hp
  obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff ..).mp hp
  cases h
  exact ⟨hx, rfl⟩

/-- Measuring qubit `q` from `ρ₀` yields an outcome in its Born support and collapses the
register onto that outcome. -/
@[spec] theorem measureQubit_spec {n : ℕ} (f : (Fin n → Fin 2) → Bool)
    (q : Fin n) (ρ₀ : QState n) :
    letI := quantumWP n f
    ⦃fun ρ => ⌜ρ = ρ₀⌝⦄ measureQubit q
    ⦃⇓ b ρ => ⌜b ∈ (bornPMF (measureQubitPOVM q) ρ₀).support ∧
        ρ = collapse ((measureQubitPOVM q).mats b).mat ρ₀⌝⦄ := by
  apply (quantumModel_spec_iff f _ _ _).mpr
  intro ρ h p hp
  simp only [measureQubit, Prog.evalM_lift, quantumModel_evalQuery_measure,
    measureQubitM, StateT.run] at hp
  obtain ⟨b, hb, rfl⟩ := (PMF.mem_support_map_iff ..).mp hp
  cases h
  exact ⟨hb, rfl⟩

end

end Algolean.Algorithms
