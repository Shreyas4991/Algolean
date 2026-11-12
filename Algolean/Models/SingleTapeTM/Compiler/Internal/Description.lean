/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Description
import Mathlib.Data.Fintype.EquivFin

/-!
# Numbering the states of a transition-table machine

This file represents a finite single-tape machine using numbered states.
Renaming the states preserves every transition, the initial configuration, and the halting tape.
It therefore preserves execution times exactly.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler.Internal

open Cslib.Turing Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- The machine's finite state type is assigned consecutive natural-number labels. -/
noncomputable def stateEquiv (tm : SingleTapeTM Symbol) :
    tm.State ≃ Fin (Fintype.card tm.State - 1 + 1) :=
  Fintype.equivFinOfCardEq (by
    have hpos : 0 < Fintype.card tm.State := Fintype.card_pos_iff.mpr ⟨tm.q₀⟩
    lia)

/-- This description records the same transitions after numbering the original control states. -/
noncomputable def describe (tm : SingleTapeTM Symbol) : SingleTapeTM.Description Symbol where
  states := Fintype.card tm.State - 1
  initial := stateEquiv tm tm.q₀
  transition state symbol :=
    let (statement, next) := tm.tr ((stateEquiv tm).symm state) symbol
    (statement.symbol, statement.movement.map (fun direction =>
      match direction with | .left => false | .right => true), next.map (stateEquiv tm))

/-- Numbering the control states leaves the tape unchanged. -/
noncomputable def cfgEquiv (tm : SingleTapeTM Symbol) : tm.Cfg ≃ (describe tm).machine.Cfg where
  toFun cfg := ⟨cfg.state.map (stateEquiv tm), cfg.BiTape⟩
  invFun cfg := ⟨cfg.state.map (stateEquiv tm).symm, cfg.BiTape⟩
  left_inv cfg := by
    cases cfg with
    | mk label tape =>
      cases label with
      | none => rfl
      | some state =>
        change (⟨some ((stateEquiv tm).symm (stateEquiv tm state)), tape⟩ : tm.Cfg) = _
        rw [Equiv.symm_apply_apply]
  right_inv cfg := by
    cases cfg with
    | mk label tape =>
      cases label with
      | none => rfl
      | some state =>
        change Fin (Fintype.card tm.State - 1 + 1) at state
        change (⟨some (stateEquiv tm ((stateEquiv tm).symm state)), tape⟩ :
          (describe tm).machine.Cfg) = _
        rw [Equiv.apply_symm_apply]

/-- Renaming a configuration changes only its control-state label. -/
theorem cfgEquiv_apply (tm : SingleTapeTM Symbol) (label : Option tm.State)
    (tape : BiTape Symbol) : cfgEquiv tm ⟨label, tape⟩ =
      ⟨label.map (stateEquiv tm), tape⟩ := rfl

/-- Converting a direction to a Boolean value and back preserves left, right, and no movement. -/
theorem movement_roundTrip (movement : Option _root_.Turing.Dir) :
    (movement.map (fun direction => match direction with | .left => false | .right => true)).map
      (fun right => if right then _root_.Turing.Dir.right else .left) = movement := by
  cases movement with
  | none => rfl
  | some direction => cases direction <;> rfl

/-- Renaming the control states commutes with one ordinary machine transition. -/
theorem describe_step (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    (tm.step cfg).map (cfgEquiv tm) = (describe tm).machine.step (cfgEquiv tm cfg) := by
  cases cfg with
  | mk label tape =>
    cases label with
    | none => rfl
    | some state =>
      change some (⟨((tm.tr state tape.head).2).map (stateEquiv tm),
        (tape.write (tm.tr state tape.head).1.symbol).optionMove
          (tm.tr state tape.head).1.movement⟩ : (describe tm).machine.Cfg) =
        some ⟨((tm.tr ((stateEquiv tm).symm (stateEquiv tm state)) tape.head).2).map
          (stateEquiv tm),
          (tape.write
            (tm.tr ((stateEquiv tm).symm (stateEquiv tm state)) tape.head).1.symbol).optionMove
              (((tm.tr ((stateEquiv tm).symm (stateEquiv tm state)) tape.head).1.movement.map
                (fun direction => match direction with | .left => false | .right => true)).map
                  (fun right => if right then _root_.Turing.Dir.right else .left))⟩
      rw [Equiv.symm_apply_apply, movement_roundTrip]

/-- A transition holds before state renaming exactly when the renamed transition holds. -/
theorem describe_transition_iff (tm : SingleTapeTM Symbol) (a b : tm.Cfg) :
    tm.TransitionRelation a b ↔
      (describe tm).machine.TransitionRelation (cfgEquiv tm a) (cfgEquiv tm b) := by
  change tm.step a = some b ↔ (describe tm).machine.step (cfgEquiv tm a) = some (cfgEquiv tm b)
  rw [← describe_step]
  exact (Option.map_injective (cfgEquiv tm).injective).eq_iff.symm

/-- State renaming preserves the exact number of transitions between any two configurations. -/
theorem describe_steps_iff (tm : SingleTapeTM Symbol) (a b : tm.Cfg) (steps : ℕ) :
    RelatesInSteps tm.TransitionRelation a b steps ↔
      RelatesInSteps (describe tm).machine.TransitionRelation (cfgEquiv tm a) (cfgEquiv tm b)
        steps := by
  constructor
  · intro h
    exact h.map (cfgEquiv tm) (fun a b hab => (describe_transition_iff tm a b).mp hab)
  · intro h
    have hinverse : ∀ a b, (describe tm).machine.TransitionRelation a b →
        tm.TransitionRelation ((cfgEquiv tm).symm a) ((cfgEquiv tm).symm b) := by
      intro a b hab
      apply (describe_transition_iff tm _ _).mpr
      simpa only [Equiv.apply_symm_apply] using hab
    simpa only [Equiv.symm_apply_apply] using h.map (cfgEquiv tm).symm hinverse

/-- Numbering the machine states preserves every time-bounded output statement. -/
theorem describe_outputsWithinTime_iff (tm : SingleTapeTM Symbol) (input output : List Symbol)
    (time : ℕ) : (describe tm).machine.OutputsWithinTime input output time ↔
      tm.OutputsWithinTime input output time := by
  change (∃ steps ≤ time, RelatesInSteps (describe tm).machine.TransitionRelation
    ((describe tm).machine.initCfg input) ((describe tm).machine.haltCfg output) steps) ↔ _
  have hinit : cfgEquiv tm (tm.initCfg input) = (describe tm).machine.initCfg input := rfl
  have hhalt : cfgEquiv tm (tm.haltCfg output) = (describe tm).machine.haltCfg output := rfl
  simp only [← hinit, ← hhalt, ← describe_steps_iff, SingleTapeTM.OutputsWithinTime,
    RelatesWithinSteps]

end Algolean.Algorithms.TMQuery.Compiler.Internal
