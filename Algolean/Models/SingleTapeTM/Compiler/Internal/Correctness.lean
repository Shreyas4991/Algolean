/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Internal.Machine
public import Algolean.Models.SingleTapeTM.Compiler.Internal.Time
public import Algolean.Models.SingleTapeTM.Computability

/-!
# Relating query execution to compiled machine execution

This file proves that the compiler preserves termination and the complete output tape.

* A successful query execution produces a compiled computation with the same charged moves.
* Every halting compiled computation comes from a successful query execution.
* The bound on stationary work converts a query time bound into an affine transition bound.

For a fixed source program, logical label type, and alphabet, the coefficient and constant term
are independent of input length. Thus a source time bound `T(n)` becomes `C * T(n) + C`.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler.Internal

open Cslib Cslib.Turing Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A query that does not charge a move compiles to a stationary machine transition. -/
theorem stationary_query (program : Program tm) (query : TMQuery tm α) (next : α → Program tm)
    (h : (.liftBind query next : Program tm) ∈ programPositions program) (s : TMState tm)
    (hcost : (TMQuery.step query next s).cost.steps = 0) :
    Stationary (machine program) (encodeCfg program (.liftBind query next) h s.config)
      (encodeCfg program (TMQuery.step query next s).program
        (advance_eq_step_program query next s ▸
          advance_mem_programPositions program (.liftBind query next) h _ _)
        (TMQuery.step query next s).machine.config) := by
  refine ⟨(position program (.liftBind query next) h, s.config.state), rfl, ?_,
    machine_step program query next h s⟩
  cases query with
  | move direction => simp [TMQuery.step] at hcost
  | write value => simp [machine, encodeCfg, position, action, -FreeM.liftBind_eq]
  | update state => simp [machine, encodeCfg, position, action, -FreeM.liftBind_eq]
  | branchCode condition yes no =>
    simp [machine, encodeCfg, position, action, -FreeM.liftBind_eq]
  | whileCode condition body =>
    simp [machine, encodeCfg, position, action, -FreeM.liftBind_eq]

/-- Finishing the query program adds one stationary transition that halts the compiled machine. -/
theorem stationary_halt (program : Program tm)
    (h : (pure () : Program tm) ∈ programPositions program) (cfg : tm.Cfg) :
    Stationary (machine program) (encodeCfg program (pure ()) h cfg) ⟨none, cfg.BiTape⟩ := by
  exact ⟨(position program (pure ()) h, cfg.state), rfl,
    by simp [machine, position, action, ← FreeM.pure_eq_pure], machine_halt program h cfg⟩

/-- Successful query execution becomes a compiled computation with the same charged move count. -/
theorem execute_runsWithMoves (program : Program tm) (fuel : ℕ) (pending : Program tm)
    (hp : pending ∈ programPositions program) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : execute fuel pending s = some (result, final)) :
    RunsWithMoves (machine program) (encodeCfg program pending hp s.config)
      ⟨none, final.machine.config.BiTape⟩ result.tell.steps := by
  induction fuel generalizing pending s result final with
  | zero =>
    cases pending with
    | pure value =>
      cases value
      simp only [FreeM.pure_eq_pure, execute, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .stationary (.single (stationary_halt program hp s.config))
    | liftBind query next =>
      simp only [execute, FuelExecMonad.execute_zero_liftBind] at h
      cases h
  | succ fuel ih =>
    cases pending with
    | pure value =>
      cases value
      simp only [FreeM.pure_eq_pure, execute, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .stationary (.single (stationary_halt program hp s.config))
    | liftBind query next =>
      rw [execute, FuelExecMonad.execute_liftBind_succ] at h
      cases hr : execute fuel (TMQuery.step query next s).program
          (TMQuery.step query next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        change (do
          let (result, final) ← execute fuel (TMQuery.step query next s).program
            (TMQuery.step query next s).machine
          pure ((⟨result.ret, (TMQuery.step query next s).cost + result.tell⟩ :
            AddWriter TMCost Unit), final)) = _ at h
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem := advance_eq_step_program query next s ▸
          advance_mem_programPositions program (.liftBind query next) hp
            s.config.state s.config.BiTape.head
        have hrest := ih _ hmem _ _ _ hr
        have hstep := machine_step program query next hp s
        cases query with
        | move direction =>
          simpa [TMQuery.step, Nat.add_comm] using
            (RunsWithMoves.move .refl hstep hrest)
        | write value =>
          simpa [TMQuery.step] using hrest.prepend_stationary
            (stationary_query program (.write value) next hp s rfl)
        | update state =>
          simpa [TMQuery.step] using hrest.prepend_stationary
            (stationary_query program (.update state) next hp s rfl)
        | branchCode condition yes no =>
          simpa [TMQuery.step] using hrest.prepend_stationary
            (stationary_query program (.branchCode condition yes no) next hp s rfl)
        | whileCode condition body =>
          simpa [TMQuery.step] using hrest.prepend_stationary
            (stationary_query program (.whileCode condition body) next hp s rfl)

omit [DecidableEq Symbol] in
/-- A halting machine configuration cannot take any further transitions. -/
theorem terminal_steps {compiled : SingleTapeTM Symbol} {tape : BiTape Symbol}
    {final : compiled.Cfg} {steps : ℕ}
    (h : RelatesInSteps compiled.TransitionRelation ⟨none, tape⟩ final steps) :
    final = ⟨none, tape⟩ := by
  cases steps with
  | zero => exact h.zero.symm
  | succ steps =>
    obtain ⟨_, hstep, _⟩ := h.succ'
    simp [SingleTapeTM.TransitionRelation] at hstep

/-- A halting compiled computation can be reconstructed as a successful query execution. -/
theorem execute_of_machine_steps (program : Program tm) (steps : ℕ) (pending : Program tm)
    (hp : pending ∈ programPositions program) (s : TMState tm) (tape : BiTape Symbol)
    (h : RelatesInSteps (machine program).TransitionRelation
      (encodeCfg program pending hp s.config) ⟨none, tape⟩ steps) :
    ∃ fuel result final, execute fuel pending s = some (result, final) ∧
      final.machine.config.BiTape = tape := by
  induction steps generalizing pending s with
  | zero =>
    have heq := congrArg SingleTapeTM.Cfg.state h.zero
    simp [encodeCfg] at heq
  | succ steps ih =>
    obtain ⟨middle, hfirst, hrest⟩ := h.succ'
    cases pending with
    | pure value =>
      cases value
      change (machine program).step _ = _ at hfirst
      have hhalt := machine_halt program hp s.config
      simp only [← FreeM.pure_eq_pure] at hhalt
      rw [hhalt] at hfirst
      cases Option.some.inj hfirst
      have htape := congrArg SingleTapeTM.Cfg.BiTape (terminal_steps hrest)
      exact ⟨0, ⟨(), 0⟩, ⟨s, 0⟩, rfl, htape.symm⟩
    | liftBind query next =>
      change (machine program).step _ = _ at hfirst
      rw [machine_step program query next hp s] at hfirst
      cases Option.some.inj hfirst
      obtain ⟨fuel, result, final, hrun, htape⟩ := ih _ _ _ hrest
      refine ⟨fuel + 1, ⟨result.ret, (TMQuery.step query next s).cost + result.tell⟩,
        final, ?_, htape⟩
      rw [execute, FuelExecMonad.execute_liftBind_succ]
      change (do
        let (result, final) ← execute fuel (TMQuery.step query next s).program
          (TMQuery.step query next s).machine
        pure ((⟨result.ret, (TMQuery.step query next s).cost + result.tell⟩ :
          AddWriter TMCost Unit), final)) = _
      rw [hrun]
      rfl

/--
Compilation preserves output words and gives an affine bound on machine transitions.
For a fixed source program, logical label type, and alphabet, both constants are independent
of input length.
-/
theorem outputsWithinTime (program : Program tm) {input output : List Symbol} {time : ℕ}
    (h : OutputsWithinTime program input output time) :
    (machine program).OutputsWithinTime input output
      (stationaryBound (machine program) * (time + 1)) := by
  obtain ⟨fuel, result, final, hrun, htape, htime⟩ := h
  have hcompiled := execute_runsWithMoves program fuel program (mem_programPositions program)
    (TMState.init tm input) result final hrun
  have hbound := hcompiled.withinTime
  simp only [TMState.init_config, encodeCfg_init, htape] at hbound
  exact hbound.mono (Nat.mul_le_mul_left _ (Nat.add_le_add_right htime 1))

/-- A compiled output word comes from a successful query execution with the same output. -/
theorem outputs_iff (program : Program tm) (input output : List Symbol) :
    (machine program).Outputs input output ↔
      ∃ time, OutputsWithinTime program input output time := by
  constructor
  · intro h
    obtain ⟨steps, hsteps⟩ := h.relatesInSteps
    rw [← encodeCfg_init program input] at hsteps
    obtain ⟨fuel, result, final, hrun, htape⟩ := execute_of_machine_steps program steps program
      (mem_programPositions program) (TMState.init tm input) _ hsteps
    exact ⟨result.tell.steps, fuel, result, final, hrun, htape, le_rfl⟩
  · rintro ⟨time, h⟩
    exact (outputsWithinTime program h).choose_spec.2.reflTransGen

end Algolean.Algorithms.TMQuery.Compiler.Internal
