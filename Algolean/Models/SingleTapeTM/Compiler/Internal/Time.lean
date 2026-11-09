/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Relating head-move counts to transition counts

Query programs charge time for head-move instructions. An ordinary Turing machine also spends
transitions on work that keeps the head still. This file bounds that additional work.

* While the head stays still, only the control state and the scanned symbol can change.
* These values range over a finite set, which bounds the stationary work needed between moves.
* The resulting transition bound is `C * moves + C`, where `C` depends only on the machine's
  states and tape symbols.

For a fixed machine, `C` is independent of input length.
The bound is affine in the charged move count.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler.Internal

open Cslib.Turing Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A stationary transition leaves the head in place and performs one ordinary machine step. -/
def Stationary (tm : SingleTapeTM Symbol) (a b : tm.Cfg) : Prop :=
  ∃ state, a.state = some state ∧ (tm.tr state a.BiTape.head).1.movement = none ∧
    tm.TransitionRelation a b

/-- Stationary transitions preserve the tape contents on both sides of the head. -/
theorem Stationary.sides {tm : SingleTapeTM Symbol} {a b : tm.Cfg} (h : Stationary tm a b) :
    b.BiTape.left = a.BiTape.left ∧ b.BiTape.right = a.BiTape.right := by
  obtain ⟨state, hstate, hmove, hstep⟩ := h
  cases a with
  | mk label tape =>
    change label = some state at hstate
    subst label
    simp only [SingleTapeTM.TransitionRelation, SingleTapeTM.step, hmove,
      BiTape.optionMove, Option.some.injEq] at hstep
    subst b
    exact ⟨rfl, rfl⟩

/-- A sequence of stationary transitions preserves the tape contents on both sides of the head. -/
theorem stationary_sides {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : ReflTransGen (Stationary tm) a b) :
    b.BiTape.left = a.BiTape.left ∧ b.BiTape.right = a.BiTape.right := by
  induction h with
  | refl => exact ⟨rfl, rfl⟩
  | tail _ hstep ih =>
    have hsides := hstep.sides
    exact ⟨hsides.1.trans ih.1, hsides.2.trans ih.2⟩

/-- This constant counts the possible control states and symbols under a stationary head. -/
def stationaryBound (tm : SingleTapeTM Symbol) : ℕ :=
  Fintype.card (Option tm.State × Option Symbol)

/-- A stationary endpoint can be reached in fewer transitions than the local finite-state count. -/
theorem stationary_steps_lt {tm : SingleTapeTM Symbol} {a b : tm.Cfg}
    (h : ReflTransGen (Stationary tm) a b) :
    ∃ steps < stationaryBound tm, RelatesInSteps (Stationary tm) a b steps := by
  classical
  let rebuild (labelAndSymbol : Option tm.State × Option Symbol) : tm.Cfg :=
    ⟨labelAndSymbol.1, {a.BiTape with head := labelAndSymbol.2}⟩
  have hsub : {c | ReflTransGen (Stationary tm) a c} ⊆ Set.range rebuild := by
    intro c hc
    obtain ⟨hleft, hright⟩ := stationary_sides hc
    refine ⟨(c.state, c.BiTape.head), ?_⟩
    cases c with
    | mk label tape =>
      cases tape
      simp_all [rebuild]
  obtain ⟨steps, hsteps, hlt⟩ := h.relatesInSteps_lt_encard
  have hcard : (Set.range rebuild).encard ≤ (stationaryBound tm : ℕ∞) := by
    rw [← Set.image_univ]
    exact (Set.encard_image_le _ _).trans_eq (by
      simp [stationaryBound, ENat.card_eq_coe_fintype_card])
  have hlt' : (steps : ℕ∞) < stationaryBound tm :=
    hlt.trans_le ((Set.encard_le_encard hsub).trans hcard)
  exact ⟨steps, ENat.natCast_lt_natCast.mp hlt', hsteps⟩

/--
A computation is divided into stationary stretches separated by a specified number of charged
transitions. A charged transition may also keep the head still, as a `.Stop` instruction does.
-/
inductive RunsWithMoves (tm : SingleTapeTM Symbol) : tm.Cfg → tm.Cfg → ℕ → Prop
  | stationary {a b} (h : ReflTransGen (Stationary tm) a b) : RunsWithMoves tm a b 0
  | move {a b c d moves} (before : ReflTransGen (Stationary tm) a b)
      (step : tm.TransitionRelation b c) (rest : RunsWithMoves tm c d moves) :
      RunsWithMoves tm a d (moves + 1)

/-- A stationary transition can precede a computation without adding a charged move. -/
theorem RunsWithMoves.prepend_stationary {tm : SingleTapeTM Symbol} {a b c : tm.Cfg} {moves : ℕ}
    (hstep : Stationary tm a b) (h : RunsWithMoves tm b c moves) : RunsWithMoves tm a c moves := by
  cases h with
  | stationary h => exact .stationary (.head hstep h)
  | move before step rest => exact .move (.head hstep before) step rest

/--
The total number of transitions has an affine bound in the number of charged moves. The
coefficient and constant term depend only on the machine's finite control and alphabet.
For a fixed machine, both are independent of input length.
-/
theorem RunsWithMoves.withinTime {tm : SingleTapeTM Symbol} {a b : tm.Cfg} {moves : ℕ}
    (h : RunsWithMoves tm a b moves) :
    RelatesWithinSteps tm.TransitionRelation a b (stationaryBound tm * (moves + 1)) := by
  induction h with
  | stationary h =>
    obtain ⟨steps, hlt, hsteps⟩ := stationary_steps_lt h
    refine ⟨steps, by simpa using hlt.le, ?_⟩
    exact hsteps.map id (fun _ _ hstep => hstep.choose_spec.2.2)
  | @move a b c d moves before step rest ih =>
    obtain ⟨steps, hlt, hsteps⟩ := stationary_steps_lt before
    have hp : RelatesWithinSteps tm.TransitionRelation _ _ steps :=
      ⟨steps, le_rfl, hsteps.map id (fun _ _ hstep => hstep.choose_spec.2.2)⟩
    refine RelatesWithinSteps.mono ?_ (hp.trans ((RelatesWithinSteps.single step).trans ih))
    simp only [Nat.mul_add, Nat.mul_one]
    lia

end Algolean.Algorithms.TMQuery.Compiler.Internal
