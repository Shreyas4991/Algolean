/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Functions
public import Algolean.Models.SingleTapeTM.Composition.Relabel
public import Algolean.Models.SingleTapeTM.Composition.Frame
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Composition across independently chosen finite control alphabets

The composed query program embeds both control alphabets into their disjoint sum and switches
to the second initial state at the boundary. It preserves the tape, head origin, allocated
storage, and visits. Output length and polynomial time use the existing query interpreter.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing Polynomial
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

section Execution

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Run a bounded computation from matching tape contents and control state, using the supplied
head coordinate and storage and visit records. The additional storage cost may change. -/
theorem OutputsWithinTime.runFrom {p : Prog (TMQuery tm) Unit} {input output : List Symbol}
    {time : ℕ} (h : OutputsWithinTime p input output time) {s : TMState tm}
    (hs : s.config = (TMState.init tm input).config) :
    ∃ cost final, Completes p s cost final ∧
      final.config.BiTape = BiTape.mk₁ output ∧ cost.steps ≤ time := by
  obtain ⟨fuel, result, final, hr, ht, hb⟩ := h
  have := execute_of_config_eq fuel p hs.symm hr
  grind [completes_of_execute]

/-- Prepare an input with a verified procedure, then run a bounded computation on its output.
The two programs share the actual intermediate machine state and their time bounds add. -/
theorem Computes.outputsWithinTime_seq {p q : Prog (TMQuery tm) Unit}
    {f : List Symbol → List Symbol} {time : List Symbol → ℕ} (h : Computes p f time)
    {input output : List Symbol} {budget : ℕ}
    (hq : OutputsWithinTime q (f input) output budget) :
    OutputsWithinTime (do p; q) input output (time input + budget) := by
  obtain ⟨moves, ⟨a, t, hp, ht, _, ha⟩, hb⟩ := h input (TMState.init tm input) rfl
  obtain ⟨b, u, hq, hu, hc⟩ := hq.runFrom (s := t)
    (by simp [ht, TMState.init, SingleTapeTM.initCfg])
  have := hp.seq hq
  grind [Completes, OutputsWithinTime]

end Execution

/-- Head-move time bounds the output size, including when a zero-move write fills an empty tape. -/
theorem OutputsWithinTime.output_length_le {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State] {p : Prog (TMQuery tm) Unit}
    {input output : List Symbol} {time : ℕ} (h : OutputsWithinTime p input output time) :
    output.length ≤ 1 + input.length + time := by
  obtain ⟨fuel, result, final, hr, ht, hb⟩ := h
  rw [execute_eq_runCode] at hr
  have := runCode_tapeExtent_le fuel _ _ _ _ hr
  simp only [ht, TMState.init_config, SingleTapeTM.initCfg, BiTape.spaceUsed_mk₁] at this
  lia

/-- Compose independently defined machines, explicitly initializing the second control alphabet. -/
def TimeComputable.comp {f g : List Symbol → List Symbol}
    (first : TimeComputable f) (second : TimeComputable g) (mono : Monotone second.timeBound) :
    TimeComputable (g ∘ f) := by
  letI := first.symbolDecidableEq
  letI := first.stateDecidableEq
  letI := second.stateDecidableEq
  letI : DecidableEq (SingleTapeTM.compComputer first.tm second.tm).State :=
    inferInstanceAs (DecidableEq (first.tm.State ⊕ second.tm.State))
  let joined := SingleTapeTM.compComputer first.tm second.tm
  let left : first.tm.State → joined.State := Sum.inl
  let right : second.tm.State → joined.State := Sum.inr
  exact {
    tm := joined
    program := do [TMQuery joined]
      relabelProg left first.program
      state ←ₜ right second.tm.q₀
      relabelProg right second.program
    timeBound n := first.timeBound n + second.timeBound (1 + n + first.timeBound n)
    outputsFunInTime input := by
      have hfirst := first.outputsFunInTime input
      have hsecond : OutputsWithinTime second.program (f input) (g (f input))
          (second.timeBound (f input).length) := by
        convert second.outputsFunInTime (f input) using 1
      have hlength := hfirst.output_length_le
      obtain ⟨_, a, t, ha, hatape, hatime⟩ := hfirst
      obtain ⟨_, b, u, hb, hbtape, hbtime⟩ := hsecond
      have hpa := (completes_of_execute ha).relabel left Sum.inl_injective
      have hpb := (completes_of_execute hb).relabel right Sum.inr_injective
      obtain ⟨fuel, hpb⟩ := hpb
      let mid := {t.machine.relabel left with config.state := some (right second.tm.q₀)}
      have hcfg : ((TMState.init second.tm (f input)).relabel right).config = mid.config := by
        simp [mid, TMState.relabel, TMState.init, SingleTapeTM.initCfg, hatape]
      obtain ⟨result, final, hrun, hfinal, htime, _⟩ := execute_of_config_eq fuel _ hcfg hpb
      have hc := hpa.seq ((completes_update (t.machine.relabel left) (right second.tm.q₀)).seq
        (completes_of_execute hrun))
      obtain ⟨budget, hbudget⟩ := hc
      refine ⟨budget, _, _, hbudget, ?_, ?_⟩
      · simpa [hfinal, TMState.relabel] using hbtape
      · simp only [TMCost.add_steps, zero_add, htime]
        exact Nat.add_le_add hatime (hbtime.trans (mono hlength)) }

/-- Replace a polynomial-time witness's bound by its polynomial, leaving its program fixed. -/
def PolyTimeComputable.polynomialBound {f : List Symbol → List Symbol}
    (machine : PolyTimeComputable f) : TimeComputable f where
  tm := machine.tm
  symbolDecidableEq := machine.symbolDecidableEq
  stateDecidableEq := machine.stateDecidableEq
  program := machine.program
  timeBound := machine.poly.eval
  outputsFunInTime input := by
    let := machine.symbolDecidableEq
    let := machine.stateDecidableEq
    exact (machine.outputsFunInTime input).mono (machine.bounds input.length)

/-- Uniform polynomial-time functions are closed under composition in the query model. -/
noncomputable def PolyTimeComputable.comp {f g : List Symbol → List Symbol}
    (first : PolyTimeComputable f) (second : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) where
  toTimeComputable := first.polynomialBound.comp second.polynomialBound
    (fun _ _ h => second.poly.eval_mono h)
  poly := first.poly + second.poly.comp (1 + X + first.poly)
  bounds _ := by simp [TimeComputable.comp, polynomialBound]

end Algolean.Algorithms.TMQuery
