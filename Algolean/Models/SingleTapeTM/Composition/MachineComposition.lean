/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Functions
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.Relabel
public import Algolean.Models.SingleTapeTM.Composition.Frame
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Running independently defined machines in sequence

This file combines programs written for different machines. It gives their states distinct
names, runs the first program, and then starts the second in its own initial state on the first
program's output tape. The programs run one after the other.

[Sequential.lean](Algolean/Models/SingleTapeTM/Composition/Sequential.html) joins procedures
that already use the same machine states. This file handles different machines and proves time
bounds in terms of the original input length. The bound accounts for the length of the first
output. In particular, composing two functions computed in polynomial time gives another
function computed in polynomial time.

## Main definitions and results

* [OutputsWithinTime.runFrom](##Algolean.Algorithms.TMQuery.OutputsWithinTime.runFrom) reuses a
  computation with different records of head position and tape use.
* [output_length_le](##Algolean.Algorithms.TMQuery.OutputsWithinTime.output_length_le)
  bounds the output length.
* [TimeComputable.comp](##Algolean.Algorithms.TMQuery.TimeComputable.comp) combines two machines
  and adds their time bounds.
* [PolyTimeComputable.comp](##Algolean.Algorithms.TMQuery.PolyTimeComputable.comp) proves that
  the combined time has a polynomial bound.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing Polynomial
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

section Execution

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
A completed computation can be run with different recorded head coordinates and tape use,
provided its starting tape and state label are the same. Its output tape and number of head
moves stay the same. The number of newly counted tape cells may change.
-/
theorem OutputsWithinTime.runFrom {p : Prog (TMQuery tm) Unit} {input output : List Symbol}
    {time : ℕ} (h : OutputsWithinTime p input output time) {s : TMState tm}
    (hs : s.config = (TMState.init tm input).config) :
    ∃ cost final, Completes p s cost final ∧
      final.config.BiTape = BiTape.mk₁ output ∧ cost.steps ≤ time := by
  obtain ⟨fuel, result, final, hr, ht, hb⟩ := h
  have := execute_of_config_eq fuel p hs.symm hr
  grind [completes_of_execute]

/--
A program can prepare the input for a second program and then run that program on the resulting
tape. The time required adds up, and both programs use the actual intermediate machine state.
-/
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

/--
The output has at most one cell plus the input length plus the allowed number of head moves. The
extra cell accounts for writing a symbol on an empty input without moving the head.
-/
theorem OutputsWithinTime.output_length_le {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State] {p : Prog (TMQuery tm) Unit}
    {input output : List Symbol} {time : ℕ} (h : OutputsWithinTime p input output time) :
    output.length ≤ 1 + input.length + time := by
  obtain ⟨fuel, result, final, hr, ht, hb⟩ := h
  have := execute_tapeExtent_le fuel _ _ _ _ hr
  simp only [ht, TMState.init_config, SingleTapeTM.initCfg, BiTape.spaceUsed_mk₁] at this
  lia

/--
This construction runs the first program to completion and then runs the second program on its
output. The programs may use different machine states; the construction gives them distinct
state names and sets the second program's initial state before starting it.

The resulting time bound adds the first program's time to the second program's time at an upper
bound on the intermediate output length. The second bound must not decrease as its input length
grows.
-/
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
      first.program.reduceProg (relabelReduction left)
      state ←ₜ right second.tm.q₀
      second.program.reduceProg (relabelReduction right)
    timeBound n := first.timeBound n + second.timeBound (1 + n + first.timeBound n)
    computesWithin := by
      apply TMQuery.ComputesWithin.of_outputsWithinTime
      intro input
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

/--
This construction uses the supplied polynomial as the time bound for the same program. The
existing proof that the polynomial bounds execution justifies the change.
-/
def PolyTimeComputable.polynomialBound {f : List Symbol → List Symbol}
    (machine : PolyTimeComputable f) : TimeComputable f where
  tm := machine.tm
  symbolDecidableEq := machine.symbolDecidableEq
  stateDecidableEq := machine.stateDecidableEq
  program := machine.program
  timeBound := machine.poly.eval
  computesWithin := machine.computesWithin_poly

/--
Two programs that compute functions in polynomial time can be run in sequence to compute the
composed function in polynomial time. The resulting bound accounts for both execution times and
the length of the first output.
-/
noncomputable def PolyTimeComputable.comp {f g : List Symbol → List Symbol}
    (first : PolyTimeComputable f) (second : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) where
  toTimeComputable := first.polynomialBound.comp second.polynomialBound
    (fun _ _ h => second.poly.eval_mono h)
  poly := first.poly + second.poly.comp (1 + X + first.poly)
  bounds _ := by simp [TimeComputable.comp, polynomialBound]

/--
This runs the original computation on nonempty inputs. On the empty input it writes the single
symbol `fallback` instead. The initial test and this stationary write add no head moves.
-/
def TimeComputable.onNonempty {f : List Symbol → List Symbol} (computer : TimeComputable f)
    (fallback : Symbol) :
    TimeComputable (fun input => if input.isEmpty then [fallback] else f input) := by
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  exact {
    tm := computer.tm
    program := do [TMQuery computer.tm]
      ifₜ tape =ₜ none then
        tape ←ₜ some fallback
      else
        computer.program
    timeBound := computer.timeBound
    computesWithin := by
      apply TMQuery.ComputesWithin.of_outputsWithinTime
      intro input
      cases input with
      | nil =>
        let s := TMState.init computer.tm []
        have hc : Completes
            (branch (.tapeIs none) (FreeM.lift (.write (some fallback))) computer.program)
            s 0 (s.write (some fallback)) := by
          apply Completes.branch
          simpa [s, TMState.init, SingleTapeTM.initCfg, BiTape.mk₁, BiTape.nil] using
            completes_write s (some fallback)
        exact hc.outputsWithinTime rfl (Nat.zero_le _)
      | cons symbol rest =>
        obtain ⟨fuel, result, final, hr, htape, htime⟩ :=
          computer.outputsFunInTime (symbol :: rest)
        have hc : Completes
            (branch (.tapeIs none) (FreeM.lift (.write (some fallback))) computer.program)
            (TMState.init computer.tm (symbol :: rest)) result.tell final.machine := by
          apply Completes.branch
          simpa [TMState.init, SingleTapeTM.initCfg, BiTape.mk₁] using completes_of_execute hr
        exact hc.outputsWithinTime htape htime }

/-- Replacing a polynomial-time computation's answer on the empty input preserves its time bound. -/
def PolyTimeComputable.onNonempty {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) (fallback : Symbol) :
    PolyTimeComputable (fun input => if input.isEmpty then [fallback] else f input) where
  toTimeComputable := computer.toTimeComputable.onNonempty fallback
  poly := computer.poly
  bounds := computer.bounds

end Algolean.Algorithms.TMQuery
