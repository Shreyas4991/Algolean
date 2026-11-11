/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.While
public import Algolean.Models.SingleTapeTM.Composition.Frame

/-!
# Compiling transition-table Turing machines to query programs

* `machine` uses the source machine's state names and one extra name recording that it has halted.
  A source machine with `Q` states therefore gives a query machine with `Q + 1` state names.
* `compile` repeatedly tests the current state and tape symbol, then performs the selected
  transition's write, movement, and state update. These tests form one fixed finite program.
* `correct` preserves and reflects output and termination, and `time_bound` preserves time bounds
  exactly in the reverse direction.
* `TimeComputable.toQuery` and `PolyTimeComputable.toQuery` preserve the computed function and
  source time bound. `polyTimeComputable_iff` relates the two notions of polynomial time.
* Each source transition uses one query move instruction. A stationary transition uses `Stop`,
  which leaves the head in place and is charged one unit by the query model.

The tape alphabet is unchanged. The source machine and its finite sets of states and symbols
are fixed before execution; input contents and input length do not choose a different program.
-/

public section

namespace Algolean.Algorithms.TMQuery.Compiler.ToQuery

open Cslib Cslib.Turing Relation

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
This supplies the query program's control labels. `some q` records a source state, and `none`
records that the source machine has halted. Its transition table is unused by query execution.
-/
abbrev machine (tm : SingleTapeTM Symbol) : SingleTapeTM Symbol where
  State := Option tm.State
  q₀ := some tm.q₀
  tr _ symbol := (⟨symbol, none⟩, none)

/-- The query machine needs exactly one more state name than the source machine. -/
theorem state_count (tm : SingleTapeTM Symbol) :
    Fintype.card (machine tm).State = Fintype.card tm.State + 1 := by
  simp [machine]

variable (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State]

/-- This describes a source configuration using the query machine's control labels. -/
private def encode (cfg : tm.Cfg) : (machine tm).Cfg := ⟨some cfg.state, cfg.BiTape⟩

/-- A stationary source transition uses a charged instruction that keeps the head in place. -/
private def direction : Option _root_.Turing.Dir → Dir
  | none => .Stop
  | some .left => .Left
  | some .right => .Right

/--
For one fixed entry of the transition table, this writes its symbol, moves as specified, and
records the next source state or the source machine's halt. Its arguments choose an instruction
block when compiling the machine; the running program finds the entry through finite tests.
-/
private def action (label : tm.State) (symbol : Option Symbol) :
    Prog (TMQuery (machine tm)) Unit := do
  FreeM.lift (.write (tm.tr label symbol).1.symbol)
  FreeM.lift (.move (direction (tm.tr label symbol).1.movement))
  FreeM.lift (.update (tm.tr label symbol).2)

/-- This lists every value of a finite type once, when the program is constructed. -/
private noncomputable def values (α : Type) [Fintype α] : List α := Finset.univ.toList

/-- Every value is included among the fixed cases tested by the compiled program. -/
private theorem mem_values {α : Type} [Fintype α] (a : α) : a ∈ values α := by
  classical
  simp [values]

/-- This finds the current symbol, including blank, and executes that state's table entry. -/
private noncomputable def forState (label : tm.State) : Prog (TMQuery (machine tm)) Unit :=
  select (values (Option Symbol)) TMCondition.tapeIs (action tm label)

/-- This finds the current source state and then tests the scanned symbol. -/
private noncomputable def body : Prog (TMQuery (machine tm)) Unit :=
  select (values tm.State) (fun label => .stateIs (some (some label))) (forState tm)

/--
This fixed query program executes the supplied transition table until the source machine halts.
It uses the same tape symbols and leaves the source machine's final tape under the same head.
Its only extra control label records halting. Every source transition costs one query move
instruction, including stationary transitions, which use the charged `Stop` instruction.
-/
noncomputable def compile : Prog (TMQuery (machine tm)) Unit :=
  whileLoop (.not (.stateIs (some none))) (body tm)

/-- One table entry gives the source's next configuration and costs exactly one move instruction. -/
private theorem action_correct (label : tm.State) (s : TMState (machine tm)) :
    ∃ cost final, Completes (action tm label s.config.BiTape.head) s cost final ∧
      some final.config = (tm.step ⟨some label, s.config.BiTape⟩).map (encode tm) ∧
      cost.steps = 1 := by
  let entry := tm.tr label s.config.BiTape.head
  let written := s.write entry.1.symbol
  let moved := written.move (direction entry.1.movement)
  let final : TMState (machine tm) := {moved with config.state := some entry.2}
  refine ⟨0 + written.moveCost (direction entry.1.movement) + 0, final, ?_, ?_, ?_⟩
  · exact ((completes_write s entry.1.symbol).seq
      (completes_move written (direction entry.1.movement))).seq
        (completes_update moved entry.2)
  · cases hdir : (tm.tr label s.config.BiTape.head).1.movement with
    | none => simp [final, moved, written, TMState.move, TMState.write, direction, encode,
        SingleTapeTM.step, entry, hdir, BiTape.optionMove]
    | some dir => cases dir <;>
        simp [final, moved, written, TMState.move, TMState.write, direction, encode,
          SingleTapeTM.step, entry, hdir, BiTape.optionMove, BiTape.move]
  · simp [TMState.moveCost]

/-- The finite state and symbol tests select the table entry matching the actual configuration. -/
private theorem body_correct (cfg next : tm.Cfg) (s : TMState (machine tm))
    (hs : s.config = encode tm cfg) (hstep : tm.step cfg = some next) :
    ∃ cost final, Completes (body tm) s cost final ∧
      final.config = encode tm next ∧ cost.steps = 1 := by
  cases cfg with
  | mk label tape =>
    cases label with
    | none => simp at hstep
    | some label =>
      obtain ⟨cost, final, hr, hf, ht⟩ := action_correct tm label s
      have htape : s.config.BiTape = tape := by simp [hs, encode]
      have hsymbols : Completes (forState tm label) s cost final := by
        apply select_correct _ _ _ s.config.BiTape.head s final cost (mem_values _) _ hr
        intro candidate
        simp [eq_comm]
      refine ⟨cost, final, ?_, ?_, ht⟩
      · apply select_correct _ _ _ label s final cost (mem_values _) _ hsymbols
        intro candidate
        simp [hs, encode, eq_comm]
      · rw [htape, hstep] at hf
        exact Option.some.inj hf

/-- A terminating source computation gives a completed query loop with the same transition count. -/
private theorem run_forward {cfg last : tm.Cfg} {steps : ℕ}
    (hr : RelatesInSteps tm.TransitionRelation cfg last steps)
    (hhalt : last.state = none) (s : TMState (machine tm)) (hs : s.config = encode tm cfg) :
    ∃ cost final, Completes (compile tm) s cost final ∧
      final.config = encode tm last ∧ cost.steps = steps := by
  induction hr using RelatesInSteps.head_induction_on generalizing s with
  | hrefl =>
    exact ⟨0, s, completes_while_false _ _ _ (by simp [hs, encode, hhalt]), hs, rfl⟩
  | @hhead cfg next n hstep hrest ih =>
    obtain ⟨a, middle, hbody, hmiddle, ha⟩ := body_correct tm cfg next s hs hstep
    obtain ⟨b, final, hrun, hfinal, hb⟩ := ih middle hmiddle
    have hnonhalt : cfg.state ≠ none := by
      intro h
      cases cfg
      simp_all [SingleTapeTM.TransitionRelation]
    refine ⟨a + b, final, Completes.while_step ?_ hbody hrun, hfinal, ?_⟩
    · simp [hs, encode, hnonhalt]
    · simp [ha, hb, Nat.add_comm]

/-- A completed query loop traces a source computation ending in the source halt label. -/
private theorem run_backward (fuel : ℕ) (cfg : tm.Cfg) (s : TMState (machine tm))
    (hs : s.config = encode tm cfg) (result : AddWriter TMCost Unit)
    (final : ExecutionState (machine tm))
    (hr : execute fuel (compile tm) s = some (result, final)) :
    RelatesInSteps tm.TransitionRelation cfg ⟨none, final.machine.config.BiTape⟩ result.tell.steps ∧
      final.machine.config.state = some none := by
  induction fuel using Nat.strong_induction_on generalizing cfg s result final with
  | h fuel ih =>
    cases fuel with
    | zero => simp [compile] at hr
    | succ fuel =>
      cases hlabel : cfg.state with
      | none =>
        have hstop : (TMCondition.not (.stateIs (some none))).eval s.config = false := by
          simp [hs, encode, hlabel]
        simp only [compile, execute_while_succ, hstop, Bool.false_eq_true, ite_false] at hr
        have heq : result = ⟨(), 0⟩ ∧ final = ⟨s, fuel⟩ := by simpa using hr.symm
        obtain ⟨rfl, rfl⟩ := heq
        have hcfg : cfg = ⟨none, s.config.BiTape⟩ := by
          have htape : s.config.BiTape = cfg.BiTape := by simp [hs, encode]
          cases cfg
          simp_all
        exact ⟨by simp [hcfg],
          by simp [hs, encode, hlabel]⟩
      | some label =>
        let entry := tm.tr label cfg.BiTape.head
        let next : tm.Cfg :=
          ⟨entry.2, (cfg.BiTape.write entry.1.symbol).optionMove entry.1.movement⟩
        have hstep : tm.step cfg = some next := by
          cases cfg
          simp_all [SingleTapeTM.step, next, entry]
        obtain ⟨a, middle, hbody, hmiddle, ha⟩ := body_correct tm cfg next s hs hstep
        have hgo : (TMCondition.not (.stateIs (some none))).eval s.config = true := by
          simp [hs, encode, hlabel]
        simp only [compile, execute_while_succ, hgo, ite_true] at hr
        change execute fuel (do body tm; compile tm) s = some (result, final) at hr
        simp only [execute, FuelExecMonad.execute_bind] at hr
        cases hb : execute fuel (body tm) s with
        | none => simp [hb] at hr
        | some pair =>
          obtain ⟨rb, mb⟩ := pair
          cases hl : execute mb.fuel (compile tm) mb.machine with
          | none => simp [hb, hl] at hr
          | some pair =>
            obtain ⟨rl, last⟩ := pair
            have heq : result = ⟨rl.ret, rb.tell + rl.tell⟩ ∧ final = last := by
              simpa [hb, hl] using hr.symm
            obtain ⟨rfl, rfl⟩ := heq
            have hsame := (completes_of_execute hb).unique hbody
            have hmb : mb.machine.config = encode tm next := by rw [hsame.2, hmiddle]
            have hbound := (FuelExecMonad.execute_trim_fuel fuel (body tm) s rb mb hb).1
            obtain ⟨htrace, hhalt⟩ := ih mb.fuel (by lia) next mb.machine hmb rl final hl
            refine ⟨?_, hhalt⟩
            have hcost : rb.tell.steps = 1 := by rw [hsame.1, ha]
            simpa [hcost, Nat.add_comm] using
              htrace.head cfg next _ rl.tell.steps hstep

/--
The compiled query program produces exactly the same output words as the source machine.
In particular, a nonterminating source computation cannot give a completed query computation.
Both models require the output word to be the only occupied part of the tape, under the head.
-/
theorem correct (input output : List Symbol) :
    tm.Outputs input output ↔ ∃ time, OutputsWithinTime (compile tm) input output time := by
  constructor
  · intro h
    obtain ⟨steps, hsteps⟩ := h.relatesInSteps
    obtain ⟨cost, final, ⟨fuel, hr⟩, hf, ht⟩ :=
      run_forward tm hsteps rfl (TMState.init (machine tm) input) rfl
    exact ⟨steps, fuel, ⟨(), cost⟩, ⟨final, 0⟩, hr, congrArg SingleTapeTM.Cfg.BiTape hf,
      by lia⟩
  · rintro ⟨time, fuel, result, final, hr, hf, _⟩
    have htrace := (run_backward tm fuel (tm.initCfg input)
      (TMState.init (machine tm) input) rfl result final hr).1
    rw [hf] at htrace
    exact htrace.reflTransGen

/--
A source computation using at most `time` transitions gives a query computation using at most
`time` move instructions. The reverse compiler has no multiplicative or additive time overhead
under the query cost measure. Its fixed state and symbol tests consume interpreter fuel.
-/
private theorem outputs_forward {input output : List Symbol} {time : ℕ}
    (h : tm.OutputsWithinTime input output time) :
    OutputsWithinTime (compile tm) input output time := by
  obtain ⟨steps, hle, hsteps⟩ := h
  obtain ⟨cost, final, ⟨fuel, hr⟩, hf, ht⟩ :=
    run_forward tm hsteps rfl (TMState.init (machine tm) input) rfl
  exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, hr, congrArg SingleTapeTM.Cfg.BiTape hf, by lia⟩

/--
A completed query computation comes from a source computation within the same time bound.
Each loop iteration represents exactly one source transition, including a stationary transition.
-/
private theorem outputs_backward {input output : List Symbol} {time : ℕ}
    (h : OutputsWithinTime (compile tm) input output time) :
    tm.OutputsWithinTime input output time := by
  obtain ⟨fuel, result, final, hr, hf, ht⟩ := h
  have htrace := (run_backward tm fuel (tm.initCfg input)
    (TMState.init (machine tm) input) rfl result final hr).1
  rw [hf] at htrace
  exact ⟨result.tell.steps, ht, htrace⟩

/--
The reverse compiler preserves time bounds exactly. The query program produces `output` within
`time` charged move instructions exactly when the source table produces it within `time`
transitions. Stationary source transitions are counted through the query instruction `Stop`.
-/
theorem time_bound {input output : List Symbol} {time : ℕ} :
    OutputsWithinTime (compile tm) input output time ↔
      tm.OutputsWithinTime input output time :=
  ⟨outputs_backward tm, outputs_forward tm⟩

end Algolean.Algorithms.TMQuery.Compiler.ToQuery

namespace Cslib.Turing.SingleTapeTM

open Algolean.Algorithms

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
This compiles a transition-table computer to one fixed query program for the same function.
The time bound is unchanged: every source transition costs exactly one query move instruction.
The finite state and symbol comparisons consume interpreter fuel rather than query move cost.
-/
noncomputable def TimeComputable.toQuery {f : List Symbol → List Symbol}
    (computer : TimeComputable f) : TMQuery.TimeComputable f := by
  classical
  exact {
    tm := TMQuery.Compiler.ToQuery.machine computer.tm
    program := TMQuery.Compiler.ToQuery.compile computer.tm
    timeBound := computer.timeBound
    computesWithin := by
      apply TMQuery.ComputesWithin.of_outputsWithinTime
        (program := TMQuery.Compiler.ToQuery.compile computer.tm) (f := f)
        (time := computer.timeBound)
      intro input
      exact (TMQuery.Compiler.ToQuery.time_bound computer.tm).mpr
        (computer.outputsFunInTime input) }

private theorem toQuery_timeBound_impl {f : List Symbol → List Symbol}
    (computer : TimeComputable f) (n : ℕ) :
    computer.toQuery.timeBound n = computer.timeBound n := rfl

/-- Compiling a transition-table computer to queries leaves its time bound unchanged. -/
@[simp] theorem TimeComputable.toQuery_timeBound {f : List Symbol → List Symbol}
    (computer : TimeComputable f) (n : ℕ) :
    computer.toQuery.timeBound n = computer.timeBound n := toQuery_timeBound_impl computer n

/--
This compiles a polynomial-time transition-table computer to a polynomial-time query computer.
It preserves both the time-bound function and its bounding polynomial.
-/
noncomputable def PolyTimeComputable.toQuery {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) : TMQuery.PolyTimeComputable f where
  toTimeComputable := computer.toTimeComputable.toQuery
  poly := computer.poly
  bounds := computer.bounds

private theorem toQuery_poly_impl {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) : computer.toQuery.poly = computer.poly := rfl

/-- Compiling a polynomial-time table computer to queries leaves its polynomial unchanged. -/
@[simp] theorem PolyTimeComputable.toQuery_poly {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) : computer.toQuery.poly = computer.poly :=
  toQuery_poly_impl computer

end Cslib.Turing.SingleTapeTM

namespace Algolean.Algorithms.TMQuery

open Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A word-valued function has a query program with a time bound exactly when it has a
transition-table Turing machine with a time bound. Both conversions preserve the computed function.
-/
theorem timeComputable_iff (f : List Symbol → List Symbol) :
    Nonempty (TimeComputable f) ↔ Nonempty (SingleTapeTM.TimeComputable f) :=
  ⟨fun ⟨computer⟩ => ⟨computer.toTransitionTable⟩,
    fun ⟨computer⟩ => ⟨computer.toQuery⟩⟩

/--
A word-valued function has a polynomial-time query program exactly when it has a polynomial-time
transition-table Turing machine. Query-to-table compilation gives an affine time bound with
constants fixed by the program, and table-to-query compilation preserves the source time bound.
-/
theorem polyTimeComputable_iff (f : List Symbol → List Symbol) :
    Nonempty (PolyTimeComputable f) ↔ Nonempty (SingleTapeTM.PolyTimeComputable f) :=
  ⟨fun ⟨computer⟩ => ⟨computer.toTransitionTable⟩,
    fun ⟨computer⟩ => ⟨computer.toQuery⟩⟩

end Algolean.Algorithms.TMQuery

