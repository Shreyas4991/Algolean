/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Checking both Turing machine compilers

* The compiled table executes the query program even when the original table does different work.
* Nested branches and loops preserve their output and receive an affine transition bound.
* A loop with no head moves still cannot produce an output when it never finishes.
* Ordinary compiler imports provide the public theorems without importing implementation helpers.
* The reverse compiler handles stationary transitions, blank cells, and movement in both directions.
* A stationary infinite source computation cannot give a completed query computation.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMCompiler

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open scoped TMQuery

noncomputable section

/-- This finite view records the head symbol and both stored sides of a tape. -/
def snapshot {Symbol : Type} (viewed : BiTape Symbol) :
    Option Symbol × List (Option Symbol) × List (Option Symbol) :=
  (viewed.head, viewed.left.toList, viewed.right.toList)

/-- Equal finite views describe equal tapes, including all symbols on both sides of the head. -/
theorem snapshot_injective {Symbol : Type} : Function.Injective (@snapshot Symbol) := by
  rintro ⟨head₁, ⟨left₁, hl₁⟩, ⟨right₁, hr₁⟩⟩ ⟨head₂, ⟨left₂, hl₂⟩, ⟨right₂, hr₂⟩⟩ h
  simp_all [snapshot]

/-- This source machine supplies two logical labels; its own table writes false and halts. -/
abbrev control : SingleTapeTM Bool where
  State := Fin 2
  q₀ := 0
  tr _ _ := (⟨some false, none⟩, none)

/-- This query program writes true without moving, regardless of the source transition table. -/
def writeTrue : Prog (TMQuery control) Unit := do [TMQuery control]
  tape ←ₜ some true

/-- Writing true on a one-bit input finishes with zero charged head moves. -/
theorem writeTrue_outputs : OutputsWithinTime writeTrue [false] [true] 0 := by
  refine ⟨1, ⟨(), 0⟩, ⟨{TMState.init control [false] with
    config.BiTape := BiTape.mk₁ [true]}, 0⟩, rfl, rfl, le_rfl⟩

-- The original table writes false, while compilation follows the query program and writes true.
example : control.step (control.initCfg [false]) = some (control.haltCfg [false]) := rfl

example : (Compiler.compile writeTrue).machine.OutputsWithinTime [false] [true]
    (((Compiler.compile writeTrue).states + 2) * 3) := by
  simpa [Compiler.transitionFactor_eq] using Compiler.time_bound writeTrue writeTrue_outputs

-- Even a completed program needs a transition to halt its ordinary machine.
example (input : List Bool) :
    ¬(Compiler.compile (pure () : Prog (TMQuery control) Unit)).machine.OutputsWithinTime
      input input 0 := by
  intro h
  have heq := Relation.RelatesWithinSteps.zero h
  have hstate := congrArg SingleTapeTM.Cfg.state heq
  simp [SingleTapeTM.initCfg, SingleTapeTM.haltCfg] at hstate

/--
If the logical label is zero, this program flips leading true bits, moves left twice,
and sets the label to one. Otherwise it leaves the tape unchanged.
-/
def nested : Prog (TMQuery control) Unit := do [TMQuery control]
  ifₜ state =ₜ some 0 then
    whileₜ (tape =ₜ some true) do
      tape ←ₜ some false
      moveₜ .Right
    moveₜ .Left
    moveₜ .Left
    state ←ₜ 1
  else
    pure ()

/-- The nested program changes two true bits to false and returns after four head moves. -/
theorem nested_outputs : OutputsWithinTime nested [true, true, false] [false, false, false] 4 := by
  have hvalue : (execute 11 nested (TMState.init control [true, true, false])).map
      (fun (result, final) => (snapshot final.machine.config.BiTape, result.tell.steps)) =
        some (snapshot (BiTape.mk₁ [false, false, false]), 4) := by decide +kernel
  obtain ⟨⟨result, final⟩, hrun, heq⟩ := Option.map_eq_some_iff.mp hvalue
  have ⟨htape, htime⟩ := Prod.mk.inj heq
  exact ⟨11, result, final, hrun, snapshot_injective htape, htime.le⟩

-- Seven source instructions, two labels, and two symbols give constants of at most 75.
example : (Compiler.compile nested).machine.OutputsWithinTime [true, true, false]
    [false, false, false] 375 := by
  refine Relation.RelatesWithinSteps.mono ?_ (Compiler.time_bound nested nested_outputs)
  have hsize : Compiler.instructionCount nested = 7 := by decide +kernel
  have hfactor : Compiler.transitionFactor nested ≤ 75 := by
    simpa [hsize] using Compiler.transitionFactor_le nested
  lia

/-- This program repeatedly tests its initial label and performs no writes or head moves. -/
def forever : Prog (TMQuery control) Unit := do [TMQuery control]
  whileₜ (state =ₜ some 0) do
    pure ()

/-- No finite interpreter budget completes the loop because its condition always remains true. -/
theorem forever_fails (fuel : ℕ) (input : List Bool) :
    execute fuel forever (TMState.init control input) = none := by
  induction fuel with
  | zero => simp [forever]
  | succ fuel ih =>
    simpa [forever, execute_while_succ, TMState.init, SingleTapeTM.initCfg] using ih

-- Compiling a zero-move infinite loop cannot introduce a halting output.
example (input output : List Bool) : ¬(Compiler.compile forever).machine.Outputs input output := by
  rw [Compiler.correct forever input output]
  rintro ⟨time, fuel, result, final, hrun, _⟩
  simp [forever_fails] at hrun

-- Existing polynomial-time records can be converted directly to transition-table records.
example : SingleTapeTM.PolyTimeComputable (id : List Bool → List Bool) :=
  TMQuery.PolyTimeComputable.id.toTransitionTable

/--
The reverse compiler follows the table, which writes false and halts without moving. The stationary
transition still costs one query move instruction. On an empty input it creates a one-bit output.
-/
theorem reverse_stationary (input : List Bool) :
    OutputsWithinTime (Compiler.ToQuery.compile control) input (false :: input.tail) 1 := by
  apply (Compiler.ToQuery.time_bound control).mpr
  apply Relation.RelatesWithinSteps.single
  cases input <;> rfl

/-- A stationary source transition cannot finish within a zero-transition bound. -/
theorem reverse_stationary_not_zero (input : List Bool) :
    ¬OutputsWithinTime (Compiler.ToQuery.compile control) input (false :: input.tail) 0 := by
  rw [Compiler.ToQuery.time_bound control]
  intro h
  have hstate := congrArg SingleTapeTM.Cfg.state (Relation.RelatesWithinSteps.zero h)
  simp [SingleTapeTM.initCfg, SingleTapeTM.haltCfg] at hstate

/-- This table moves right, moves left, then writes false and halts on its original cell. -/
abbrev roundTrip : SingleTapeTM Bool where
  State := Fin 3
  q₀ := 0
  tr label symbol :=
    if label = 0 then (⟨symbol, some .right⟩, some 1)
    else if label = 1 then (⟨symbol, some .left⟩, some 2)
    else (⟨some false, none⟩, none)

/-- The reverse compiler preserves both directions of movement and the final stationary write. -/
theorem reverse_roundTrip :
    OutputsWithinTime (Compiler.ToQuery.compile roundTrip) [true, false] [false, false] 3 := by
  apply (Compiler.ToQuery.time_bound roundTrip).mpr
  let middle := (roundTrip.step (roundTrip.initCfg [true, false])).getD default
  let ready := (roundTrip.step middle).getD default
  exact ⟨3, le_rfl,
    ((Relation.RelatesInSteps.single (r := roundTrip.TransitionRelation)
      (b := middle) rfl).tail _ _ ready _ rfl).tail _ _ _ _ rfl⟩

/-- This table keeps its state and current tape symbol forever, without moving the head. -/
abbrev stationaryForever : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, some ())

/-- Every reachable source configuration still has an active state, so the table never halts. -/
private theorem stationaryForever_active (input : List Bool) (cfg : stationaryForever.Cfg)
    (h : Relation.ReflTransGen stationaryForever.TransitionRelation
      (stationaryForever.initCfg input) cfg) : cfg.state = some () := by
  induction h with
  | refl => rfl
  | @tail cfg final h hstep ih =>
    cases cfg with
    | mk label cells =>
      cases label with
      | none => simp_all
      | some label =>
        have hf : final = ⟨some (), (cells.write cells.head).optionMove none⟩ := by
          simpa [SingleTapeTM.TransitionRelation, stationaryForever] using hstep.symm
        rw [hf]

/-- The reverse compiler cannot make a stationary infinite source computation finish. -/
theorem reverse_forever (input output : List Bool) :
    ¬∃ time, OutputsWithinTime (Compiler.ToQuery.compile stationaryForever) input output time := by
  rw [← Compiler.ToQuery.correct]
  intro h
  have hactive := stationaryForever_active input _ h
  simp [SingleTapeTM.haltCfg] at hactive

/-- Compiling a query program to a table and back preserves its output and affine time bound. -/
theorem compile_both_ways :
    letI : DecidableEq (Compiler.compile writeTrue).machine.State := Classical.decEq _
    OutputsWithinTime (Compiler.ToQuery.compile (Compiler.compile writeTrue).machine)
      [false] [true] (Compiler.transitionFactor writeTrue) := by
  classical
  apply (Compiler.ToQuery.time_bound _).mpr
  simpa using Compiler.time_bound writeTrue writeTrue_outputs

-- A two-state source machine gives exactly three query control labels.
example : Fintype.card (Compiler.ToQuery.machine control).State = 3 := by
  simp

-- Both record conversions can be applied successively.
example : TMQuery.PolyTimeComputable (id : List Bool → List Bool) :=
  SingleTapeTM.PolyTimeComputable.id.toQuery.toTransitionTable.toQuery

-- Polynomial-time computability is independent of the choice of either model.
example (f : List Bool → List Bool) :
    Nonempty (TMQuery.PolyTimeComputable f) ↔ Nonempty (SingleTapeTM.PolyTimeComputable f) :=
  TMQuery.polyTimeComputable_iff f

/-- error: Unknown identifier `Compiler.Internal.programPositions` -/
#guard_msgs in
#check Compiler.Internal.programPositions

end

end AlgoleanTests.SingleTapeTMCompiler
