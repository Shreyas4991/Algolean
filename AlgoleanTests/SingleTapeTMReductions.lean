/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.KarpReduction
public import Algolean.Models.SingleTapeTM.Composition.TuringReduction

/-!
# Checking function composition and reductions

These examples check that sequential composition starts the second machine in its own initial
state. They also check a concrete [Karp reduction](##Algolean.Algorithms.KarpReduction) and an
oracle program whose second question depends on the first answer. The execution examples check
the output, time cost, tape use, and fuel exhaustion.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMReductions

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open scoped TMQuery

/-- This machine has one state and is used for the writing program. -/
abbrev writerControl : SingleTapeTM Bool where
  State := PUnit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This program writes a true bit under the head only when it starts in its own initial state. -/
noncomputable def writer :
    TMQuery.PolyTimeComputable (fun input : List Bool => true :: input.tail) where
  tm := writerControl
  program := do [TMQuery writerControl]
    ifₜ state =ₜ some () then
      tape ←ₜ some true
    else
      pure ()
  timeBound _ := 0
  outputsFunInTime input := by
    refine ⟨2, ⟨(), 0⟩,
      ⟨{TMState.init writerControl input with
        config.BiTape := BiTape.mk₁ (true :: input.tail)}, 0⟩, ?_, rfl, le_rfl⟩
    cases input <;> rfl
  poly := 0
  bounds _ := by simp

/-- This machine uses two states, distinct from the writing machine's state type. -/
abbrev boolControl : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This program leaves its input unchanged and uses a machine with two states. -/
noncomputable def boolIdentity : TMQuery.PolyTimeComputable (id : List Bool → List Bool) where
  tm := boolControl
  program := pure ()
  timeBound _ := 0
  outputsFunInTime input := ⟨0, ⟨(), 0⟩, ⟨TMState.init boolControl input, 0⟩,
    rfl, rfl, le_rfl⟩
  poly := 0
  bounds _ := by simp

/--
This function runs the stored program and reports its output, time cost, and recorded tape size.
-/
def observe {f : List Bool → List Bool} (machine : TMQuery.TimeComputable f)
    (input : List Bool) : Option (List Bool × ℕ × ℕ) :=
  let := machine.symbolDecidableEq
  let := machine.stateDecidableEq
  (execute 10 machine.program (TMState.init machine.tm input)).map fun (result, final) =>
    (final.machine.config.BiTape.head.toList ++
      final.machine.config.BiTape.right.toList.filterMap id,
      result.tell.steps, final.machine.cellsAllocated.card)

-- The second program must start in its own initial state for the write to happen.
example : observe (boolIdentity.comp writer).toTimeComputable [false, false] =
    some ([true, false], 0, 2) := by decide +kernel

-- A stationary write can produce one symbol even on an empty input.
example : observe (boolIdentity.comp writer).toTimeComputable [] = some ([true], 0, 1) := by
  decide +kernel

/--
This reduction converts the question "Does the input have length at most one?" into "Is the
converted input exactly the word containing one true bit?"
-/
noncomputable def shortWordReduction : KarpReduction {input : List Bool | input.tail = []}
    {[true]} where
  transform input := true :: input.tail
  computer := writer
  correct input := by simp

example : {input : List Bool | input.tail = []} ∈ P :=
  shortWordReduction.preservesP
    ⟨id, [true], ⟨TMQuery.PolyTimeComputable.id⟩, fun _ => Iff.rfl⟩

example (input : List Bool) :
    input.tail = [] ↔
      (shortWordReduction.trans (KarpReduction.refl _)).transform input = [true] :=
  (shortWordReduction.trans (KarpReduction.refl _)).correct input

example : KarpReducible {input : List Bool | input.tail = []} {[true]} :=
  (show KarpReducible _ _ from ⟨shortWordReduction⟩).trans (KarpReducible.refl _)

/-- This program executes one `.Stop` instruction, which costs one head move without moving. -/
def stop : Prog (TMQuery writerControl) Unit := do [TMQuery writerControl]
  moveₜ .Stop

-- A completed program must still meet its time bound, even when its head stays in place.
example (input : List Bool) : ¬OutputsWithinTime stop input input 0 := by
  rintro ⟨fuel, result, final, h, _, htime⟩
  cases fuel <;> simp_all [stop, step]
  grind

/-- This program repeatedly tests a condition that never changes and never moves the head. -/
def forever : Prog (TMQuery writerControl) Unit := do [TMQuery writerControl]
  whileₜ (state =ₜ some ()) do
    pure ()

/-- The loop cannot finish with any finite amount of fuel, even though it makes no head moves. -/
theorem forever_fails (fuel : ℕ) (input : List Bool) :
    execute fuel forever (TMState.init writerControl input) = none := by
  induction fuel with
  | zero => simp [forever]
  | succ fuel ih =>
    simpa [forever, execute_while_succ, TMState.init, SingleTapeTM.initCfg] using ih

example (input output : List Bool) (time : ℕ) :
    ¬OutputsWithinTime forever input output time := by
  rintro ⟨fuel, result, final, h, _⟩
  simp [forever_fails] at h

/-- This program asks about successive suffixes of the input until the solver answers yes. -/
def suffixSearch : Prog (TMQuery TuringReduction.identityControl) Unit :=
    do [TMQuery TuringReduction.identityControl]
  whileₜ (notₜ state =ₜ some TuringReduction.identityInterface.yes) do
    TuringReduction.identityInterface.ask
    ifₜ state =ₜ some TuringReduction.identityInterface.no then
      moveₜ .Right
    else
      pure ()

-- Two requests and one head move cost three steps. Both requests run inside structured control.
example :
    (TuringReduction.identityInterface.execute (fun input => input == [false]) 8 suffixSearch
      (TMState.init TuringReduction.identityControl [true, false])).map
      (fun (result, final) => (final.machine.config.state, final.machine.headPos,
        result.tell.steps, result.tell.cellsAllocated, final.machine.cellsAllocated.card,
        final.fuel)) = some (some 1, 1, 3, 0, 2, 0) := by
  decide +kernel

-- Losing the fuel needed for the last loop test fails the whole execution.
example : TuringReduction.identityInterface.execute (fun input => input == [false]) 7
    suffixSearch (TMState.init TuringReduction.identityControl [true, false]) = none := by
  rfl

-- Query extraction stops at a blank even when later cells contain data.
example : OracleInterface.queryWord
    ⟨some true, ∅, StackTape.cons none (StackTape.mapSome [false])⟩ = [true] := by
  simp [OracleInterface.queryWord, StackTape.cons, StackTape.mapSome]

example (language : Algorithms.Language Bool) : TuringReducible language language :=
  TuringReducible.refl language

end AlgoleanTests.SingleTapeTMReductions
