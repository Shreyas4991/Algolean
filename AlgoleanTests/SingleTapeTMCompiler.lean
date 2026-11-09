/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Checking compilation from query programs to transition tables

* The compiled table executes the query program even when the original table does different work.
* Nested branches and loops preserve their output and receive an affine transition bound.
* A loop with no head moves still cannot produce an output when it never finishes.
* Ordinary compiler imports provide the public theorems without importing implementation helpers.
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

/-- error: Unknown identifier `Compiler.Internal.programPositions` -/
#guard_msgs in
#check Compiler.Internal.programPositions

end

end AlgoleanTests.SingleTapeTMCompiler
