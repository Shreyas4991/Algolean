/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.KarpReduction
public import Algolean.Models.SingleTapeTM.Composition.Pairing
public import Algolean.Models.SingleTapeTM.Composition.TuringReduction
public import Algolean.Algorithms.SingleTapeTuringMachines.Framed
public import AlgoleanTests.SingleTapeTuringMachines
public import AlgoleanTests.PolytimeBasicClasses

/-! # Verified composition, Boolean encodings, and adaptive oracle examples -/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMComposition

open Algolean Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Cslib Cslib.Turing TMQuery
open scoped TMQuery Computer

/-- Reuse the single-state control alphabet for ordinary verified components. -/
abbrev machine := AlgoleanTests.SingleTapeTuringMachines.machine

example (first second : List Bool) :
    BooleanTapeEncoding.unpair (BooleanTapeEncoding.pair first second) = some (first, second) := by
  simp

example : BooleanTapeEncoding.unpair [true, true, false, true] = none := by
  simp [BooleanTapeEncoding.unpair, BooleanTapeEncoding.readLength]

/-- A concrete reduction from the empty-word singleton to the singleton `[true]`. -/
noncomputable def appendReduction :
    KarpReduction (fun input => input = []) (fun input => input = [true]) where
  transform input := input ++ [true]
  computer := appendBitPolyTimeComputable (tm := machine) true
  correct input := by
    constructor
    · rintro rfl; rfl
    · intro h
      simpa using h

example : P (fun input : List Bool => input = []) :=
  appendReduction.preservesP (PolytimeBasicClasses.singleton_inP [true])

example (input : List Bool) :
    input = [] ↔ (appendReduction.trans (KarpReduction.refl _)).transform input = [true] :=
  (appendReduction.trans (KarpReduction.refl _)).correct input

-- Different control alphabets are joined by the machine composition theorem.
example : Nonempty (TMQuery.PolyTimeComputable (fun input : List Bool => input ++ [true])) := by
  exact ⟨TMQuery.PolyTimeComputable.id.comp (appendBitPolyTimeComputable (tm := machine) true)⟩

/-- A fixed oracle program that keeps querying successive suffixes until an answer is yes. -/
def suffixSearch : Prog (TMQuery TuringReduction.identityControl) Unit :=
    do [TMQuery TuringReduction.identityControl]
  whileₜ (notₜ state =ₜ some TuringReduction.identityInterface.yes) do
    TuringReduction.identityInterface.ask
    ifₜ state =ₜ some TuringReduction.identityInterface.no then
      moveₜ .Right
    else
      pure ()

attribute [local simp] OracleInterface.execute_eq_runCode OracleInterface.step
  OracleInterface.ask OracleInterface.queryWord runCodeWith step branch whileLoop
  TMState.init SingleTapeTM.initCfg BiTape.mk₁ BiTape.nil BiTape.moveRight
  StackTape.head StackTape.tail StackTape.mapSome StackTape.nil StackTape.cons
  StackTape.length
  TuringReduction.identityInterface

-- Two calls and one head move: the second request depends on the first answer.
example :
    (TuringReduction.identityInterface.execute (fun input => input == [false]) 100 suffixSearch
      (TMState.init TuringReduction.identityControl [true, false])).map
      (fun (result, final) => (final.machine.config.state, final.machine.headPos,
        result.tell.steps, result.tell.cellsAllocated, final.machine.cellsAllocated.card)) =
      some (some 1, 1, 3, 0, 2) := by
  simp [suffixSearch]

-- Query extraction ends at a blank even if further cells hold nonblank data.
example : OracleInterface.queryWord
    ⟨some true, ∅, StackTape.cons none (StackTape.mapSome [false])⟩ = [true] := by
  simp [OracleInterface.queryWord]

example (language : Algorithms.Language Bool) : TuringReducible language language :=
  TuringReducible.refl language

/-- Observe completed components externally; the input is passed only to the initial tape. -/
def observe {ι : Type} {pre : ι → TMState machine → Prop}
    {post : ι → TMState machine → TMCost → TMState machine → Prop}
    (component : Component machine pre post) (input : List Bool) :
    Option (List Bool × ℤ × ℕ × ℕ × ℕ) :=
  (component.execute 1000 (TMState.init machine input)).map fun (result, final) =>
    (final.machine.config.BiTape.head.toList ++
      final.machine.config.BiTape.right.toList.filterMap id,
      final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
      final.machine.cellsAllocated.card)

example : observe (Copying.duplicateComputer (tm := machine)) [] =
    some ([false], -1, 5, 3, 4) := by decide
example : observe (Copying.duplicateComputer (tm := machine)) [true] =
    some ([true, false, true, true], -2, 20, 6, 7) := by decide
example : observe (Copying.duplicateComputer (tm := machine)) [true, false] =
    some ([true, true, false, true, false, true, false], -3, 43, 8, 10) := by decide

-- Actual fan-out includes physical copying and the framed right-word computation.
example : observe (duplicateAppendRightComputer (tm := machine) true) [] =
    some ([false, true], -1, 9, 3, 4) := by decide
example : observe (duplicateAppendRightComputer (tm := machine) true) [true, false] =
    some ([true, true, false, true, false, true, false, true], -3, 59, 8, 10) := by decide

example :
    let initial : TMState machine := {TMState.init machine [true, false] with
      headPos := 37
      cellsAllocated := Finset.Icc 35 41
      cellsVisited := Finset.Icc 35 41}
    ((Copying.duplicateComputer (tm := machine)).execute 1000 initial).map
      (fun (result, final) => (final.machine.headPos, result.tell.steps,
        result.tell.cellsAllocated, final.machine.cellsAllocated.card)) = some (34, 43, 3, 10) := by
  decide

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final,
      Completes (duplicateAppendRightComputer (tm := machine) true).program s cost final ∧
      final.config = {s.config with
        BiTape := BiTape.mk₁ (BooleanTapeEncoding.pair input (input ++ [true]))} ∧
      final.headPos = s.headPos - (input.length + 1 : ℕ) ∧
      cost.steps ≤ 4 * input.length ^ 2 + 17 * input.length + 9 :=
  (duplicateAppendRightComputer (tm := machine) true).correct input s hs

/-- A genuinely different control alphabet for the independent-composition regression. -/
abbrev boolMachine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This program writes only when started in its own initial control state. -/
def initialStateWriter : TMQuery.TimeComputable (fun input : List Bool => true :: input.tail) where
  tm := machine
  program := do [TMQuery machine]
    ifₜ state =ₜ some () then
      tape ←ₜ some true
    else
      pure ()
  timeBound _ := 0
  outputsFunInTime input := by
    refine ⟨2, ⟨(), 0⟩,
      ⟨{TMState.init machine input with config.BiTape := BiTape.mk₁ (true :: input.tail)}, 0⟩,
      ?_, rfl, le_rfl⟩
    cases input <;> rfl

/-- Composition must reset from a `Bool` label to the second machine's `PUnit` start label. -/
def independentComposition :
    TMQuery.TimeComputable (fun input : List Bool => true :: input.tail) :=
  ((identity_computes (tm := boolMachine)).timeComputable (timeBound := fun _ => 0)).comp
    initialStateWriter (by intro _ _ _; exact le_rfl)

/-- Execute a bundled uniform computation with its own finite control alphabet. -/
def observeTime {f : List Bool → List Bool} (computer : TMQuery.TimeComputable f)
    (input : List Bool) : Option (List Bool × ℕ × ℕ) :=
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  (execute 100 computer.program (TMState.init computer.tm input)).map fun (result, final) =>
    (final.machine.config.BiTape.head.toList ++
      final.machine.config.BiTape.right.toList.filterMap id,
      result.tell.steps, final.machine.cellsAllocated.card)

example : observeTime independentComposition [false, false] = some ([true, false], 0, 2) := by
  decide +kernel
example : observeTime independentComposition [] = some ([true], 0, 1) := by decide +kernel

end AlgoleanTests.SingleTapeTMComposition
