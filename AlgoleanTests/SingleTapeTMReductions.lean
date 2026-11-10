/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BasicTMs
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
    let reduction := shortWordReduction.trans
      (KarpReduction.refl ({[true]} : Algorithms.Language Bool))
    input.tail = [] ↔ reduction.transform input = [true] := by
  simp [KarpReduction.trans, KarpReduction.refl, shortWordReduction]

example : KarpReducible {input : List Bool | input.tail = []} {[true]} :=
  (show KarpReducible {input : List Bool | input.tail = []} {[true]} from
    ⟨shortWordReduction⟩).trans (KarpReducible.refl ({[true]} : Algorithms.Language Bool))

/-- This represents the only source symbol by symbol two on a three-symbol shared tape. -/
def unitSymbol : Unit ↪ Fin 3 := ⟨fun _ => 2, fun _ _ _ => Subsingleton.elim _ _⟩

/--
This reduction relates a language over one symbol to a language over three symbols. Their
representations on the shared tape coincide, so its fixed program leaves the tape unchanged.
-/
noncomputable def differentAlphabets :
    KarpReduction {([()] : List Unit)} {([2] : List (Fin 3))}
      unitSymbol (Function.Embedding.refl (Fin 3)) where
  transform := id
  computer := TMQuery.PolyTimeComputable.id
  correct input := by
    simp [Problems.symbolLanguage, unitSymbol]
    rfl

/-- The source word is accepted exactly when its represented target word is accepted. -/
theorem differentAlphabets_correct (input : List Unit) :
    input = [()] ↔ differentAlphabets.transform (input.map unitSymbol) = [2] := by
  simpa using differentAlphabets.correct_input input

/-- Composition keeps the common representation of the middle problem on the same tape. -/
theorem differentAlphabets_comp :
    KarpReducible {([()] : List Unit)} {([2] : List (Fin 3))}
      unitSymbol (Function.Embedding.refl (Fin 3)) := by
  exact ⟨differentAlphabets.trans (KarpReduction.refl {([2] : List (Fin 3))}
    (Function.Embedding.refl (Fin 3)))⟩

/-- A tape word using symbol zero is outside the source representation and remains a no answer. -/
theorem differentAlphabets_invalid :
    differentAlphabets.transform [0] ∉ Problems.symbolLanguage
      (Function.Embedding.refl (Fin 3)) {([2] : List (Fin 3))} := by
  simp [differentAlphabets]

/-- Complementing the represented problems reverses their answers on every shared tape word. -/
theorem differentAlphabets_complement (input : List (Fin 3)) :
    input ∉ Problems.symbolLanguage unitSymbol {([()] : List Unit)} ↔
      differentAlphabets.complementOnTape.transform input ≠ [2] := by
  simpa using differentAlphabets.complementOnTape.correct input

/-- A polynomial-time target solver gives a solver for the source represented on the shared tape. -/
theorem differentAlphabets_inP :
    Problems.symbolLanguage unitSymbol {([()] : List Unit)} ∈ P := by
  apply differentAlphabets.preservesP_onTape
  exact ⟨id, [2], ⟨TMQuery.PolyTimeComputable.id⟩, by simp⟩

/--
Composing the zero-move word conversion with appending false gives a linear time bound.
The bound includes the possible extra output symbol produced by the first program.
-/
theorem reduction_then_append_bound (input : List Bool) :
    let combined := shortWordReduction.computer.comp
      (SingleTapeTuringMachines.appendBitPolyTimeComputable (tm := writerControl) false)
    let := combined.symbolDecidableEq
    let := combined.stateDecidableEq
    OutputsWithinTime combined.program input ((true :: input.tail) ++ [false])
      (2 * input.length + 4) := by
  have hpoly : (SingleTapeTuringMachines.appendBitPolyTimeComputable
      (tm := writerControl) false).poly = 2 * Polynomial.X + 2 := rfl
  convert shortWordReduction.composition_time_bound
    (SingleTapeTuringMachines.appendBitPolyTimeComputable (tm := writerControl) false) input using 1
  simp [shortWordReduction, writer, hpoly, Nat.mul_add]
  lia

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
def suffixSearch (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] :
    Prog (TMQuery (TuringReduction.identityControl Symbol)) Unit :=
    do [TMQuery (TuringReduction.identityControl Symbol)]
  whileₜ (notₜ state =ₜ some (TuringReduction.identityInterface Symbol).yes) do
    (TuringReduction.identityInterface Symbol).ask
    ifₜ state =ₜ some (TuringReduction.identityInterface Symbol).no then
      moveₜ .Right
    else
      pure ()

-- Two requests and one head move cost three steps. Both requests run inside structured control.
example :
    ((TuringReduction.identityInterface Bool).execute (fun input => input == [false]) 8
      (suffixSearch Bool)
      (TMState.init (TuringReduction.identityControl Bool) [true, false])).map
      (fun (result, final) => (final.machine.config.state, final.machine.headPos,
        result.tell.steps, result.tell.cellsAllocated, final.machine.cellsAllocated.card,
        final.fuel)) = some (some 1, 1, 3, 0, 2, 0) := by
  decide +kernel

-- Losing the fuel needed for the last loop test fails the whole execution.
example : (TuringReduction.identityInterface Bool).execute (fun input => input == [false]) 7
    (suffixSearch Bool) (TMState.init (TuringReduction.identityControl Bool) [true, false]) =
    none := by
  rfl

-- Query extraction stops at a blank even when later cells contain data.
example : OracleInterface.queryWord
    ⟨some true, ∅, StackTape.cons none (StackTape.mapSome [false])⟩ = [true] := by
  simp [OracleInterface.queryWord, StackTape.cons, StackTape.mapSome]

example {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (language : Algorithms.Language Symbol) : TuringReducible language language :=
  TuringReducible.refl language

-- The same program asks about words over three symbols without converting them to bits.
example :
    ((TuringReduction.identityInterface (Fin 3)).execute (fun input => input == [2]) 8
      (suffixSearch (Fin 3))
      (TMState.init (TuringReduction.identityControl (Fin 3)) [1, 2])).map
      (fun (result, final) => (final.machine.config.state, final.machine.headPos,
        result.tell.steps, result.tell.cellsAllocated, final.machine.cellsAllocated.card,
        final.fuel)) = some (some 1, 1, 3, 0, 2, 0) := by
  decide +kernel

-- Even over one symbol, the control states distinguish yes from no. The last query is empty.
example :
    ((TuringReduction.identityInterface Unit).execute (fun input => input.isEmpty) 12
      (suffixSearch Unit) (TMState.init (TuringReduction.identityControl Unit) [(), ()])).map
      (fun (result, final) => (final.machine.config.state, final.machine.headPos,
        result.tell.steps, result.tell.cellsAllocated, final.machine.cellsAllocated.card,
        final.fuel)) = some (some 1, 2, 5, 1, 3, 0) := by
  decide +kernel

-- A blank ends a query over any alphabet, including one with more than two symbols.
example : OracleInterface.queryWord
    ⟨some (2 : Fin 3), ∅, StackTape.cons none (StackTape.mapSome [0, 1])⟩ = [2] := by
  simp [OracleInterface.queryWord, StackTape.cons, StackTape.mapSome]

end AlgoleanTests.SingleTapeTMReductions
