/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.TransitionWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.ControlWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Formula

/-!
# Writing the transition clauses for a fixed verifier

* `writeTransitions` writes clauses stating what the verifier writes under its head, where its
  head moves and which state it enters, and which other tape cells stay unchanged.
* `writeTransitions_spec` states the exact appended formula and proves that the input, bounds,
  and head position are restored.
* `transitionTimeBound` bounds the number of head moves by a polynomial.

The verifier's finite transition table is fixed when constructing this template. The program
has a fixed list of cases for the verifier's states and tape symbols. It reads time, position,
and state selections from runs of symbols on the tape.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

attribute [local instance 100] Encodable.decidableEqOfEncodable

namespace Algolean.Algorithms.NPToSAT.Writing

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Computability Problems Problems.SAT
open NPToSAT.Computation NPToSAT.Computation.HeadChoices NPToSAT.Computation.LiteralWriting
open NPToSAT.Computation.TransitionWriting NPToSAT.Computation.ControlWriting
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def checkEarlier (yes no : tm.State) (expected : List Γ) (distance : Nat) :
    Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (onCounter tm (checkWord tm yes no expected) distance)

omit [Encodable Γ] in
private theorem checkEarlier_spec (yes no : tm.State) (hne : yes ≠ no)
    (expected : List Γ) (left tail : StackTape Γ) (word : List Γ)
    (between : List (List Γ)) (crossed : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let view := BiTape.segment
      (StackTape.prepend crossed.reverse (earlierLeft left word between)) [] tail
    ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      checkEarlier (tm := tm) yes no expected between.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if expected = word then yes else no), view⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 4 * expected.length +
          2 * crossed.length + 2 * word.length + 2 * (between.map List.length).sum +
            4 * between.length + 6 ⦄ := by
  dsimp only
  let result := some (if expected = word then yes else no)
  let bound := 4 * expected.length + 2 * word.length +
    2 * (between.map List.length).sum + 4 * between.length + 4
  have ha (place : ℤ) (steps : Nat) := onEarlierWord_spec (tm := tm)
    (checkWord tm yes no expected) left left word between crossed tail tail label result
    (4 * expected.length)
    (fun place steps => checkWord_spec (tm := tm) yes no hne expected word
      (StackTape.cons none left) (counterRight between crossed tail) label place steps) place steps
  vcgen [checkEarlier, onPrefixAtMark_spec
    (onCounter tm (checkWord tm yes no expected) between.length)
    (earlierLeft left word between) (earlierLeft left word between) (by simp)
    crossed tail tail label result bound
    (by simpa [result, bound, Nat.add_assoc] using ha) origin elapsed]
  all_goals simp_all [result, bound]
  all_goals lia

private inductive Part where
  | firstState | secondState | secondPosition

private def Part.value (part : Part) (choice : ActiveChoices) : Nat :=
  match part with
  | .firstState => choice.firstState.1
  | .secondState => choice.secondState.1
  | .secondPosition => choice.secondPosition.1

private def checkPart (yes no : tm.State) (tick : Γ) (part : Part) (value : Nat) :
    Prog (TMQuery tm) Unit :=
  match part with
  | .firstState => checkEarlier yes no (List.replicate value tick) 3
  | .secondState => onPrefixAtMark tm (checkWord tm yes no (List.replicate value tick))
  | .secondPosition => checkEarlier yes no (List.replicate value tick) 1

private def checkMoves (value size : Nat) : Nat := 4 * value + 4 * size + 64

omit [Encodable Γ] in
private theorem checkPart_spec (yes no : tm.State) (hne : yes ≠ no) (tick : Γ)
    (part : Part) (value : Nat) (choice : ActiveChoices) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      checkPart (tm := tm) yes no tick part value
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if part.value choice = value then yes else no)) origin final ∧
        cost.steps ≤ elapsed + checkMoves value choice.size ⦄ := by
  let tail := StackTape.separateWords (choice.rightWords tick input) (StackTape.mapSome output)
  let crossed := List.replicate choice.secondState.1 tick
  cases part with
  | secondState =>
    have hs := onPrefixAtMark_spec (tm := tm)
      (checkWord tm yes no (List.replicate value tick))
      (counterLeft [] (choice.leftWords tick)) (counterLeft [] (choice.leftWords tick)) (by simp)
      crossed tail tail label (some (if List.replicate value tick = crossed then yes else no))
      (4 * value) (by
        intro place steps
        simpa only [List.length_replicate] using checkWord_spec (tm := tm) yes no hne
          (List.replicate value tick) crossed (counterLeft [] (choice.leftWords tick))
          tail label place steps) origin elapsed
    vcgen [checkPart, hs]
    all_goals simp_all [Part.value, AtPair, pairTape, markedUnaryTape, crossed, tail,
      checkMoves, ActiveChoices.size, eq_comm]
    all_goals lia
  | firstState =>
    have hs := checkEarlier_spec (tm := tm) yes no hne (List.replicate value tick)
      (counterLeft [] [List.replicate choice.firstPosition.2 tick,
        List.replicate choice.firstPosition.1 tick, List.replicate choice.time.2 tick,
        List.replicate choice.time.1 tick]).tail tail
      (List.replicate choice.firstState.1 tick)
      [List.replicate choice.secondPosition.2 tick, List.replicate choice.secondPosition.1 tick,
        List.replicate choice.firstState.2 tick] crossed label origin elapsed
    simp only [List.length_cons, List.length_nil] at hs
    vcgen [checkPart, hs]
    all_goals simp_all [Part.value, AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
      crossed, tail, checkMoves, ActiveChoices.size, eq_comm]
    all_goals lia
  | secondPosition =>
    have hs := checkEarlier_spec (tm := tm) yes no hne (List.replicate value tick)
      (counterLeft [] [List.replicate choice.firstState.2 tick,
        List.replicate choice.firstState.1 tick, List.replicate choice.firstPosition.2 tick,
        List.replicate choice.firstPosition.1 tick, List.replicate choice.time.2 tick,
        List.replicate choice.time.1 tick]).tail tail
      (List.replicate choice.secondPosition.1 tick)
      [List.replicate choice.secondPosition.2 tick] crossed label origin elapsed
    simp only [List.length_cons, List.length_nil] at hs
    vcgen [checkPart, hs]
    all_goals simp_all [Part.value, AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
      crossed, tail, checkMoves, ActiveChoices.size, eq_comm]
    all_goals lia

private def whenPart (yes no : tm.State) (tick : Γ) (part : Part) (value : Nat)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  checkPart yes no tick part value
  ifₜ state =ₜ some yes then
    action
  else
    pure ()
  state ←ₜ yes

omit [Encodable Γ] in
private theorem whenPart_spec (yes no : tm.State) (hne : yes ≠ no) (tick : Γ)
    (part : Part) (value : Nat) (action : Prog (TMQuery tm) Unit) (choice : ActiveChoices)
    (input output written : List Γ) (bound : Nat)
    (haction : part.value choice = value → ∀ (position : ℤ) (steps : Nat),
      ⦃ fun cost current => AtPair tick choice input output (some yes) position current ∧
          cost.steps ≤ steps ⦄
        action
      ⦃ fun _ cost final => AtPair tick choice input (output ++ written) (some yes) position final ∧
          cost.steps ≤ steps + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      whenPart yes no tick part value action
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ if part.value choice = value then written else []) (some yes) origin final ∧
        cost.steps ≤ elapsed + checkMoves value choice.size + bound ⦄ := by
  by_cases hc : part.value choice = value
  · vcgen [whenPart, checkPart_spec (tm := tm) yes no hne tick part value choice input output
      (some yes) origin elapsed, haction hc origin (elapsed + checkMoves value choice.size)]
    all_goals simp_all [AtPair]
  · vcgen [whenPart, checkPart_spec (tm := tm) yes no hne tick part value choice input output
      (some yes) origin elapsed]
    all_goals simp_all [AtPair, Ne.symm hne]
    all_goals lia

private def stateWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (control : Option (Fin (verifier.states + 1))) (symbol : Option (TapeSymbol Γ)) :
      List Γ :=
  if choice.firstState.1 = Encodable.encode control then
    tapeUpdateWord code choice false symbol (instruction verifier control symbol).1 else []

private def writeState (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State)
    (control : Option (Fin (verifier.states + 1))) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit :=
  whenPart yes no tick .firstState (Encodable.encode control)
    (writeTapeUpdateClause tm zero one tick code false symbol (instruction verifier control
      symbol).1)

private theorem writeState_spec (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no) (choice : ActiveChoices)
    (control : Option (Fin (verifier.states + 1))) (symbol : Option (TapeSymbol Γ))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ stateWord verifier code choice control symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeState (tm := tm) verifier zero one tick code yes no control symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ stateWord verifier code choice control symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + checkMoves (Encodable.encode control) choice.size +
          tapeUpdateTime width size ⦄ := by
  have hs := whenPart_spec (tm := tm) yes no hstates tick .firstState (Encodable.encode control)
    (writeTapeUpdateClause tm zero one tick code false symbol (instruction verifier control
      symbol).1)
    choice input output (tapeUpdateWord code choice false symbol
      (instruction verifier control symbol).1) (tapeUpdateTime width size) (by
        intro hc position steps
        dsimp only [Part.value] at hc
        exact writeTapeUpdateClause_spec (tm := tm) zero one hne tick code width hwidth choice
          false symbol (instruction verifier control symbol).1 input output size
          (by simpa [stateWord, hc] using hsize) (some yes) position steps)
    origin elapsed
  vcgen [writeState, hs]
  all_goals grind [AtPair, Part.value, stateWord]

private def statesWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbol : Option (TapeSymbol Γ)) : List Γ :=
  states.flatMap fun control => stateWord verifier code choice control symbol

private def writeStates (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State)
    (symbol : Option (TapeSymbol Γ)) :
    List (Option (Fin (verifier.states + 1))) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | control :: rest => do [TMQuery tm]
    writeState verifier zero one tick code yes no control symbol
    writeStates verifier zero one tick code yes no symbol rest

private def statesMoves (width size : Nat) {count : Nat}
    (states : List (Option (Fin count))) : Nat :=
  (states.map fun control => checkMoves (Encodable.encode control) size + tapeUpdateTime
    width size).sum

private theorem writeStates_spec (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbol : Option (TapeSymbol Γ)) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ statesWord verifier code choice states symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeStates (tm := tm) verifier zero one tick code yes no symbol states
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ statesWord verifier code choice states symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + statesMoves width size states ⦄ := by
  induction states generalizing output elapsed with
  | nil =>
    vcgen [writeStates]
    all_goals simp_all [statesWord, statesMoves]
  | cons control rest ih =>
    have hcap : choice.size ≤ size := by lia
    have hfirst : choice.size + input.length +
        (output ++ stateWord verifier code choice control symbol).length + 32 ≤ size := by
      simp only [statesWord, List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    have hrest : choice.size + input.length +
        (output ++ stateWord verifier code choice control symbol ++
          statesWord verifier code choice rest symbol).length + 32 ≤ size := by
      simpa only [statesWord, List.flatMap_cons, List.append_assoc] using hsize
    vcgen [writeStates,
      writeState_spec (tm := tm) verifier zero one hne tick code width hwidth yes no hstates
        choice control symbol input output size hfirst origin elapsed,
      ih (output ++ stateWord verifier code choice control symbol) hrest
        (elapsed + checkMoves (Encodable.encode control) size + tapeUpdateTime width size)]
    all_goals simp_all [statesWord, statesMoves, checkMoves, List.append_assoc]
    all_goals lia

private def symbolsWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) : List Γ :=
  symbols.flatMap fun symbol => statesWord verifier code choice states symbol

private def writeSymbols (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State)
    (states : List (Option (Fin (verifier.states + 1)))) :
    List (Option (TapeSymbol Γ)) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: rest => do [TMQuery tm]
    writeStates verifier zero one tick code yes no symbol states
    writeSymbols verifier zero one tick code yes no states rest

private theorem writeSymbols_spec (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ symbolsWord verifier code choice states symbols).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeSymbols (tm := tm) verifier zero one tick code yes no states symbols
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ symbolsWord verifier code choice states symbols) (some yes) origin final ∧
        cost.steps ≤ elapsed + symbols.length * statesMoves width size states ⦄ := by
  induction symbols generalizing output elapsed with
  | nil =>
    vcgen [writeSymbols]
    all_goals simp_all [symbolsWord]
  | cons symbol rest ih =>
    have hfirst : choice.size + input.length +
        (output ++ statesWord verifier code choice states symbol).length + 32 ≤ size := by
      simp only [symbolsWord, List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    have hrest : choice.size + input.length +
        (output ++ statesWord verifier code choice states symbol ++
          symbolsWord verifier code choice states rest).length + 32 ≤ size := by
      simpa only [symbolsWord, List.flatMap_cons, List.append_assoc] using hsize
    vcgen [writeSymbols,
      writeStates_spec (tm := tm) verifier zero one hne tick code width hwidth yes no hstates
        choice states symbol input output size hfirst origin elapsed,
      ih (output ++ statesWord verifier code choice states symbol) hrest
        (elapsed + statesMoves width size states)]
    all_goals simp_all [symbolsWord, List.append_assoc, Nat.succ_mul]
    all_goals lia

private def leafWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) : List Γ :=
  if choice.secondState.1 = 0 ∧ choice.secondPosition.1 = 0 then
    symbolsWord verifier code choice states symbols else []

private def writeLeaf (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) : Prog (TMQuery tm) Unit :=
  whenPart yes no tick .secondState 0
    (whenPart yes no tick .secondPosition 0
      (writeSymbols verifier zero one tick code yes no states symbols))

private def leafMoves (width size : Nat) {count : Nat}
    (states : List (Option (Fin count))) (symbols : Nat) : Nat :=
  2 * checkMoves 0 size + symbols * statesMoves width size states

private theorem writeLeaf_spec (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ leafWord verifier code choice states symbols).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeLeaf (tm := tm) verifier zero one tick code yes no states symbols
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ leafWord verifier code choice states symbols) (some yes) origin final ∧
        cost.steps ≤ elapsed + leafMoves width size states symbols.length ⦄ := by
  have hs := whenPart_spec (tm := tm) yes no hstates tick .secondState 0
    (whenPart yes no tick .secondPosition 0
      (writeSymbols verifier zero one tick code yes no states symbols))
    choice input output
    (if choice.secondPosition.1 = 0 then symbolsWord verifier code choice states symbols else [])
    (checkMoves 0 choice.size + symbols.length * statesMoves width size states) (by
      intro hsecond place steps
      have hr := whenPart_spec (tm := tm) yes no hstates tick .secondPosition 0
        (writeSymbols verifier zero one tick code yes no states symbols) choice input output
        (symbolsWord verifier code choice states symbols)
        (symbols.length * statesMoves width size states) (by
          intro hposition place steps
          dsimp only [Part.value] at hsecond hposition
          exact writeSymbols_spec (tm := tm) verifier zero one hne tick code width hwidth yes no
            hstates choice states symbols input output size
            (by simpa [leafWord, Part.value, hsecond, hposition] using hsize) place steps)
              place steps
      vcgen [hr]
      all_goals grind [AtPair, Part.value, Nat.add_assoc])
    origin elapsed
  have hcap : choice.size ≤ size := by lia
  vcgen [writeLeaf, hs]
  all_goals simp_all [leafWord, Part.value, leafMoves, checkMoves, ite_and]
  all_goals lia

private def indexChoice (time position control otherPosition otherControl : Nat) : ActiveChoices :=
  ⟨(time, 0), (position, 0), (control, 0), (otherPosition, 0), (otherControl, 0)⟩

private def piece (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ)))
    (time position control otherPosition otherControl : Nat) : List Γ :=
  leafWord verifier code (indexChoice time position control otherPosition otherControl)
    states symbols

private def scannedWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) (times positions controls : Nat) : List Γ :=
  ChoiceIteration.word (piece verifier code states symbols) times positions controls

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem leafWord_indices (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) :
    leafWord verifier code choice states symbols = piece verifier code states symbols
      choice.time.1 choice.firstPosition.1 choice.firstState.1 choice.secondPosition.1
        choice.secondState.1 := rfl

private def forTransitions (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit :=
  markFirst tick (ChoiceIteration.afterFirstTime tm tick action)

omit [Encodable Γ] in
private theorem forTransitions_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (times positions controls : Nat) (input output : List Γ)
    (piece : Nat → Nat → Nat → Nat → Nat → List Γ) (label : Option tm.State)
    (size bound : Nat)
    (hleaf : ChoiceIteration.LeafSpec tick times positions controls input piece label action
      size bound)
    (hsize : times + 2 * positions + 2 * controls + input.length +
      (output ++ ChoiceIteration.word piece times positions controls).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ChoiceIteration.layout tick (times + 1) positions controls input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forTransitions (tm := tm) tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        ChoiceIteration.layout tick (times + 1) positions controls input
          (output ++ ChoiceIteration.word piece times positions controls)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          ChoiceIteration.iterationMoves size bound + 2 ⦄ := by
  have hrun (place : ℤ) (steps : Nat) := ChoiceIteration.forFiveChoices_spec tick action
    times positions controls input output piece label size bound hleaf hsize place steps
  have hafter (place : ℤ) (steps : Nat) := ChoiceIteration.afterFirstTime_spec tick action
    times positions controls input output
    (output ++ ChoiceIteration.word piece times positions controls)
    label (ChoiceIteration.iterationMoves size bound) hrun place steps
  have hmark := markFirst_spec tick (ChoiceIteration.afterFirstTime tm tick action) StackTape.nil
    (List.replicate times tick)
    (StackTape.separateWords [List.replicate positions tick, List.replicate controls tick,
      List.replicate positions tick, List.replicate controls tick, input]
        (StackTape.mapSome output))
    (StackTape.separateWords [List.replicate positions tick, List.replicate controls tick,
      List.replicate positions tick, List.replicate controls tick, input]
      (StackTape.mapSome (output ++ ChoiceIteration.word piece times positions controls)))
    label (ChoiceIteration.iterationMoves size bound + 2) hafter origin elapsed
  vcgen [forTransitions, hmark]
  all_goals simp_all [ChoiceIteration.layout, List.replicate_succ, Nat.add_assoc]

private noncomputable def writeAll (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State)
    (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ))) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ yes
  forTransitions tick (writeLeaf verifier zero one tick code yes no states symbols)

private theorem writeAll_spec (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no)
    (cases : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ)))
    (times positions controls : Nat) (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * controls + input.length +
      (output ++ scannedWord verifier code cases symbols times positions controls).length +
        32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ChoiceIteration.layout tick (times + 1) positions controls input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeAll (tm := tm) verifier zero one tick code yes no cases symbols
    ⦃ fun _ cost final => final.config = ⟨some yes,
        ChoiceIteration.layout tick (times + 1) positions controls input
          (output ++ scannedWord verifier code cases symbols times positions controls)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          ChoiceIteration.iterationMoves size (leafMoves width size cases symbols.length) +
            2 ⦄ := by
  let action := writeLeaf (tm := tm) verifier zero one tick code yes no cases symbols
  let leaf := piece verifier code cases symbols
  let bound := leafMoves width size cases symbols.length
  have hleaf : ChoiceIteration.LeafSpec tick times positions controls input leaf
      (some yes) action size bound := by
    intro time timeRest position positionRest control controlRest otherPosition otherPositionRest
      otherControl otherControlRest ht hp hs hop hos out hcap place steps
    let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
      (control, controlRest), (otherPosition, otherPositionRest), (otherControl, otherControlRest)⟩
    have hdata : choice.size + input.length +
        (out ++ leafWord verifier code choice cases symbols).length + 32 ≤ size := by
      rw [leafWord_indices]
      dsimp [choice, ActiveChoices.size]
      dsimp [leaf] at hcap
      lia
    have ha := writeLeaf_spec (tm := tm) verifier zero one hne tick code width hwidth yes no
      hstates choice cases symbols input out size hdata place steps
    simpa [AtPair, pairTape, ActiveChoices.leftWords, ActiveChoices.rightWords, choice,
      leafWord_indices, leaf, action, bound, and_assoc, Nat.add_assoc] using ha
  have hr := forTransitions_spec (tm := tm) tick action times positions controls input output
    leaf (some yes) size bound hleaf (by simpa only [scannedWord, leaf] using hsize) origin elapsed
  dsimp only [action] at hr
  vcgen [writeAll, hr]
  all_goals simp_all [scannedWord, leaf, bound]

private def verifierStates (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :
    List (Option (Fin (verifier.states + 1))) :=
  stateChoices (⟨verifier, [], 0, 0⟩ : BoundedVerification Γ)

private noncomputable def symbols : List (Option (TapeSymbol Γ)) :=
  (Finset.univ : Finset (Option (TapeSymbol Γ))).toList

/--
This template writes the clauses describing the symbol left under the verifier's head.
The verifier's transition cases are fixed with the program; the input and bounds are read
from the tape.
-/
private noncomputable def writeScannedClauses (tm : SingleTapeTM Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no : tm.State) :
    Prog (TMQuery tm) Unit :=
  writeAll verifier zero one tick code yes no (verifierStates verifier) symbols

private theorem filterFlatMap {α β : Type} (values : List α) (predicate : α → Bool)
    (f : α → List β) :
    (values.filter predicate).flatMap f =
      values.flatMap (fun value => if predicate value then f value else []) := by
  rw [← List.filterMap_eq_filter, List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
  congr 1
  funext value
  cases h : predicate value <;> simp [h]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem statesWord_eq (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (control : Option (Fin (verifier.states + 1))) (symbol : Option (TapeSymbol Γ))
    (hchoice : choice.firstState.1 = Encodable.encode control) :
    statesWord verifier code choice (verifierStates verifier) symbol =
      tapeUpdateWord code choice false symbol (instruction verifier control symbol).1 := by
  have hmem : control ∈ verifierStates verifier := by
    cases control <;> simp [verifierStates, stateChoices]
  have hn : (verifierStates verifier).Nodup := by
    simp only [verifierStates, stateChoices, List.nodup_cons]
    refine ⟨by simp, (List.nodup_finRange _).map ?_⟩
    intro first second he
    exact Option.some.inj he
  have hf : ((verifierStates verifier).filter (fun other => decide (other = control))) =
      [control] := by
    rw [List.filter_eq]
    simp [hn.count, hmem]
  have hw : statesWord verifier code choice (verifierStates verifier) symbol =
      ((verifierStates verifier).filter (fun other => decide (other = control))).flatMap
        (fun other => tapeUpdateWord code choice false symbol (instruction verifier other
          symbol).1) := by
    rw [filterFlatMap]
    simp [statesWord, stateWord, hchoice, Encodable.encode_injective.eq_iff, eq_comm]
  rw [hw, hf]
  simp

private noncomputable def statesPolynomial (width : Nat) {count : Nat}
    (states : List (Option (Fin count))) : Polynomial Nat :=
  (states.map fun control => Polynomial.C (4 * Encodable.encode control + 64) +
    4 * Polynomial.X + Polynomial.C (73728 * (width + 1)) * (Polynomial.X + 16) ^ 2).sum

private theorem eval_statesPolynomial (width size : Nat) {count : Nat}
    (states : List (Option (Fin count))) :
    (statesPolynomial width states).eval size = statesMoves width size states := by
  induction states with
  | nil => simp [statesPolynomial, statesMoves]
  | cons control rest ih =>
    simp only [statesPolynomial, statesMoves, List.map_cons, List.sum_cons,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow] at ih ⊢
    rw [ih]
    dsimp [checkMoves, tapeUpdateTime, literalTime, tapeLiteralTime, markedNumberBudget]
    ring

/--
This polynomial bounds writing the clauses for the cell under the verifier's head. Its
coefficients depend only on the verifier, alphabet, and fixed representation of formula symbols.
-/
private noncomputable def scannedTimeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width : Nat) : Polynomial Nat :=
  ChoiceIteration.iterationPolynomial
    (2 * (4 * Polynomial.X + 64) +
      Polynomial.C (symbols (Γ := Γ)).length * statesPolynomial width (verifierStates verifier)) + 2

omit [Inhabited Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem eval_scannedTimeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width size : Nat) :
    (scannedTimeBound verifier width).eval size =
      ChoiceIteration.iterationMoves size
        (leafMoves width size (verifierStates verifier) (symbols (Γ := Γ)).length) + 2 := by
  simp [scannedTimeBound, eval_statesPolynomial, leafMoves, checkMoves]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem piece_eq (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (states : List (Option (Fin (verifier.states + 1))))
    (symbols : List (Option (TapeSymbol Γ)))
    (time position control otherPosition otherControl : Nat) :
    piece verifier code states symbols time position control otherPosition otherControl =
      if otherControl = 0 then
        if otherPosition = 0 then
          symbolsWord verifier code (indexChoice time position control 0 0) states symbols
        else []
      else [] := by
  by_cases hp : otherPosition = 0 <;> by_cases hc : otherControl = 0 <;>
    simp [piece, leafWord, indexChoice, hp, hc]

omit [Inhabited Γ] [DecidableEq Γ] in
private theorem scannedWord_eq (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ) :
    scannedWord problem.verifier code (verifierStates problem.verifier) symbols
      problem.time (NPToSAT.Computation.width problem) (problem.verifier.states + 2) =
      (formulaPrefix ((writeClauses problem).rename Variable.name)).flatMap code := by
  have hfirst (count : Nat) (hcount : 0 < count) (text : List Γ) :
      (List.range count).flatMap (fun index => if index = 0 then text else []) = text := by
    obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : count ≠ 0)
    rw [List.range_succ_eq_map]
    simp
  have hw : 0 < NPToSAT.Computation.width problem := by dsimp [NPToSAT.Computation.width]; lia
  have hindices (count : Nat) : (List.finRange count).map Fin.val = List.range count := by
    ext index
    simp
  have hstate (time position : Nat) (control : Option (Fin (problem.verifier.states + 1)))
      (symbol : Option (TapeSymbol Γ)) :
      statesWord problem.verifier code (indexChoice time position (Encodable.encode control) 0 0)
        (verifierStates problem.verifier) symbol =
      tapeUpdateWord code (indexChoice time position (Encodable.encode control) 0 0) false symbol
        (instruction problem.verifier control symbol).1 :=
    statesWord_eq problem.verifier code _ control symbol rfl
  have hclause (time : Fin problem.time) (position : Fin (NPToSAT.Computation.width problem))
      (control : Option (Fin (problem.verifier.states + 1)))
      (symbol : Option (TapeSymbol Γ)) :
      (certificateEncoding.encode
        ((Clause.implies [Variable.head time.castSucc (position, control),
          Variable.tape time.castSucc position symbol]
          (Variable.tape time.succ position (instruction problem.verifier control symbol).1)).rename
            Variable.name) ++ [(Sum.inr 4 : CodeSymbol)]).flatMap code =
      tapeUpdateWord code (indexChoice time.val position.val (Encodable.encode control) 0 0)
        false symbol (instruction problem.verifier control symbol).1 := by
    simp [tapeUpdateWord, formulaPrefix, Clause.rename, Clause.implies, Clause.forbid,
      Literal.rename, Variable.name, headName, tapeName, indexChoice, Naming.bits]
  simp only [scannedWord, ChoiceIteration.word, piece_eq,
    hfirst (problem.verifier.states + 2) (by lia), hfirst (NPToSAT.Computation.width problem) hw]
  rw [← stateChoices_codes problem]
  simp_rw [← hindices, List.flatMap_map]
  simp only [symbolsWord, hstate, writeClauses, CNF.rename, controlChoices, formulaPrefix,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc, hclause, symbols]

/--
The program appends the clauses describing the written symbol, preserves the input and bounds,
and returns to the first symbol of the time bound. The polynomial is fixed with the verifier.
-/
@[spec] private theorem writeScannedClauses_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no : tm.State) (hstates : yes ≠ no) (problem : BoundedVerification Γ)
    (hverifier : problem.verifier = verifier) (input output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (output ++ (formulaPrefix ((writeClauses problem).rename Variable.name)).flatMap
          code).length +
          32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeScannedClauses tm verifier zero one tick code yes no
    ⦃ fun _ cost final => final.config = ⟨some yes,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) input
            (output ++ (formulaPrefix ((writeClauses problem).rename
              Variable.name)).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (scannedTimeBound verifier
          width).eval size ⦄ := by
  subst verifier
  have hs := writeAll_spec (tm := tm) problem.verifier zero one hne tick code width hwidth
    yes no hstates (verifierStates problem.verifier) symbols problem.time
    (NPToSAT.Computation.width problem)
    (problem.verifier.states + 2) input output size
    (by simpa only [scannedWord_eq] using hsize) label origin elapsed
  vcgen [writeScannedClauses, hs]
  all_goals simp_all [scannedWord_eq, eval_scannedTimeBound, Nat.add_assoc]

private def runCases {α : Type} (action : α → Prog (TMQuery tm) Unit) (cases : List α) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  cases.foldlM (fun _ value => action value) ()

omit [Encodable Γ] in
private theorem runCases_spec {α : Type} (action : α → Prog (TMQuery tm) Unit)
    (cases : List α) (written : α → List Γ) (budget : α → Nat)
    (At : List Γ → TMState tm → Prop) (base size : Nat)
    (haction : ∀ value ∈ cases, ∀ output,
      base + (output ++ written value).length ≤ size → ∀ elapsed,
      ⦃ fun cost current => At output current ∧ cost.steps ≤ elapsed ⦄
        action value
      ⦃ fun _ cost final => At (output ++ written value) final ∧
          cost.steps ≤ elapsed + budget value ⦄)
    (output : List Γ) (hsize : base + (output ++ cases.flatMap written).length ≤ size)
    (elapsed : Nat) :
    ⦃ fun cost current => At output current ∧ cost.steps ≤ elapsed ⦄
      runCases (tm := tm) action cases
    ⦃ fun _ cost final => At (output ++ cases.flatMap written) final ∧
        cost.steps ≤ elapsed + (cases.map budget).sum ⦄ := by
  let inv : Std.WP.Invariant α Unit (TMCost → TMState tm → Prop) :=
    fun pref _ _ cost current => At (output ++ pref.flatMap written) current ∧
      cost.steps ≤ elapsed + (pref.map budget).sum
  have hs := Std.WP.Spec.foldlM_list (xs := cases) (init := ())
    (f := fun _ value => action value) (epost := ⊥) inv (by
      intro pref value suff hcases _
      have hmem : value ∈ cases := by rw [hcases]; simp
      have hcap : base + ((output ++ pref.flatMap written) ++ written value).length ≤ size := by
        simp only [hcases, List.flatMap_append, List.flatMap_cons, List.length_append] at hsize
        simp only [List.length_append]
        lia
      vcgen [haction value hmem (output ++ pref.flatMap written) hcap
        (elapsed + (pref.map budget).sum)]
      all_goals simp_all [inv, List.flatMap_append, List.map_append, List.sum_append,
        List.append_assoc, Nat.add_assoc])
  vcgen [runCases, hs]
  all_goals simp_all [inv]

private def movementOffset : Option Bool → Nat
  | none => 1
  | some false => 0
  | some true => 2

private def movementWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (movement : Option Bool) (symbol : Option (TapeSymbol Γ)) : List Γ :=
  if choice.firstPosition.1 + movementOffset movement = choice.secondPosition.1 + 1 then []
  else forbiddenWord code choice symbol

private noncomputable def writeMovement (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (yes no extra : tm.State) (movement : Option Bool) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  comparePositionsOffset tm zero one tick yes no extra (movementOffset movement)
  ifₜ state =ₜ some yes then
    writeForbiddenControlClause tm zero one tick code symbol
  else
    pure ()
  state ←ₜ yes

private theorem writeMovement_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (choice : ActiveChoices) (movement : Option Bool) (symbol : Option (TapeSymbol Γ))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ movementWord code choice movement symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeMovement (tm := tm) zero one tick code yes no extra movement symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ movementWord code choice movement symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + comparisonOffsetTime size (movementOffset movement) +
          forbiddenTime width size ⦄ := by
  have hcap : choice.size + input.length + output.length + 32 ≤ size := by
    simp only [List.length_append] at hsize
    lia
  have hc := comparePositionsOffset_spec (tm := tm) zero one hne tick yes no extra
    hfirst hlast hother (movementOffset movement) choice input output size hcap (some yes)
    origin elapsed
  by_cases hm : choice.firstPosition.1 + movementOffset movement = choice.secondPosition.1 + 1
  · vcgen [writeMovement, hc]
    all_goals simp_all [AtPair, movementWord, Ne.symm hfirst]
    all_goals lia
  · have hw := writeForbiddenControlClause_spec (tm := tm) zero one hne tick code width hwidth
      choice symbol input output size (by simpa only [movementWord, ite_eq_right hm] using hsize)
      (some yes) origin (elapsed + comparisonOffsetTime size (movementOffset movement))
    vcgen [writeMovement, hc, hw]
    all_goals simp_all [AtPair, movementWord]

private abbrev Controls (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :=
  Option (Fin (verifier.states + 1)) × Option (Fin (verifier.states + 1))

private def controlBodyWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) : List Γ :=
  if controls.2 = (instruction verifier controls.1 symbol).2.2 then
    movementWord code choice (instruction verifier controls.1 symbol).2.1 symbol
  else forbiddenWord code choice symbol

private noncomputable def writeControlBody
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State)
    (controls : Controls verifier) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  if controls.2 = (instruction verifier controls.1 symbol).2.2 then
    writeMovement zero one tick code yes no extra
      (instruction verifier controls.1 symbol).2.1 symbol
  else
    writeForbiddenControlClause tm zero one tick code symbol

private def controlBodyMoves (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) : Nat :=
  comparisonOffsetTime size (movementOffset (instruction verifier controls.1 symbol).2.1) +
    forbiddenTime width size

private theorem writeControlBody_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (choice : ActiveChoices) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ controlBodyWord verifier code choice controls symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeControlBody (tm := tm) verifier zero one tick code yes no extra controls symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ controlBodyWord verifier code choice controls symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + controlBodyMoves verifier width size controls symbol ⦄ := by
  by_cases hs : controls.2 = (instruction verifier controls.1 symbol).2.2
  · simp only [writeControlBody, ite_eq_left hs]
    have hm := writeMovement_spec (tm := tm) zero one hne tick code width hwidth yes no extra
      hfirst hlast hother choice (instruction verifier controls.1 symbol).2.1 symbol input output
      size
      (by simpa only [controlBodyWord, ite_eq_left hs] using hsize) origin elapsed
    vcgen [hm]
    all_goals simp_all [controlBodyWord, controlBodyMoves, AtPair, Nat.add_assoc]
  · simp only [writeControlBody, ite_eq_right hs]
    have hw := writeForbiddenControlClause_spec (tm := tm) zero one hne tick code width hwidth
      choice symbol input output size
      (by simpa only [controlBodyWord, ite_eq_right hs] using hsize) (some yes) origin elapsed
    vcgen [hw]
    all_goals simp_all [controlBodyWord, controlBodyMoves, AtPair]
    all_goals lia

private def controlCaseWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) : List Γ :=
  if choice.firstState.1 = Encodable.encode controls.1 then
    if choice.secondState.1 = Encodable.encode controls.2 then
      controlBodyWord verifier code choice controls symbol else []
  else []

private noncomputable def writeControlCase
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State)
    (controls : Controls verifier) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit :=
  whenPart yes no tick .firstState (Encodable.encode controls.1)
    (whenPart yes no tick .secondState (Encodable.encode controls.2)
      (writeControlBody verifier zero one tick code yes no extra controls symbol))

private def controlCaseMoves (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) : Nat :=
  checkMoves (Encodable.encode controls.1) size + checkMoves (Encodable.encode controls.2) size +
    controlBodyMoves verifier width size controls symbol

private theorem writeControlCase_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (choice : ActiveChoices) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ)) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ controlCaseWord verifier code choice controls symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeControlCase (tm := tm) verifier zero one tick code yes no extra controls symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ controlCaseWord verifier code choice controls symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + controlCaseMoves verifier width size controls symbol ⦄ := by
  have hs := whenPart_spec (tm := tm) yes no hfirst tick .firstState (Encodable.encode controls.1)
    (whenPart yes no tick .secondState (Encodable.encode controls.2)
      (writeControlBody verifier zero one tick code yes no extra controls symbol))
    choice input output
    (if choice.secondState.1 = Encodable.encode controls.2 then
      controlBodyWord verifier code choice controls symbol else [])
    (checkMoves (Encodable.encode controls.2) choice.size +
      controlBodyMoves verifier width size controls symbol) (by
      intro hq place steps
      have hr := whenPart_spec (tm := tm) yes no hfirst tick .secondState
        (Encodable.encode controls.2)
        (writeControlBody verifier zero one tick code yes no extra controls symbol)
        choice input output (controlBodyWord verifier code choice controls symbol)
        (controlBodyMoves verifier width size controls symbol) (by
          intro hq' place steps
          dsimp only [Part.value] at hq hq'
          exact writeControlBody_spec (tm := tm) verifier zero one hne tick code width hwidth
            yes no extra hfirst hlast hother choice controls symbol input output size
            (by simpa only [controlCaseWord, ite_eq_left hq, ite_eq_left hq'] using hsize)
            place steps)
        place steps
      vcgen [hr]
      all_goals grind [AtPair, Part.value, Nat.add_assoc]) origin elapsed
  have hcap : choice.size ≤ size := by lia
  vcgen [writeControlCase, hs]
  all_goals simp_all [Part.value, controlCaseWord, controlCaseMoves, checkMoves]
  all_goals lia

private def controlPairs (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :
    List (Controls verifier) :=
  (verifierStates verifier).product (verifierStates verifier)

private def controlSymbolWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) (symbol : Option (TapeSymbol Γ)) :
    List Γ :=
  (controlPairs verifier).flatMap fun controls =>
    controlCaseWord verifier code choice controls symbol

private noncomputable def writeControlSymbol
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State)
    (symbol : Option (TapeSymbol Γ)) : Prog (TMQuery tm) Unit :=
  runCases (fun controls =>
    writeControlCase verifier zero one tick code yes no extra controls symbol)
    (controlPairs verifier)

private def controlSymbolMoves (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) (symbol : Option (TapeSymbol Γ)) : Nat :=
  ((controlPairs verifier).map fun controls =>
    controlCaseMoves verifier width size controls symbol).sum

private theorem writeControlSymbol_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (choice : ActiveChoices) (symbol : Option (TapeSymbol Γ))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ controlSymbolWord verifier code choice symbol).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeControlSymbol (tm := tm) verifier zero one tick code yes no extra symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ controlSymbolWord verifier code choice symbol) (some yes) origin final ∧
        cost.steps ≤ elapsed + controlSymbolMoves verifier width size symbol ⦄ := by
  have hs := runCases_spec (tm := tm)
    (fun controls => writeControlCase verifier zero one tick code yes no extra controls symbol)
    (controlPairs verifier) (fun controls => controlCaseWord verifier code choice controls symbol)
    (fun controls => controlCaseMoves verifier width size controls symbol)
    (fun written => AtPair tick choice input written (some yes) origin)
    (choice.size + input.length + 32) size (by
      intro controls _ written hcap steps
      have hc := writeControlCase_spec (tm := tm) verifier zero one hne tick code width hwidth
        yes no extra hfirst hlast hother choice controls symbol input written size
        (by lia) origin steps
      vcgen [hc]) output (by simpa [controlSymbolWord, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hsize) elapsed
  vcgen [writeControlSymbol, hs]
  all_goals simp_all [controlSymbolWord, controlSymbolMoves, AtPair]

private noncomputable def controlLeafWord (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) : List Γ :=
  (symbols (Γ := Γ)).flatMap fun symbol => controlSymbolWord verifier code choice symbol

private noncomputable def writeControlLeaf
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State) :
    Prog (TMQuery tm) Unit :=
  runCases (fun symbol =>
    writeControlSymbol verifier zero one tick code yes no extra symbol) symbols

private noncomputable def controlLeafMoves
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) : Nat :=
  (symbols.map fun symbol => controlSymbolMoves verifier width size symbol).sum

private theorem writeControlLeaf_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ controlLeafWord verifier code choice).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some yes) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeControlLeaf (tm := tm) verifier zero one tick code yes no extra
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ controlLeafWord verifier code choice) (some yes) origin final ∧
        cost.steps ≤ elapsed + controlLeafMoves verifier width size ⦄ := by
  have hs := runCases_spec (tm := tm)
    (fun symbol => writeControlSymbol verifier zero one tick code yes no extra symbol)
    symbols (fun symbol => controlSymbolWord verifier code choice symbol)
    (fun symbol => controlSymbolMoves verifier width size symbol)
    (fun written => AtPair tick choice input written (some yes) origin)
    (choice.size + input.length + 32) size (by
      intro symbol _ written hcap steps
      have hc := writeControlSymbol_spec (tm := tm) verifier zero one hne tick code width hwidth
        yes no extra hfirst hlast hother choice symbol input written size (by lia) origin steps
      vcgen [hc]) output (by simpa [controlLeafWord, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hsize) elapsed
  vcgen [writeControlLeaf, hs]
  all_goals simp_all [controlLeafWord, controlLeafMoves, AtPair]

private noncomputable def controlPiece
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (time position control otherPosition otherControl : Nat) :
    List Γ :=
  controlLeafWord verifier code (indexChoice time position control otherPosition otherControl)

private noncomputable def controlWord
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (times positions controls : Nat) : List Γ :=
  ChoiceIteration.word (controlPiece verifier code) times positions controls

omit [Inhabited Γ] [DecidableEq Γ] in
private theorem controlLeafWord_indices
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) :
    controlLeafWord verifier code choice = controlPiece verifier code choice.time.1
      choice.firstPosition.1 choice.firstState.1 choice.secondPosition.1 choice.secondState.1 := rfl

/--
This template writes the clauses describing the verifier's next head position and state.
Its transition cases are fixed with the program. It reads the selected positions from the tape
and preserves the bounds and original input.
-/
private noncomputable def writeControlClauses (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ yes
  forTransitions tick (writeControlLeaf verifier zero one tick code yes no extra)

private theorem writeControlWords_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (times positions controls : Nat) (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * controls + input.length +
      (output ++ controlWord verifier code times positions controls).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ChoiceIteration.layout tick (times + 1) positions controls input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeControlClauses tm verifier zero one tick code yes no extra
    ⦃ fun _ cost final => final.config = ⟨some yes,
        ChoiceIteration.layout tick (times + 1) positions controls input
          (output ++ controlWord verifier code times positions controls)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          ChoiceIteration.iterationMoves size (controlLeafMoves verifier width size) + 2 ⦄ := by
  let action := writeControlLeaf (tm := tm) verifier zero one tick code yes no extra
  let leaf := controlPiece verifier code
  let bound := controlLeafMoves verifier width size
  have hleaf : ChoiceIteration.LeafSpec tick times positions controls input leaf
      (some yes) action size bound := by
    intro time timeRest position positionRest control controlRest otherPosition otherPositionRest
      otherControl otherControlRest ht hp hs hop hos out hcap place steps
    let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
      (control, controlRest), (otherPosition, otherPositionRest), (otherControl, otherControlRest)⟩
    have hdata : choice.size + input.length +
        (out ++ controlLeafWord verifier code choice).length + 32 ≤ size := by
      rw [controlLeafWord_indices]
      dsimp [choice, ActiveChoices.size]
      dsimp [leaf] at hcap
      lia
    have ha := writeControlLeaf_spec (tm := tm) verifier zero one hne tick code width hwidth
      yes no extra hfirst hlast hother choice input out size hdata place steps
    simpa [AtPair, pairTape, ActiveChoices.leftWords, ActiveChoices.rightWords, choice,
      controlLeafWord_indices, leaf, action, bound, and_assoc, Nat.add_assoc] using ha
  have hr := forTransitions_spec (tm := tm) tick action times positions controls input output
    leaf (some yes) size bound hleaf (by simpa only [controlWord, leaf] using hsize) origin elapsed
  dsimp only [action] at hr
  vcgen [writeControlClauses, hr]
  all_goals simp_all [controlWord, leaf, bound]

private noncomputable def controlCasePolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width : Nat) (controls : Controls verifier) (symbol : Option (TapeSymbol Γ)) :
    Polynomial Nat :=
  Polynomial.C (4 * Encodable.encode controls.1 + 4 * Encodable.encode controls.2 + 128) +
    8 * Polynomial.X + Polynomial.C 4096 *
      (Polynomial.X +
        Polynomial.C (movementOffset (instruction verifier controls.1 symbol).2.1 + 15)) ^ 2 +
        Polynomial.C (61440 * (width + 1)) * (Polynomial.X + 16) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem eval_controlCasePolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) (controls : Controls verifier) (symbol : Option (TapeSymbol Γ)) :
    (controlCasePolynomial verifier width controls symbol).eval size =
      controlCaseMoves verifier width size controls symbol := by
  simp only [controlCasePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_pow]
  dsimp [controlCaseMoves, checkMoves, controlBodyMoves, comparisonOffsetTime, forbiddenTime,
    markedNumberBudget]
  ring

private noncomputable def controlSymbolPolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width : Nat) (symbol : Option (TapeSymbol Γ)) : Polynomial Nat :=
  ((controlPairs verifier).map fun controls =>
    controlCasePolynomial verifier width controls symbol).sum

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem eval_controlSymbolPolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (width size : Nat) (symbol : Option (TapeSymbol Γ)) :
    (controlSymbolPolynomial verifier width symbol).eval size =
      controlSymbolMoves verifier width size symbol := by
  simp [controlSymbolPolynomial, controlSymbolMoves, Polynomial.eval_listSum,
    eval_controlCasePolynomial, Function.comp_def]

private noncomputable def controlLeafPolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width : Nat) : Polynomial Nat :=
  (symbols.map fun symbol => controlSymbolPolynomial verifier width symbol).sum

omit [Inhabited Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem eval_controlLeafPolynomial
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width size : Nat) :
    (controlLeafPolynomial verifier width).eval size = controlLeafMoves verifier width size := by
  simp [controlLeafPolynomial, controlLeafMoves, Polynomial.eval_listSum,
    eval_controlSymbolPolynomial, Function.comp_def]

/-- This polynomial bounds writing the next-head clauses for the fixed verifier. -/
private noncomputable def controlTimeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width : Nat) : Polynomial Nat :=
  ChoiceIteration.iterationPolynomial (controlLeafPolynomial verifier width) + 2

omit [Inhabited Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem eval_controlTimeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width size : Nat) :
    (controlTimeBound verifier width).eval size =
      ChoiceIteration.iterationMoves size (controlLeafMoves verifier width size) + 2 := by
  simp [controlTimeBound, eval_controlLeafPolynomial]

private theorem selectedCodes {α β : Type} [Encodable α] (cases : List α)
    (hnodup : cases.Nodup) (actual : α) (hmem : actual ∈ cases) (part : α → List β) :
    cases.flatMap (fun value => if Encodable.encode actual = Encodable.encode value
      then part value else []) = part actual := by
  have hf : (cases.filter (fun value => decide (value = actual))) = [actual] := by
    rw [List.filter_eq]
    simp [hnodup.count, hmem]
  have he : cases.flatMap (fun value => if Encodable.encode actual = Encodable.encode value
      then part value else []) =
        (cases.filter (fun value => decide (value = actual))).flatMap part := by
    rw [filterFlatMap]
    simp [Encodable.encode_injective.eq_iff, eq_comm]
  rw [he, hf]
  simp

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem verifierStates_mem
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (control : Option (Fin (verifier.states + 1))) : control ∈ verifierStates verifier := by
  cases control <;> simp [verifierStates, stateChoices]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem verifierStates_nodup
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :
    (verifierStates verifier).Nodup := by
  simp only [verifierStates, stateChoices, List.nodup_cons]
  refine ⟨by simp, (List.nodup_finRange _).map ?_⟩
  intro first second he
  exact Option.some.inj he

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem controlSymbolWord_eq
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (code : CodeSymbol → List Γ) (choice : ActiveChoices) (controls : Controls verifier)
    (symbol : Option (TapeSymbol Γ))
    (hfirst : choice.firstState.1 = Encodable.encode controls.1)
    (hsecond : choice.secondState.1 = Encodable.encode controls.2) :
    controlSymbolWord verifier code choice symbol =
      controlBodyWord verifier code choice controls symbol := by
  have hinner (first : Option (Fin (verifier.states + 1))) :
      (verifierStates verifier).flatMap (fun second =>
        controlCaseWord verifier code choice (first, second) symbol) =
      if choice.firstState.1 = Encodable.encode first then
        controlBodyWord verifier code choice (first, controls.2) symbol else [] := by
    by_cases hc : choice.firstState.1 = Encodable.encode first
    · simpa only [controlCaseWord, Prod.fst, Prod.snd, ite_eq_left hc, hsecond] using
        selectedCodes (verifierStates verifier) (verifierStates_nodup verifier) controls.2
          (verifierStates_mem verifier controls.2)
          (fun second => controlBodyWord verifier code choice (first, second) symbol)
    · simp [controlCaseWord, hc]
  simp only [controlSymbolWord, controlPairs, List.product, List.flatMap_assoc,
    List.flatMap_map, hinner, hfirst]
  exact selectedCodes (verifierStates verifier) (verifierStates_nodup verifier) controls.1
    (verifierStates_mem verifier controls.1)
    (fun first => controlBodyWord verifier code choice (first, controls.2) symbol)

private theorem moved_iff_offset {width : Nat} (first second : Fin width) (movement : Option Bool) :
    Moved first movement second ↔ first.val + movementOffset movement = second.val + 1 := by
  cases movement with
  | none => simp [Moved, movementOffset, Fin.ext_iff, eq_comm]
  | some direction =>
    cases direction <;> simp only [Moved, movementOffset, Nat.add_zero] <;> lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem controlBodyWord_eq (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (time : Fin problem.time) (first second :
      Fin (NPToSAT.Computation.width problem) × Option (Fin (problem.verifier.states + 1)))
    (symbol : Option (TapeSymbol Γ)) :
    controlBodyWord problem.verifier code
      (indexChoice time.val first.1.val (Encodable.encode first.2)
        second.1.val (Encodable.encode second.2)) (first.2, second.2) symbol =
      if controlAllowed problem first symbol second then [] else
        forbiddenWord code (indexChoice time.val first.1.val (Encodable.encode first.2)
          second.1.val (Encodable.encode second.2)) symbol := by
  simp only [controlBodyWord, movementWord, indexChoice, controlAllowed, moved_iff_offset,
    ]
  split_ifs <;> simp_all

omit [Inhabited Γ] [DecidableEq Γ] in
private theorem controlWord_eq (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ) :
    controlWord problem.verifier code problem.time (NPToSAT.Computation.width problem)
      (problem.verifier.states + 2) =
      (formulaPrefix ((NPToSAT.controlClauses problem).rename Variable.name)).flatMap code := by
  have hindices (count : Nat) : (List.finRange count).map Fin.val = List.range count := by
    ext index
    simp
  have hselected (time position otherPosition : Nat)
      (first second : Option (Fin (problem.verifier.states + 1)))
      (symbol : Option (TapeSymbol Γ)) :
      controlSymbolWord problem.verifier code
        (indexChoice time position (Encodable.encode first) otherPosition (Encodable.encode second))
        symbol =
      controlBodyWord problem.verifier code
        (indexChoice time position (Encodable.encode first) otherPosition (Encodable.encode second))
        (first, second) symbol :=
    controlSymbolWord_eq problem.verifier code _ (first, second) symbol rfl rfl
  have hclause (time : Fin problem.time) (first second :
      Fin (NPToSAT.Computation.width problem) × Option (Fin (problem.verifier.states + 1)))
      (symbol : Option (TapeSymbol Γ)) :
      (certificateEncoding.encode
        ((Clause.forbid [Variable.head time.castSucc first,
          Variable.tape time.castSucc first.1 symbol,
          Variable.head time.succ second]).rename Variable.name) ++
            [(Sum.inr 4 : CodeSymbol)]).flatMap code =
      forbiddenWord code (indexChoice time.val first.1.val (Encodable.encode first.2)
        second.1.val (Encodable.encode second.2)) symbol := by
    simp [forbiddenWord, formulaPrefix, Clause.rename, Clause.forbid, Literal.rename,
      Variable.name, headNameAtTime, tapeName, indexChoice, Naming.bits]
  simp only [controlWord, ChoiceIteration.word, controlPiece, controlLeafWord]
  rw [← stateChoices_codes problem]
  simp_rw [← hindices, List.flatMap_map]
  simp only [hselected, NPToSAT.controlClauses, CNF.rename, controlChoices, formulaPrefix,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc]
  simp only [symbols]
  congr 1
  funext time
  congr 1
  funext firstPosition
  congr 1
  funext firstControl
  congr 1
  funext secondPosition
  congr 1
  funext secondControl
  congr 1
  funext symbol
  rw [controlBodyWord_eq code problem time (firstPosition, firstControl)
    (secondPosition, secondControl) symbol]
  by_cases h : controlAllowed problem (firstPosition, firstControl) symbol
      (secondPosition, secondControl)
  · simp [h]
  · have hc := hclause time (firstPosition, firstControl) (secondPosition, secondControl) symbol
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hc
    simpa only [h, ite_false, List.flatMap_cons, List.flatMap_nil,
      List.flatMap_append, List.append_nil] using hc.symm

/--
The program writes the clauses describing the next head position and state. It preserves the
bounds, original input, and head position within the fixed polynomial move bound.
-/
@[spec] private theorem writeControlClauses_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (problem : BoundedVerification Γ) (hverifier : problem.verifier = verifier)
    (input output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (output ++ (formulaPrefix ((NPToSAT.controlClauses problem).rename Variable.name)).flatMap
          code).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick (problem.time + 1) (NPToSAT.Computation.width problem)
        (problem.verifier.states + 2) input output label origin current ∧ cost.steps ≤ elapsed ⦄
      writeControlClauses tm verifier zero one tick code yes no extra
    ⦃ fun _ cost final => AtInput tick (problem.time + 1) (NPToSAT.Computation.width problem)
        (problem.verifier.states + 2) input
          (output ++ (formulaPrefix ((NPToSAT.controlClauses problem).rename Variable.name)).flatMap
            code) (some yes) origin final ∧
        cost.steps ≤ elapsed + (controlTimeBound verifier width).eval size ⦄ := by
  subst verifier
  have hs := writeControlWords_spec (tm := tm) problem.verifier zero one hne tick code width hwidth
    yes no extra hfirst hlast hother problem.time (NPToSAT.Computation.width problem)
    (problem.verifier.states + 2) input output size
    (by simpa only [controlWord_eq] using hsize) label origin elapsed
  vcgen [hs]
  all_goals simp_all [AtInput, ChoiceIteration.layout, controlWord_eq, eval_controlTimeBound,
    Nat.add_assoc]

/-- This polynomial bounds writing all transition clauses for the fixed verifier. -/
noncomputable def transitionTimeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width : Nat) : Polynomial Nat :=
  scannedTimeBound verifier width + controlTimeBound verifier width +
    Polynomial.C (4194304 * ((symbols (Γ := Γ)).length + 1) * (width + 1)) * (Polynomial.X + 16) ^ 7

/--
This template writes the clauses for every transition of the verifier. It describes the
written symbol, the next head and state, and the cells that stay unchanged. The transition cases
are fixed with the program; the input and bounds are read from the tape and preserved.
-/
noncomputable def writeTransitions (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes no extra : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeScannedClauses tm verifier zero one tick code yes no
  writeControlClauses tm verifier zero one tick code yes no extra
  TransitionWriting.writeUnchangedClauses tm zero one tick code symbols yes no extra

/--
The program appends the clauses for consecutive configurations of the verifier and preserves
the input, bounds, and starting head position. The displayed polynomial bounds all head moves.
-/
@[spec] theorem writeTransitions_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes no extra : tm.State) (hfirst : yes ≠ no) (hlast : yes ≠ extra) (hother : no ≠ extra)
    (problem : BoundedVerification Γ) (hverifier : problem.verifier = verifier)
    (input output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) +
      input.length + (output ++
        (formulaPrefix ((NPToSAT.stepClauses problem).rename Variable.name)).flatMap code).length +
          32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick (problem.time + 1) (NPToSAT.Computation.width problem)
        (problem.verifier.states + 2) input output label origin current ∧ cost.steps ≤ elapsed ⦄
      writeTransitions tm verifier zero one tick code yes no extra
    ⦃ fun _ cost final => AtInput tick (problem.time + 1) (NPToSAT.Computation.width problem)
        (problem.verifier.states + 2) input (output ++
          (formulaPrefix ((NPToSAT.stepClauses problem).rename Variable.name)).flatMap code)
          (some yes) origin final ∧
        cost.steps ≤ elapsed + (transitionTimeBound verifier width).eval size ⦄ := by
  let first :=
    (formulaPrefix ((NPToSAT.Computation.writeClauses problem).rename Variable.name)).flatMap code
  let second := (formulaPrefix ((NPToSAT.controlClauses problem).rename Variable.name)).flatMap code
  let third :=
    (formulaPrefix
      ((NPToSAT.Computation.unchangedClauses problem).rename Variable.name)).flatMap code
  have heq : (formulaPrefix ((NPToSAT.stepClauses problem).rename Variable.name)).flatMap code =
      first ++ second ++ third := by
    simp [NPToSAT.stepClauses, CNF.rename, first, second, third, List.flatMap_append,
      List.append_assoc]
  have hs₁ : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length + (output ++ first).length + 32 ≤ size := by
    rw [heq] at hsize
    simp only [List.length_append] at hsize ⊢
    lia
  have hs₂ : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (output ++ first ++ second).length + 32 ≤ size := by
    rw [heq] at hsize
    simp only [List.length_append] at hsize ⊢
    lia
  have hs₃ : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (output ++ first ++ second ++ third).length + 32 ≤ size := by
    simpa only [heq, List.append_assoc] using hsize
  have h₁ := writeScannedClauses_spec (tm := tm) verifier zero one hne tick code width hwidth
    yes no hfirst problem hverifier input output size hs₁ label origin elapsed
  have h₂ := writeControlClauses_spec (tm := tm) verifier zero one hne tick code width hwidth
    yes no extra hfirst hlast hother problem hverifier input (output ++ first) size hs₂
    (some yes) origin (elapsed + (scannedTimeBound verifier width).eval size)
  have hu := TransitionWriting.writeUnchangedClauses_spec (tm := tm) zero one hne tick code
    width hwidth symbols yes no extra hfirst hlast hother problem.time
    (NPToSAT.Computation.width problem)
    (problem.verifier.states + 2) input (output ++ first ++ second) size
    (by simpa only [symbols, TransitionWriting.unchangedWord_eq, third] using hs₃)
    (some yes) origin (elapsed + (scannedTimeBound verifier width).eval size +
      (controlTimeBound verifier width).eval size)
  have hword : unchangedWord code symbols problem.time (NPToSAT.Computation.width problem)
      (problem.verifier.states + 2) = third := by
    simpa only [symbols, third] using TransitionWriting.unchangedWord_eq code problem
  have ht := TransitionWriting.unchangedTime_le width size (symbols (Γ := Γ)).length
  vcgen [writeTransitions, h₁, h₂, hu]
  all_goals simp_all only [AtInput, symbols,
    transitionTimeBound, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat, first, second, third,
    List.append_assoc]
  all_goals lia

end Algolean.Algorithms.NPToSAT.Writing
