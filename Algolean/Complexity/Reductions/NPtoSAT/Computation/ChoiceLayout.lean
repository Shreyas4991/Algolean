/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting

/-!
# Selected times, positions, and states on one tape

* `ActiveChoices` records the lengths before and after five selected cells in unary words.
* `pairTape` describes those words, the original input, and the output. A blank marks each
  selected cell, and the head rests at the selected second-state cell.
* `AtPair` also records the finite control state and the head position. `AtPairCounter` allows
  a temporary counter farther left.

The data here describe tape configurations. The containing machine reads every count from
its tape; these descriptions do not choose a different program for different inputs.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.Computation.HeadChoices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines

variable {Γ : Type} [Inhabited Γ] [Fintype Γ]
variable {tm : SingleTapeTM Γ}

/-- Each pair counts the unary cells before and after one temporarily erased cell. -/
structure ActiveChoices where
  /-- This pair locates the recorded time. -/
  time : Nat × Nat
  /-- This pair locates the first head position. -/
  firstPosition : Nat × Nat
  /-- This pair locates the first state, with zero meaning halt. -/
  firstState : Nat × Nat
  /-- This pair locates the second head position. -/
  secondPosition : Nat × Nat
  /-- This pair locates the second state, with zero meaning halt. -/
  secondState : Nat × Nat

/-- This counts all unary cells before and after the five currently chosen cells. -/
@[expose] def ActiveChoices.size (choice : ActiveChoices) : Nat :=
  choice.time.1 + choice.time.2 + choice.firstPosition.1 + choice.firstPosition.2 +
    choice.firstState.1 + choice.firstState.2 + choice.secondPosition.1 +
    choice.secondPosition.2 + choice.secondState.1 + choice.secondState.2

/-- These are the eight preserved unary parts, from nearest to farthest left. -/
@[expose] def ActiveChoices.leftWords (tick : Γ) (choice : ActiveChoices) : List (List Γ) :=
  [List.replicate choice.secondPosition.2 tick, List.replicate choice.secondPosition.1 tick,
    List.replicate choice.firstState.2 tick, List.replicate choice.firstState.1 tick,
    List.replicate choice.firstPosition.2 tick, List.replicate choice.firstPosition.1 tick,
    List.replicate choice.time.2 tick, List.replicate choice.time.1 tick]

/-- These are the remaining second-state cells and the preserved input after the head. -/
@[expose] def ActiveChoices.rightWords (tick : Γ) (choice : ActiveChoices) (input : List Γ) :
    List (List Γ) :=
  [List.replicate choice.secondState.2 tick, input]

/--
This is the tape while both head choices are selected. A blank marks each selected unary cell,
and the head is at the blank marking the second state. The original input and output follow.
-/
@[expose] def pairTape (tick : Γ) (choice : ActiveChoices) (input output : List Γ)
    (counter : List Γ := []) : BiTape Γ :=
  markedUnaryTape (ActiveChoices.leftWords tick choice)
    (List.replicate choice.secondState.1 tick)
    (ActiveChoices.rightWords tick choice input) output counter

/-- This states the active choices, preserved words, control state, and head position. -/
@[expose] def AtPair (tick : Γ) (choice : ActiveChoices) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, pairTape tick choice input output⟩ ∧ current.headPos = origin



/-- This records the same selected cells with a temporary counter farther left. -/
@[expose] def AtPairCounter (tick : Γ) (choice : ActiveChoices) (input output counter : List Γ)
    (label : Option tm.State) (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, pairTape tick choice input output counter⟩ ∧ current.headPos = origin

omit [Inhabited Γ] [Fintype Γ] in
/-- The source words contain all ten unary parts, the input, and ten separating blanks. -/
@[simp, grind =] theorem ActiveChoices.source_span (tick : Γ) (choice : ActiveChoices)
    (input : List Γ) :
    regionSpan (choice.leftWords tick) + choice.secondState.1 +
      regionSpan (choice.rightWords tick input) = choice.size + input.length + 10 := by
  simp [ActiveChoices.leftWords, ActiveChoices.rightWords, ActiveChoices.size, regionSpan]
  ring

end Algolean.Algorithms.NPToSAT.Computation.HeadChoices
