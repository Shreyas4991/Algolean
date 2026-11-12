/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.ChoiceLayout
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.VariableNames
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnarySuccessorWriting

/-!
# Writing head and tape variables in clauses

* `writePrefix` starts a variable name with its selected time and position.
* `writeHeadLiteralAtTime` writes a head variable for a selected position and state. It can use
  the selected time or the following time.
* `writeTapeLiteral` writes a signed tape variable for a selected time and position. It can
  use the following time instead, which is needed for the result of a verifier transition.
* Each writer uses the existing variable names and SAT representation. It preserves the selected
  counts, original input, and head position and gives a quadratic time bound.

The time, position, and state counts are stored as repetitions of one tape symbol. The same
finite program reads these counts on every run. The alphabet symbol and the choices of sign,
position word, and time offset are fixed when the containing machine includes this template.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Computation.LiteralWriting

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT HeadChoices
open Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the start of an encoded literal: its sign, variable kind, time, and position. -/
@[expose] def prefixWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (positive head successor second : Bool) : List Γ :=
  code (if positive then .inr 0 else .inr 1) ++ code (.inl true) ++ code (.inl head) ++
    (unaryNumberBits true (choice.time.1 + successor.toNat)).flatMap (fun bit => code (.inl bit)) ++
    (unaryNumberBits true
      (if second then choice.secondPosition.1 else choice.firstPosition.1)).flatMap
        (fun bit => code (.inl bit))

/-- This starts a literal by reading its time and position from the selected tape cells. -/
def writePrefix (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (positive head successor second : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendAcross tm (code (if positive then .inr 0 else .inr 1) ++
    code (.inl true) ++ code (.inl head)) 2
  appendEarlierOffsetAtMark zero one tick (fun bit => code (.inl bit)) true successor 0 7 11
  if second then
    appendEarlierAtMark zero one tick (fun bit => code (.inl bit)) true 6 1 11
  else
    appendEarlierAtMark zero one tick (fun bit => code (.inl bit)) true 2 5 11

/-- Writing the start of a literal preserves the selected cells and the head position. -/
@[spec] theorem writePrefix_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (positive head successor second : Bool)
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ prefixWord code choice positive head successor second).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writePrefix (tm := tm) zero one tick code positive head successor second
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ prefixWord code choice positive head successor second) label origin final ∧
        cost.steps ≤ elapsed + 3 * markedNumberBudget width size ⦄ := by
  let word := fun count => List.replicate count tick
  let near := ActiveChoices.leftWords tick choice
  let parts := ActiveChoices.rightWords tick choice input
  let crossed := word choice.secondState.1
  let digits := fun bit => code (.inl bit)
  let front := code (if positive then .inr 0 else .inr 1) ++ code (.inl true) ++ code (.inl head)
  let first := output ++ front
  let secondOutput := first ++
    (unaryNumberBits true (choice.time.1 + successor.toNat)).flatMap digits
  let position := if second then choice.secondPosition.1 else choice.firstPosition.1
  let written := secondOutput ++ (unaryNumberBits true position).flatMap digits
  let timeBetween := [word choice.secondPosition.2, word choice.secondPosition.1,
    word choice.firstState.2, word choice.firstState.1, word choice.firstPosition.2,
    word choice.firstPosition.1, word choice.time.2]
  let positionBefore := if second then [word choice.firstState.2, word choice.firstState.1,
      word choice.firstPosition.2, word choice.firstPosition.1,
      word choice.time.2, word choice.time.1]
    else [word choice.time.2, word choice.time.1]
  let positionBetween := if second then [word choice.secondPosition.2]
    else [word choice.secondPosition.2, word choice.secondPosition.1, word choice.firstState.2,
      word choice.firstState.1, word choice.firstPosition.2]
  let budget := markedNumberBudget width size
  have heq : output ++ prefixWord code choice positive head successor second = written := by
    simp [prefixWord, written, secondOutput, first, front, digits, position, List.append_assoc]
  have hdata : choice.size + input.length + written.length + 32 ≤ size := by
    simpa only [heq] using hsize
  have htData : choice.time.1 + regionSpan ([] : List (List Γ)) + regionSpan timeBetween +
      crossed.length + regionSpan parts + first.length ≤ size := by
    simp [timeBetween, crossed, parts, ActiveChoices.rightWords, word, regionSpan]
    dsimp [ActiveChoices.size, written, secondOutput] at hdata
    simp only [List.length_append] at hdata
    lia
  have hpData : position + regionSpan positionBefore + regionSpan positionBetween +
      crossed.length + regionSpan parts + secondOutput.length ≤ size := by
    cases second <;>
      simp [position, positionBefore, positionBetween, crossed, parts,
        ActiveChoices.rightWords, word, regionSpan]
    all_goals
      dsimp [ActiveChoices.size, written] at hdata
      simp only [List.length_append] at hdata
      lia
  have hfBound : 2 * (regionSpan parts + output.length + front.length) + 8 ≤ budget := by
    dsimp [parts, ActiveChoices.rightWords, regionSpan, budget, markedNumberBudget]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_replicate]
    dsimp [ActiveChoices.size, written, secondOutput, first] at hdata
    simp only [List.length_append] at hdata
    ring_nf
    lia
  have hpBound := appendEarlierAtMark_moves_le true width position size positionBefore
    positionBetween crossed parts secondOutput.length hpData
  have hf := appendAcross_le_spec (tm := tm) front parts output
    (StackTape.prepend crossed.reverse (counterLeft [] near)) label origin elapsed
  have ht := appendEarlierOffsetAtMark_spec (tm := tm) zero one hne tick digits width
    (fun bit => hwidth (.inl bit)) true successor choice.time.1 [] timeBetween crossed parts
    first size htData label origin (elapsed + budget)
  have hp := appendEarlierAtMark_spec (tm := tm) zero one hne tick digits width
    (fun bit => hwidth (.inl bit)) true position positionBefore positionBetween crossed parts
    secondOutput label origin (elapsed + 2 * budget)
  dsimp only [front] at hf
  dsimp only [digits] at ht hp
  cases second
  all_goals
    norm_num only [positionBefore, positionBetween, timeBetween, parts, ActiveChoices.rightWords,
      Bool.false_eq_true, ite_false, ite_true, List.length_cons, List.length_nil] at hf ht hp
    simp only [writePrefix, Bool.false_eq_true, ite_false, ite_true]
    vcgen [hf, ht, hp]
    all_goals
      simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
        ActiveChoices.rightWords, prefixWord, near, crossed, parts, digits, word,
        timeBetween, positionBefore, positionBetween,
        front, first, secondOutput, written, position, budget, List.append_assoc]
      all_goals lia


/-- Appending one fixed part of a literal preserves the selected cells and head position. -/
theorem appendPart_spec (part : List Γ) (tick : Γ) (choice : ActiveChoices)
    (input output : List Γ) (width size : Nat)
    (hsize : choice.size + input.length + (output ++ part).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      appendAcross tm part 2
    ⦃ fun _ cost final => AtPair tick choice input (output ++ part) label origin final ∧
        cost.steps ≤ elapsed + markedNumberBudget width size ⦄ := by
  have hsource := choice.source_span tick input
  have hbound : 2 * (regionSpan (choice.rightWords tick input) + output.length + part.length) +
      8 ≤ markedNumberBudget width size := by
    simp only [List.length_append] at hsize
    dsimp [markedNumberBudget]
    ring_nf
    lia
  have ha := appendAcross_le_spec (tm := tm) part (choice.rightWords tick input) output
    (StackTape.prepend (List.replicate choice.secondState.1 tick).reverse
      (counterLeft [] (choice.leftWords tick))) label origin elapsed
  norm_num only [ActiveChoices.rightWords, List.length_cons, List.length_nil] at ha
  vcgen [ha]
  all_goals
    simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.rightWords]
    all_goals lia

private def writeStateField (zero one tick : Γ) (code : Bool → List Γ) (second : Bool) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  if second then
    appendCurrentAtMark zero one tick code false 8 11
  else
    appendEarlierAtMark zero one tick code false 4 3 11

private theorem writeStateField_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (choice : ActiveChoices) (second : Bool) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + output.length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeStateField (tm := tm) zero one tick code second
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ (unaryNumberBits false
          (if second then choice.secondState.1 else choice.firstState.1)).flatMap code)
        label origin final ∧ cost.steps ≤ elapsed + markedNumberBudget width size ⦄ := by
  let word := fun count => List.replicate count tick
  let near := choice.leftWords tick
  let parts := choice.rightWords tick input
  let crossed := word choice.secondState.1
  cases second
  · let before := [word choice.firstPosition.2, word choice.firstPosition.1,
      word choice.time.2, word choice.time.1]
    let between := [word choice.secondPosition.2, word choice.secondPosition.1,
      word choice.firstState.2]
    have hdata : choice.firstState.1 + regionSpan before + regionSpan between + crossed.length +
        regionSpan parts + output.length ≤ size := by
      simp [before, between, crossed, parts, ActiveChoices.rightWords, word, regionSpan]
      dsimp [ActiveChoices.size] at hsize
      lia
    have hb := appendEarlierAtMark_moves_le false width choice.firstState.1 size before between
      crossed parts output.length hdata
    have hs := appendEarlierAtMark_spec (tm := tm) zero one hne tick code width hwidth false
      choice.firstState.1 before between crossed parts output label origin elapsed
    norm_num only [before, between, parts, ActiveChoices.rightWords,
      List.length_cons, List.length_nil] at hs
    simp only [writeStateField, Bool.false_eq_true, ite_false]
    vcgen [hs]
    all_goals
      simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
        ActiveChoices.rightWords, before, between, crossed, parts, word]
      all_goals lia
  · have hdata : choice.secondState.1 + regionSpan near + regionSpan parts + output.length ≤
        size := by
      simp [near, parts, ActiveChoices.leftWords, ActiveChoices.rightWords, regionSpan]
      dsimp [ActiveChoices.size] at hsize
      lia
    have hb := appendCurrentAtMark_moves_le false width choice.secondState.1 size near parts
      output.length hdata
    have hs := appendCurrentAtMark_spec (tm := tm) zero one hne tick code width hwidth false
      choice.secondState.1 near parts output label origin elapsed
    norm_num only [near, parts, ActiveChoices.leftWords, ActiveChoices.rightWords,
      List.length_cons, List.length_nil] at hs
    simp only [writeStateField, ite_true]
    vcgen [hs]
    all_goals
      simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.leftWords,
        ActiveChoices.rightWords, near, parts]
      all_goals lia

/-- This is a selected head variable, optionally at the following time. -/
@[expose] def headNameAtTime (choice : ActiveChoices) (successor second : Bool) : SAT.Variable :=
  Naming.bits .head (encodingNatBool.encode (choice.time.1 + successor.toNat))
    (encodingNatBool.encode (if second then choice.secondPosition.1 else choice.firstPosition.1))
    (encodingNatBool.encode (if second then choice.secondState.1 else choice.firstState.1))

/-- This is the signed head variable in the existing SAT representation. -/
@[expose] def headLiteralWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (positive successor second : Bool) : List Γ :=
  code (if positive then .inr 0 else .inr 1) ++
    (headNameAtTime choice successor second).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)

/--
This writes a signed head variable for either selected position and state, at the selected or
following time. The containing machine fixes those choices; all indices are read from the tape.
-/
def writeHeadLiteralAtTime (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (positive successor second : Bool) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writePrefix zero one tick code positive true successor second
  writeStateField zero one tick (fun bit => code (.inl bit)) second
  appendAcross tm (code (.inr 2)) 2

/-- Writing a head variable preserves every selected count and the original head position. -/
@[spec] theorem writeHeadLiteralAtTime_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (positive successor second : Bool)
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ headLiteralWord code choice positive successor second).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeHeadLiteralAtTime tm zero one tick code positive successor second
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ headLiteralWord code choice positive successor second) label origin final ∧
        cost.steps ≤ elapsed + 5 * markedNumberBudget width size ⦄ := by
  let stem := prefixWord code choice positive true successor second
  let digits := (unaryNumberBits false
    (if second then choice.secondState.1 else choice.firstState.1)).flatMap
      (fun bit => code (.inl bit))
  let first := output ++ stem
  let secondOutput := first ++ digits
  have heq : headLiteralWord code choice positive successor second =
      stem ++ digits ++ code (.inr 2) := by
    simp [headLiteralWord, headNameAtTime, prefixWord, stem, digits, Naming.bits,
      unaryNumberBits, BooleanTapeEncoding.pair, List.flatMap_append, List.append_assoc]
  have hpData : choice.size + input.length + (output ++ stem).length + 32 ≤ size := by
    simp only [heq, List.length_append] at hsize
    simp only [List.length_append]
    lia
  have hsData : choice.size + input.length + first.length + 32 ≤ size := hpData
  have hp := writePrefix_spec (tm := tm) zero one hne tick code width hwidth choice
    positive true successor second input output size hpData label origin elapsed
  have hs := writeStateField_spec (tm := tm) zero one hne tick (fun bit => code (.inl bit))
    width (fun bit => hwidth (.inl bit)) choice second input first size hsData label origin
    (elapsed + 3 * markedNumberBudget width size)
  have hb := appendPart_spec (tm := tm) (code (.inr 2)) tick choice input secondOutput width
    size (by simpa only [heq, List.append_assoc, secondOutput, first] using hsize)
    label origin (elapsed + 4 * markedNumberBudget width size)
  vcgen [writeHeadLiteralAtTime, hp, hs, hb]
  all_goals
    simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.rightWords, stem, digits,
      first, secondOutput, List.append_assoc]
    all_goals lia

variable [Encodable Γ]

/-- This is the existing name of the selected tape variable, possibly at the following time. -/
@[expose] def tapeName (choice : ActiveChoices) (successor second : Bool)
    (symbol : Option (TapeSymbol Γ)) : SAT.Variable :=
  Naming.bits .tape (encodingNatBool.encode (choice.time.1 + successor.toNat))
    (encodingNatBool.encode (if second then choice.secondPosition.1 else choice.firstPosition.1))
    (encodingNatBool.encode (Encodable.encode symbol))

/-- This is the signed tape variable in the existing SAT representation. -/
@[expose] def tapeLiteralWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (positive successor second : Bool) (symbol : Option (TapeSymbol Γ)) : List Γ :=
  code (if positive then .inr 0 else .inr 1) ++
    (tapeName choice successor second symbol).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)

/--
This writes a tape literal at the selected time or the following time. The containing machine
fixes the sign, symbol, and which position word to read; the tape gives the time and position.
The writer preserves the five selected indices and returns to the blank marking the second
selected state.
-/
def writeTapeLiteral (tm : SingleTapeTM Γ) (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (positive successor second : Bool) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writePrefix zero one tick code positive false successor second
  appendAcross tm ((encodingNatBool.encode (Encodable.encode symbol)).flatMap
    (fun bit => code (.inl bit)) ++ code (.inr 2)) 2

/-- This bounds writing a signed tape literal, including its binary time and position. -/
@[expose] def tapeLiteralTime (width size : Nat) : Nat := 4 * markedNumberBudget width size

/-- Writing a tape literal uses its existing name and preserves the selected counts and head. -/
@[spec] theorem writeTapeLiteral_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (positive successor second : Bool)
    (symbol : Option (TapeSymbol Γ)) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ tapeLiteralWord code choice positive successor second symbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeTapeLiteral tm zero one tick code positive successor second symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ tapeLiteralWord code choice positive successor second symbol)
        label origin final ∧
        cost.steps ≤ elapsed + tapeLiteralTime width size ⦄ := by
  let stem := prefixWord code choice positive false successor second
  let back := (encodingNatBool.encode (Encodable.encode symbol)).flatMap
    (fun bit => code (.inl bit)) ++ code (.inr 2)
  have heq : tapeLiteralWord code choice positive successor second symbol = stem ++ back := by
    simp [tapeLiteralWord, tapeName, stem, prefixWord, back, Naming.bits, unaryNumberBits,
      BooleanTapeEncoding.pair, List.flatMap_append, List.append_assoc]
  have hpData : choice.size + input.length + (output ++ stem).length + 32 ≤ size := by
    simp only [heq, List.length_append] at hsize
    dsimp [stem]
    simp only [List.length_append]
    lia
  have hp := writePrefix_spec (tm := tm) zero one hne tick code width hwidth choice
    positive false successor second input output size hpData label origin elapsed
  have hb := appendPart_spec (tm := tm) back tick choice input (output ++ stem) width size
    (by simpa only [heq, List.append_assoc] using hsize) label origin
    (elapsed + 3 * markedNumberBudget width size)
  dsimp only [back] at hb
  vcgen [writeTapeLiteral, hp, hb]
  all_goals
    simp_all [AtPair, pairTape, markedUnaryTape, ActiveChoices.rightWords,
      stem, back, tapeLiteralTime,
      List.append_assoc]
    all_goals lia

end Algolean.Algorithms.NPToSAT.Computation.LiteralWriting
