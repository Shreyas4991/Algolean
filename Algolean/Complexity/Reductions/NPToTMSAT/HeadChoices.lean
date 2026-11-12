/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockOutput
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CellMarking
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryComparison
public import Algolean.Complexity.Reductions.NPToTMSAT.LiteralWriting
public import Algolean.Complexity.Reductions.NPToTMSAT.ChoiceIteration
public import Algolean.Complexity.Reductions.NPToTMSAT.VariableNames
public import Algolean.Complexity.Reductions.NPToTMSAT.Variables

/-!
# Writing the head and state choices

* `writeHeadChoices` reads the number of times, tape positions, and states from unary words.
  For each time, it writes one clause requiring a head position and state, followed by the
  clauses forbidding two different choices at that time.
* The tape contains two copies of each position and state bound. They allow the same fixed
  program to visit every ordered pair of choices, while reading all four indices from the tape.
* `comparePositionsOffset` compares the selected positions with a fixed offset. Offsets zero,
  one, and two test a move left, no move, and a move right, respectively.
* State index zero represents a halted machine. The remaining indices represent the running
  states, using the existing binary variable names.

These are machine templates. Alphabet symbols, output representations, and finite control
states are fixed once, independently of the bounds and indices stored on the tape.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToTMSAT.HeadChoices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the existing head-variable name for one of the two selected choices. -/
@[expose] def headName (choice : ActiveChoices) (second : Bool) : SAT.Variable :=
  Naming.bits .head (Computability.encodingNatBool.encode choice.time.1)
    (Computability.encodingNatBool.encode
      (if second then choice.secondPosition.1 else choice.firstPosition.1))
    (Computability.encodingNatBool.encode
      (if second then choice.secondState.1 else choice.firstState.1))

/-- This is one head literal, including its sign and the symbol ending its binary name. -/
@[expose] def literalWord (code : CodeSymbol → List Γ)
    (choice : ActiveChoices) (positive second : Bool) : List Γ :=
  code (if positive then .inr 0 else .inr 1) ++
    (headName choice second).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)

private def visitNext (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onFollowingWord tm (forBlocks tm tick [] action)

/--
This machine template writes a head literal at the two active choices. `second`
selects which of the two choices to write; the actual indices are read from the tape.
-/
def writeHeadLiteral (tm : SingleTapeTM Γ) (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (positive second : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  LiteralWriting.writeHeadLiteralAtTime tm zero one tick code positive false second

/-- This bounds writing one signed head literal in terms of all preserved and written words. -/
@[expose] def literalTime (width size : Nat) : Nat :=
  5 * (4096 * (width + 1) * (size + 16) ^ 2)

/--
The writer appends the selected head literal with its existing binary name. Both selected
choices, the preserved words, the control state, and the head position are unchanged.
-/
@[spec] theorem writeHeadLiteral_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (positive second : Bool) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ literalWord code choice positive second).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeHeadLiteral tm zero one tick code positive second
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ literalWord code choice positive second) label origin final ∧
        cost.steps ≤ elapsed + literalTime width size ⦄ := by
  simpa [writeHeadLiteral, literalTime, markedNumberBudget, literalWord, headName,
    LiteralWriting.headLiteralWord, LiteralWriting.headNameAtTime] using
    LiteralWriting.writeHeadLiteralAtTime_spec (tm := tm) zero one hne tick code width hwidth
      choice positive false second input output size hsize label origin elapsed

private def writePositive (zero one tick : Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onFollowingWord tm (markFirst tick
    (onFollowingWord tm (markFirst tick (writeHeadLiteral tm zero one tick code true false))))

private def positiveTape (tick : Γ) (time timeRest position positionRest control controlRest
    positions states : Nat) (input output : List Γ) : BiTape Γ :=
  markedUnaryTape [List.replicate positionRest tick, List.replicate position tick,
      List.replicate timeRest tick, List.replicate time tick] (List.replicate control tick)
    [List.replicate controlRest tick, List.replicate positions tick, List.replicate states tick,
      input] output

private def positiveWord (code : CodeSymbol → List Γ) (time position control : Nat) : List Γ :=
  code (.inr 0) ++
    (Naming.bits .head (Computability.encodingNatBool.encode time)
      (Computability.encodingNatBool.encode position)
      (Computability.encodingNatBool.encode control)).flatMap
        (fun bit => code (.inl bit)) ++ code (.inr 2)

private def positiveTime (width size : Nat) : Nat := literalTime width size + 4 * size + 12

private theorem writePositive_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest control controlRest positions states : Nat)
    (hpositions : 0 < positions) (hstates : 0 < states) (input output : List Γ) (size : Nat)
    (hsize : time + timeRest + position + positionRest + control + controlRest +
      positions + states + input.length +
        (output ++ positiveWord code time position control).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        positiveTape tick time timeRest position positionRest control controlRest positions states
          input output⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writePositive (tm := tm) zero one tick code
    ⦃ fun _ cost final => final.config = ⟨label,
        positiveTape tick time timeRest position positionRest control controlRest positions states
          input (output ++ positiveWord code time position control)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + positiveTime width size ⦄ := by
  obtain ⟨positions, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : positions ≠ 0)
  obtain ⟨states, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by lia : states ≠ 0)
  let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
    (control, controlRest), (0, positions), (0, states)⟩
  let left := StackTape.prepend (List.replicate control tick).reverse
    (counterLeft [] [List.replicate positionRest tick, List.replicate position tick,
      List.replicate timeRest tick, List.replicate time tick])
  let middle := StackTape.cons none
    (StackTape.prepend (List.replicate controlRest tick).reverse (StackTape.cons none left))
  let finalLeft := StackTape.cons none
    (StackTape.prepend (List.replicate positions tick).reverse (StackTape.cons none middle))
  let written := output ++ positiveWord code time position control
  let tail := StackTape.separateWords [input] (StackTape.mapSome output)
  let resultTail := StackTape.separateWords [input] (StackTape.mapSome written)
  have hw : literalWord code choice true false = positiveWord code time position control := by
    simp [literalWord, headName, choice, positiveWord]
  have hcap : choice.size + input.length +
      (output ++ literalWord code choice true false).length + 32 ≤ size := by
    rw [hw]
    simp only [choice, ActiveChoices.size, List.length_append] at hsize ⊢
    lia
  have hl (position : ℤ) (steps : Nat) := writeHeadLiteral_spec (tm := tm) zero one hne tick
    code width hwidth choice true false input output size hcap label position steps
  have hinner (position : ℤ) (steps : Nat) := markFirst_spec tick
    (writeHeadLiteral tm zero one tick code true false) finalLeft (List.replicate states tick)
    tail resultTail label (literalTime width size) (by
      simpa [AtPair, pairTape, ActiveChoices.leftWords, ActiveChoices.rightWords,
        markedUnaryTape, finalLeft, middle, left, choice, tail, resultTail, written, hw,
        counterLeft, StackTape.separateWords, and_assoc] using hl) position steps
  have hvisit (position : ℤ) (steps : Nat) := onFollowingWord_spec (tm := tm)
    (markFirst tick (writeHeadLiteral tm zero one tick code true false)) middle
    (List.replicate positions tick) (tick :: List.replicate states tick) tail resultTail
    label label (literalTime width size) (by simpa [finalLeft] using hinner) position steps
  have houter (position : ℤ) (steps : Nat) := markFirst_spec tick
    (onFollowingWord tm (markFirst tick (writeHeadLiteral tm zero one tick code true false)))
    middle (List.replicate positions tick)
    (StackTape.prepend (tick :: List.replicate states tick) (StackTape.cons none tail))
    (StackTape.prepend (tick :: List.replicate states tick) (StackTape.cons none resultTail)) label
    (literalTime width size + 2 * positions + 6) (by
      simpa [StackTape.separateWords, Nat.add_assoc] using hvisit) position steps
  have hr := onFollowingWord_spec (tm := tm)
    (markFirst tick (onFollowingWord tm
      (markFirst tick (writeHeadLiteral tm zero one tick code true false))))
    left (List.replicate controlRest tick) (tick :: List.replicate positions tick)
    (StackTape.prepend (tick :: List.replicate states tick) (StackTape.cons none tail))
    (StackTape.prepend (tick :: List.replicate states tick) (StackTape.cons none resultTail))
    label label (literalTime width size + 2 * positions + 6)
    (by simpa [middle] using houter) origin elapsed
  vcgen [writePositive, hr]
  all_goals
    simp_all [positiveTape, markedUnaryTape, left, written, tail, resultTail,
      StackTape.separateWords, List.replicate_succ, positiveTime]
    all_goals lia

private def positiveAt (code : CodeSymbol → List Γ) (time position states : Nat) : List Γ :=
  (List.range states).flatMap (positiveWord code time position)

private def positiveRow (code : CodeSymbol → List Γ) (time positions states : Nat) : List Γ :=
  (List.range positions).flatMap fun position => positiveAt code time position states

private theorem writePositiveAt_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest positions states : Nat)
    (hposition : position + positionRest + 1 = positions)
    (input output : List Γ) (size : Nat)
    (hsize : time + timeRest + 2 * positions + 2 * states + input.length +
      (output ++ positiveAt code time position states).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape [List.replicate timeRest tick, List.replicate time tick]
          (List.replicate position tick)
          [List.replicate positionRest tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input] output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitNext tick (writePositive (tm := tm) zero one tick code)
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape [List.replicate timeRest tick, List.replicate time tick]
          (List.replicate position tick)
          [List.replicate positionRest tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input]
          (output ++ positiveAt code time position states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          states * (positiveTime width size + 2) + 2 * positionRest + 8 ⦄ := by
  let near := [List.replicate timeRest tick, List.replicate time tick]
  let parts := [List.replicate positions tick, List.replicate states tick, input]
  have ha (index rest : Nat) (hcount : index + rest + 1 = states)
      (positionHead : ℤ) (steps : Nat) := writePositive_spec (tm := tm) zero one hne tick code
    width hwidth time timeRest position positionRest index rest positions states (by lia) (by lia)
    input (output ++ (List.range index).flatMap (positiveWord code time position)) size (by
      have hp := ((List.range_sublist.mpr (show index + 1 ≤ states by lia)).flatMap
        (positiveWord code time position)).length_le
      have hout : ((output ++ (List.range index).flatMap (positiveWord code time position)) ++
          positiveWord code time position index).length ≤
            (output ++ positiveAt code time position states).length := by
        simpa [positiveAt, List.range_succ, List.length_append, Nat.add_assoc] using
          Nat.add_le_add_left hp output.length
      lia) label positionHead steps
  have hr := onFollowingBlocks_append_spec tick (writePositive (tm := tm) zero one tick code)
    near (List.replicate position tick) positionRest states parts output
    (positiveWord code time position) label (positiveTime width size) (by
      intro index rest hcount positionHead steps
      simpa [near, parts, positiveTape, List.range_succ, List.append_assoc] using
        ha index rest hcount positionHead steps) origin elapsed
  vcgen [visitNext, hr]
  all_goals simp_all [near, parts, positiveAt]

private def positiveRowTime (width size positions states : Nat) : Nat :=
  positions * (states * (positiveTime width size + 2) + 2 * positions + 10) + 2 * size + 8

private theorem writePositiveRow_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest positions states : Nat)
    (input output : List Γ) (size : Nat)
    (hsize : time + timeRest + 2 * positions + 2 * states + input.length +
      (output ++ positiveRow code time positions states).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick)
          [List.replicate timeRest tick, List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input] output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitNext tick (visitNext tick (writePositive (tm := tm) zero one tick code))
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape [] (List.replicate time tick)
          [List.replicate timeRest tick, List.replicate positions tick, List.replicate states tick,
            List.replicate positions tick, List.replicate states tick, input]
          (output ++ positiveRow code time positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positiveRowTime width size positions states ⦄ := by
  let parts := [List.replicate states tick, List.replicate positions tick,
    List.replicate states tick, input]
  let bound := states * (positiveTime width size + 2) + 2 * positions + 8
  have ha (index rest : Nat) (hcount : index + rest + 1 = positions)
      (positionHead : ℤ) (steps : Nat) := writePositiveAt_spec (tm := tm) zero one hne tick
    code width hwidth time timeRest index rest positions states hcount input
    (output ++ (List.range index).flatMap (fun position => positiveAt code time position states))
    size (by
      have hp := ((List.range_sublist.mpr (show index + 1 ≤ positions by lia)).flatMap
        (fun position => positiveAt code time position states)).length_le
      have hout : ((output ++ (List.range index).flatMap
          (fun position => positiveAt code time position states)) ++
          positiveAt code time index states).length ≤
            (output ++ positiveRow code time positions states).length := by
        simpa [positiveRow, List.range_succ, List.length_append, Nat.add_assoc] using
          Nat.add_le_add_left hp output.length
      simpa only [List.append_assoc] using
        (show time + timeRest + 2 * positions + 2 * states + input.length +
          ((output ++ (List.range index).flatMap
            (fun position => positiveAt code time position states)) ++
              positiveAt code time index states).length + 32 ≤ size by lia))
    label positionHead steps
  have hr := onFollowingBlocks_append_spec tick
    (visitNext tick (writePositive (tm := tm) zero one tick code)) []
    (List.replicate time tick) timeRest positions parts output
    (fun position => positiveAt code time position states) label bound (by
      intro index rest hcount positionHead steps
      have hc := ha index rest hcount positionHead steps
      vcgen [hc]
      all_goals
        simp_all [parts, bound, List.range_succ, List.append_assoc]
        all_goals lia) origin elapsed
  vcgen [visitNext, hr]
  all_goals
    simp_all [parts, positiveRow, positiveRowTime, bound]
    all_goals lia

private noncomputable def compareSources (zero one tick : Γ) (different equal extra : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  equalBlocks tm zero one tick different equal extra 4 3
  ifₜ state =ₜ some equal then
    onCounter tm (equalBlocks tm zero one tick different equal extra 2 3) 1
  else
    pure ()

private noncomputable def compareChoices (zero one tick : Γ) (different equal extra : tm.State) :
    Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (compareSources zero one tick different equal extra)

private abbrev sameChoice (choice : ActiveChoices) : Prop :=
  choice.firstPosition.1 = choice.secondPosition.1 ∧ choice.firstState.1 = choice.secondState.1

/-- This quadratic expression bounds comparisons between selected unary indices. -/
@[expose] def comparisonTime (size : Nat) : Nat := 4096 * (size + 16) ^ 2

/-- This bounds a selected-position comparison with an arbitrary fixed offset. -/
@[expose] def comparisonOffsetTime (size offset : Nat) : Nat :=
  4096 * (size + offset + 15) ^ 2

/--
This template compares the first selected position plus a fixed offset with the second
selected position plus one. It records the answer in its control state and preserves the tape.
The offset is fixed with the program; both positions are read from the tape.
-/
noncomputable def comparePositionsOffset (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (different equal extra : tm.State) (offset : Nat) :
    Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm
    (onCounter tm (compareBlocksOffset tm zero one tick different equal extra offset 2 3) 1)

/-- The comparison preserves the entire tape and returns to the selected second-state cell. -/
@[spec] theorem comparePositionsOffset_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra) (offset : Nat)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + output.length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      comparePositionsOffset tm zero one tick different equal extra offset
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if choice.firstPosition.1 + offset = choice.secondPosition.1 + 1
          then equal else different))
        origin final ∧ cost.steps ≤ elapsed + comparisonOffsetTime size offset ⦄ := by
  let word := fun count => List.replicate count tick
  let before := [word choice.time.2, word choice.time.1]
  let between := [word choice.firstState.2, word choice.firstState.1, word choice.firstPosition.2]
  let atPosition := between ++ word choice.firstPosition.1 :: before
  let crossed := [word choice.secondPosition.2]
  let current := word choice.secondState.1
  let near := ActiveChoices.leftWords tick choice
  let parts := ActiveChoices.rightWords tick choice input
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let moves := compareBlocksOffsetMoves choice.firstPosition.1 choice.secondPosition.1
    (regionSpan before) (regionSpan between) offset
  let visitMoves := moves + 2 * choice.secondPosition.1 + 2 * choice.secondPosition.2 + 8
  have hframe : earlierLeft (counterLeft [] atPosition).tail
      (word choice.secondPosition.1) crossed = counterLeft [] near := by
    simp [earlierLeft_counterLeft, atPosition, before, between, crossed, near,
      ActiveChoices.leftWords, word]
  have ha (position : ℤ) (steps : Nat) := onEarlierWord_spec (tm := tm)
    (compareBlocksOffset tm zero one tick different equal extra offset 2 3)
    (counterLeft [] atPosition).tail (counterLeft [] atPosition).tail
    (word choice.secondPosition.1) crossed current tail tail label
    (some (if choice.firstPosition.1 + offset = choice.secondPosition.1 + 1
          then equal else different))
    moves (by
      intro position steps
      simpa [comparisonLeft, before, between, atPosition, counterRight, word, moves]
        using compareBlocksOffset_spec (tm := tm) zero one hne tick different equal extra
          hfirst hlast hother offset choice.firstPosition.1 choice.secondPosition.1 before between
          (counterRight crossed current tail) label position steps) position steps
  simp only [hframe] at ha
  norm_num only [crossed, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, word, List.length_replicate] at ha
  have hbound : 2 * current.length + 2 + visitMoves ≤ comparisonOffsetTime size offset := by
    have hm : moves ≤ 512 * (size + offset + 15) ^ 2 := by
      dsimp [moves, compareBlocksOffsetMoves, before, between, word]
      simp only [regionSpan_cons, regionSpan_nil, List.length_replicate]
      gcongr
      all_goals
        dsimp [ActiveChoices.size] at hsize
        lia
    dsimp [current, word, visitMoves, comparisonOffsetTime]
    simp only [List.length_replicate]
    dsimp [ActiveChoices.size] at hsize
    ring_nf at hm ⊢
    lia
  have hr := onPrefixAtMark_output_spec (tm := tm)
    (onCounter tm (compareBlocksOffset tm zero one tick different equal extra offset 2 3) 1)
    near current parts output output label
    (some (if choice.firstPosition.1 + offset = choice.secondPosition.1 + 1
          then equal else different))
    visitMoves (by simpa [tail, visitMoves, Nat.add_assoc] using ha) origin elapsed
  vcgen [comparePositionsOffset, hr]
  all_goals
    simp_all [AtPair, pairTape, near, parts, current, word]
    all_goals lia
/--
This template compares the two selected head positions and records equality in its control
state. Both positions are read from the tape; the program is fixed for all input lengths.
-/
noncomputable def comparePositions (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (different equal extra : tm.State) : Prog (TMQuery tm) Unit :=
  comparePositionsOffset tm zero one tick different equal extra 1

/-- The comparison preserves the entire tape and returns to the selected second-state cell. -/
@[spec] theorem comparePositions_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + output.length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      comparePositions tm zero one tick different equal extra
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if choice.firstPosition.1 = choice.secondPosition.1 then equal else different))
        origin final ∧ cost.steps ≤ elapsed + comparisonTime size ⦄ := by
  simpa [comparePositions, comparisonOffsetTime, comparisonTime, Nat.add_assoc] using
    comparePositionsOffset_spec (tm := tm) zero one hne tick different equal extra
      hfirst hlast hother 1 choice input output size hsize label origin elapsed

private theorem compareChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + output.length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      compareChoices (tm := tm) zero one tick different equal extra
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if sameChoice choice then equal else different)) origin final ∧
        cost.steps ≤ elapsed + comparisonTime size ⦄ := by
  let word := fun count => List.replicate count tick
  let near := ActiveChoices.leftWords tick choice
  let parts := ActiveChoices.rightWords tick choice input
  let current := word choice.secondState.1
  let beforeState := [word choice.firstPosition.2, word choice.firstPosition.1,
    word choice.time.2, word choice.time.1]
  let betweenState := [word choice.secondPosition.2, word choice.secondPosition.1,
    word choice.firstState.2]
  let beforePosition := [word choice.time.2, word choice.time.1]
  let betweenPosition := [word choice.firstState.2, word choice.firstState.1,
    word choice.firstPosition.2]
  let positionNear := [word choice.firstState.2, word choice.firstState.1,
    word choice.firstPosition.2, word choice.firstPosition.1,
    word choice.time.2, word choice.time.1]
  let positionParts := [word choice.secondPosition.2]
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let stateMoves := equalBlocksMoves choice.firstState.1 choice.secondState.1
    (regionSpan beforeState) (regionSpan betweenState)
  let positionMoves := equalBlocksMoves choice.firstPosition.1 choice.secondPosition.1
    (regionSpan beforePosition) (regionSpan betweenPosition)
  let visitMoves := positionMoves + 2 * choice.secondPosition.1 +
    2 * (positionParts.map List.length).sum + 4 * positionParts.length + 4
  have hstateFrame : comparisonLeft zero one tick 0 choice.firstState.1
      beforeState betweenState = counterLeft [] near := by
    simp [comparisonLeft, beforeState, betweenState, near, ActiveChoices.leftWords, word]
  have hpositionFrame : earlierLeft (counterLeft [] positionNear).tail
      (word choice.secondPosition.1) positionParts = counterLeft [] near := by
    simp [earlierLeft_counterLeft, positionNear, positionParts, near, ActiveChoices.leftWords, word]
  have hs (position : ℤ) (steps : Nat) := equalBlocks_spec (tm := tm) zero one hne tick
    different equal extra hfirst hlast hother choice.firstState.1 choice.secondState.1
    beforeState betweenState tail label position steps
  simp only [hstateFrame] at hs
  norm_num only [beforeState, betweenState, List.length_cons, List.length_nil] at hs
  have hp (position : ℤ) (steps : Nat) := onEarlierWord_spec (tm := tm)
    (equalBlocks tm zero one tick different equal extra 2 3)
    (counterLeft [] positionNear).tail (counterLeft [] positionNear).tail
    (word choice.secondPosition.1) positionParts current tail tail (some equal)
    (some (if choice.firstPosition.1 = choice.secondPosition.1 then equal else different))
    positionMoves (by
      intro position steps
      simpa [positionMoves, beforePosition, betweenPosition, positionNear, positionParts,
        comparisonLeft, word, current, counterRight, counterLeft,
        StackTape.separateWords_append] using
        equalBlocks_spec (tm := tm) zero one hne tick different equal extra hfirst hlast hother
          choice.firstPosition.1 choice.secondPosition.1 beforePosition betweenPosition
          (counterRight positionParts current tail) (some equal) position steps)
    position steps
  simp only [hpositionFrame] at hp
  norm_num only [positionParts, List.length_cons, List.length_nil] at hp
  have hwork : 2 * current.length + 2 + stateMoves + visitMoves ≤ comparisonTime size := by
    have hsBound : stateMoves ≤ 512 * (size + 16) ^ 2 := by
      dsimp [stateMoves, equalBlocksMoves, regionSpan, beforeState, betweenState, word]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_replicate]
      gcongr
      all_goals
        dsimp [ActiveChoices.size] at hsize
        lia
    have hpBound : positionMoves ≤ 512 * (size + 16) ^ 2 := by
      dsimp [positionMoves, equalBlocksMoves, regionSpan, beforePosition, betweenPosition, word]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_replicate]
      gcongr
      all_goals
        dsimp [ActiveChoices.size] at hsize
        lia
    dsimp [visitMoves, current, word, positionParts, comparisonTime]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_replicate]
    dsimp [ActiveChoices.size] at hsize
    ring_nf at hsBound hpBound ⊢
    lia
  have hi (position : ℤ) (steps : Nat) :
      ⦃ fun cost currentState => currentState.config = ⟨label,
          BiTape.segment (counterLeft [] near) current tail⟩ ∧
          currentState.headPos = position ∧ cost.steps ≤ steps ⦄
        compareSources (tm := tm) zero one tick different equal extra
      ⦃ fun _ cost final => final.config =
          ⟨some (if sameChoice choice then equal else different),
            BiTape.segment (counterLeft [] near) current tail⟩ ∧
          final.headPos = position ∧ cost.steps ≤ steps + stateMoves + visitMoves ⦄ := by
    by_cases hstates : choice.firstState.1 = choice.secondState.1
    · vcgen [compareSources, hs position steps, Spec.branch_true_spec]
      case vc1 => simp_all [current, word]
      case vc2 =>
        refine ⟨by simp_all, ?_⟩
        vcgen [hp position (steps + stateMoves)]
        all_goals
          simp_all [current, word, stateMoves, visitMoves, positionParts,
            beforeState, betweenState]
          all_goals lia
    · vcgen [compareSources, hs position steps, Spec.branch_false_spec]
      case vc1 => simp_all [current, word]
      case vc2 =>
        refine ⟨by simp_all, ?_⟩
        vcgen
        all_goals
          simp_all [current, word, stateMoves, visitMoves, positionParts,
            beforeState, betweenState]
          all_goals lia
  have hr := onPrefixAtMark_output_spec (tm := tm)
    (compareSources zero one tick different equal extra) near current parts output output
    label (some (if sameChoice choice then equal else different)) (stateMoves + visitMoves)
    (by simpa only [tail, Nat.add_assoc] using hi) origin elapsed
  vcgen [compareChoices, hr]
  all_goals
    simp_all [AtPair, pairTape, near, parts, current, word]
    all_goals lia

private noncomputable def writePair (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (different equal extra : tm.State) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  compareChoices zero one tick different equal extra
  ifₜ state =ₜ some different then
    writeHeadLiteral tm zero one tick code false false
    writeHeadLiteral tm zero one tick code false true
    appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2
  else
    pure ()
  state ←ₜ different

/--
Appending a fixed word preserves both selected choices and restores the head. The same bound
used for one head literal also bounds this append when the complete written word fits `size`.
-/
theorem appendAtPair_spec (word : List Γ) (tick : Γ) (choice : ActiveChoices)
    (input output : List Γ) (width size : Nat)
    (hsize : choice.size + input.length + (output ++ word).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      appendAcross tm word 2
    ⦃ fun _ cost final => AtPair tick choice input (output ++ word) label origin final ∧
        cost.steps ≤ elapsed + literalTime width size ⦄ := by
  have ha := LiteralWriting.appendPart_spec (tm := tm) word tick choice input output width size
    hsize label origin elapsed
  vcgen [ha]
  all_goals simp_all [literalTime, markedNumberBudget]
  all_goals lia

private def pairWord (code : CodeSymbol → List Γ) (choice : ActiveChoices) : List Γ :=
  if sameChoice choice then [] else
    literalWord code choice false false ++ literalWord code choice false true ++
      code (.inr 3) ++ code (.inr 4)

private def pairTime (width size : Nat) : Nat := comparisonTime size + 3 * literalTime width size

private theorem writePair_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + (output ++ pairWord code choice).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some different) origin current ∧
        cost.steps ≤ elapsed ⦄
      writePair (tm := tm) zero one tick code different equal extra
    ⦃ fun _ cost final => AtPair tick choice input (output ++ pairWord code choice)
        (some different) origin final ∧ cost.steps ≤ elapsed + pairTime width size ⦄ := by
  have hstart : choice.size + input.length + output.length + 32 ≤ size := by
    simp only [List.length_append] at hsize
    lia
  have hc := compareChoices_spec (tm := tm) zero one hne tick different equal extra
    hfirst hlast hother choice input output size hstart (some different) origin elapsed
  by_cases heq : sameChoice choice
  · vcgen [writePair, hc, Spec.branch_false_spec]
    refine ⟨by simp_all [AtPair, ne_comm], ?_⟩
    vcgen
    simp_all [AtPair, pairWord, pairTime, sameChoice]
    lia
  · let first := output ++ literalWord code choice false false
    let second := first ++ literalWord code choice false true
    let ending := code (.inr 3) ++ code (.inr 4)
    let start := elapsed + comparisonTime size
    let middle := start + literalTime width size
    let later := middle + literalTime width size
    have hdata : choice.size + input.length + second.length + ending.length + 32 ≤ size := by
      simpa [pairWord, heq, second, first, ending, List.length_append, Nat.add_assoc] using hsize
    have hf := writeHeadLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
      false false input output size (by
        dsimp [second, first] at hdata
        simp only [List.length_append] at hdata ⊢
        lia) (some different) origin start
    have hs := writeHeadLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
      false true input first size (by
        simpa only [second, List.length_append] using (show choice.size + input.length +
          second.length + 32 ≤ size by lia)) (some different) origin middle
    have he := appendAtPair_spec (tm := tm) ending tick choice input second width size
      (by simpa only [List.length_append, Nat.add_assoc] using hdata) (some different) origin later
    dsimp only [ending] at he
    vcgen [writePair, hc, Spec.branch_true_spec]
    refine ⟨by simp_all [AtPair], ?_⟩
    vcgen [hf, hs, he]
    all_goals
      simp_all [AtPair, pairWord, pairTime, sameChoice, first, second, ending,
        start, middle, later, List.append_assoc]
      all_goals lia

private def pairAt (code : CodeSymbol → List Γ)
    (time position control otherPosition otherControl : Nat) : List Γ :=
  pairWord code ⟨(time, 0), (position, 0), (control, 0),
    (otherPosition, 0), (otherControl, 0)⟩

private def timeTape (tick : Γ) (time timeRest positions states : Nat)
    (input output : List Γ) : BiTape Γ :=
  markedUnaryTape [] (List.replicate time tick)
    [List.replicate timeRest tick, List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input] output

private theorem writeNegativeRow_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (times time timeRest positions states : Nat) (htime : time + timeRest + 1 = times)
    (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ ChoiceIteration.rowWord (pairAt code) time positions states).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some different,
        timeTape tick time timeRest positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      ChoiceIteration.forRemainingChoices tm tick
        (writePair zero one tick code different equal extra)
    ⦃ fun _ cost final => final.config = ⟨some different,
        timeTape tick time timeRest positions states input
          (output ++ ChoiceIteration.rowWord (pairAt code) time positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          ChoiceIteration.nestedMoves size (pairTime width size) 4 ⦄ := by
  have hleaf : ChoiceIteration.LeafSpec tick times positions states input (pairAt code)
      (some different) (writePair zero one tick code different equal extra)
      size (pairTime width size) := by
    intro time timeRest position positionRest control controlRest otherPosition otherPositionRest
      otherControl otherControlRest htime hposition hcontrol hotherPosition hotherControl
      output hsize origin elapsed
    let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
      (control, controlRest), (otherPosition, otherPositionRest), (otherControl, otherControlRest)⟩
    have hword : pairWord code choice = pairAt code time position control
        otherPosition otherControl := rfl
    have hcap : choice.size + input.length + (output ++ pairWord code choice).length + 32 ≤
        size := by
      rw [hword]
      dsimp [choice, ActiveChoices.size]
      lia
    simpa [AtPair, pairTape, ActiveChoices.leftWords, ActiveChoices.rightWords, choice,
      hword, and_assoc] using writePair_spec (tm := tm) zero one hne tick code width hwidth
        different equal extra hfirst hlast hother choice input output size hcap origin elapsed
  vcgen [ChoiceIteration.forRemainingChoices_spec tick
    (writePair (tm := tm) zero one tick code different equal extra) times positions states
    input output (pairAt code) (some different) size (pairTime width size) hleaf
    time timeRest htime hsize origin elapsed]
  all_goals simp_all [timeTape]

private theorem appendAtTime_spec (word : List Γ) (tick : Γ)
    (time timeRest positions states : Nat) (input output : List Γ) (width size : Nat)
    (hsize : time + timeRest + 2 * positions + 2 * states + input.length +
      (output ++ word).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        timeTape tick time timeRest positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendAcross tm word 6
    ⦃ fun _ cost final => final.config = ⟨label,
        timeTape tick time timeRest positions states input (output ++ word)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + literalTime width size ⦄ := by
  let parts := [List.replicate timeRest tick, List.replicate positions tick,
    List.replicate states tick, List.replicate positions tick, List.replicate states tick, input]
  have hbound : 2 * (regionSpan parts + output.length + word.length) + 8 ≤
      literalTime width size := by
    simp only [parts, regionSpan_cons, regionSpan_nil, List.length_replicate] at hsize ⊢
    simp only [List.length_append] at hsize
    dsimp [literalTime]
    ring_nf
    lia
  have ha := appendAcross_le_spec (tm := tm) word parts output
    (StackTape.prepend (List.replicate time tick).reverse (counterLeft [] []))
    label origin elapsed
  norm_num only [parts, List.length_cons, List.length_nil] at ha
  vcgen [ha]
  all_goals
    simp_all [timeTape, markedUnaryTape, parts]
    all_goals lia

private def rowParts (code : CodeSymbol → List Γ) (time positions states : Nat) : List Γ :=
  positiveRow code time positions states ++ code (.inr 3) ++ code (.inr 4) ++
    ChoiceIteration.rowWord (pairAt code) time positions states

private def rowTime (width size positions states : Nat) : Nat :=
  positiveRowTime width size positions states + literalTime width size +
    ChoiceIteration.nestedMoves size (pairTime width size) 4

private noncomputable def writeTime (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (different equal extra : tm.State) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  visitNext tick (visitNext tick (writePositive zero one tick code))
  appendAcross tm (code (.inr 3) ++ code (.inr 4)) 6
  ChoiceIteration.forRemainingChoices tm tick (writePair zero one tick code different equal extra)

private theorem writeTime_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (times time timeRest positions states : Nat) (htime : time + timeRest + 1 = times)
    (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ rowParts code time positions states).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some different,
        timeTape tick time timeRest positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeTime (tm := tm) zero one tick code different equal extra
    ⦃ fun _ cost final => final.config = ⟨some different,
        timeTape tick time timeRest positions states input
          (output ++ rowParts code time positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + rowTime width size positions states ⦄ := by
  let first := output ++ positiveRow code time positions states
  let ending := code (.inr 3) ++ code (.inr 4)
  let second := first ++ ending
  let positiveMoves := positiveRowTime width size positions states
  let appendMoves := literalTime width size
  have hp := writePositiveRow_spec (tm := tm) zero one hne tick code width hwidth
    time timeRest positions states input output size (by
      simp only [rowParts, List.length_append] at hsize ⊢
      lia) (some different) origin elapsed
  have he := appendAtTime_spec (tm := tm) ending tick time timeRest positions states
    input first width size (by
      simp only [rowParts, first, ending, List.length_append] at hsize ⊢
      lia) (some different) origin (elapsed + positiveMoves)
  dsimp only [ending] at he
  have hn := writeNegativeRow_spec (tm := tm) zero one hne tick code width hwidth different
    equal extra hfirst hlast hother times time timeRest positions states htime input second size
    (by simpa [rowParts, second, first, ending, List.append_assoc] using hsize)
    origin (elapsed + positiveMoves + appendMoves)
  vcgen [writeTime, hp, he, hn]
  all_goals
    simp_all [timeTape, rowParts, rowTime, first, second, ending, positiveMoves, appendMoves,
      List.append_assoc]
    all_goals lia

/-- This is the encoded head-choice clause prefix, with the times in increasing order. -/
def word (code : CodeSymbol → List Γ) (times positions states : Nat) : List Γ :=
  (List.range times).flatMap fun time => rowParts code time positions states

/-- This states the five unary bounds, preserved words, control state, and head position. -/
@[expose] def AtInput (tick : Γ) (times positions states : Nat) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, ChoiceIteration.layout tick times positions states input output⟩ ∧
    current.headPos = origin

/--
This polynomial bounds the complete head-choice writer in the total source and output size.
It includes both the clause requiring a choice and the clauses excluding different choices.
-/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  let x : Polynomial Nat := Polynomial.X
  let literal := Polynomial.C (5 * 4096 * (width + 1)) * (x + 16) ^ 2
  let comparison := Polynomial.C 4096 * (x + 16) ^ 2
  let pairs := comparison + 3 * literal
  let nested := ChoiceIteration.nestedPolynomial pairs 4
  let positive := x * (x * (literal + 4 * x + 12 + 2) + 2 * x + 10) + 2 * x + 8
  x * (positive + literal + nested + 2) + 2

private theorem timeBound_eval (width size : Nat) :
    (timeBound width).eval size = size *
      (rowTime width size size size + 2) + 2 := by
  simp only [timeBound, rowTime, positiveRowTime, positiveTime, literalTime, pairTime,
    comparisonTime, ChoiceIteration.eval_nestedPolynomial, ChoiceIteration.nestedMoves,
    selectionMoves,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  ring

/--
This machine template writes the head-choice clauses at every recorded time. Its tape words
are the time bound, two copies of the position and state bounds, the preserved input, and
output. The head begins and ends at the first time cell. Every index is read from the tape.
-/
noncomputable def writeHeadChoices (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (different equal extra : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ different
  forBlocks tm tick [] (writeTime zero one tick code different equal extra)

/--
The fixed program writes every head-choice clause in order. It preserves all source words and
returns the head to the first time cell. One polynomial bounds every source and output size.
-/
@[spec] theorem writeHeadChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (times positions states : Nat) (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ word code times positions states).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick times positions states input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeHeadChoices tm zero one tick code different equal extra
    ⦃ fun _ cost final => AtInput tick times positions states input
        (output ++ word code times positions states) (some different) origin final ∧
        cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  let parts := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  have ha (index rest : Nat) (hcount : index + rest + 1 = times)
      (positionHead : ℤ) (steps : Nat) := writeTime_spec (tm := tm) zero one hne tick code
    width hwidth different equal extra hfirst hlast hother times index rest positions states
    hcount input (output ++ (List.range index).flatMap
      (fun time => rowParts code time positions states)) size (by
      have hp := ((List.range_sublist.mpr (show index + 1 ≤ times by lia)).flatMap
        (fun time => rowParts code time positions states)).length_le
      have hout : ((output ++ (List.range index).flatMap
          (fun time => rowParts code time positions states)) ++
          rowParts code index positions states).length ≤
            (output ++ word code times positions states).length := by
        simpa [word, List.range_succ, List.length_append, Nat.add_assoc] using
          Nat.add_le_add_left hp output.length
      simpa only [List.append_assoc] using
        (show times + 2 * positions + 2 * states + input.length +
          ((output ++ (List.range index).flatMap
            (fun time => rowParts code time positions states)) ++
              rowParts code index positions states).length + 32 ≤ size by lia)) positionHead steps
  have hr := forBlocks_append_spec tick
    (writeTime (tm := tm) zero one tick code different equal extra) times [] parts output
    (fun time => rowParts code time positions states) (some different)
    (rowTime width size positions states) (by
      intro index rest hcount positionHead steps
      simpa [timeTape, parts, List.range_succ, List.append_assoc] using
        ha index rest hcount positionHead steps) origin elapsed
  have hwork : times * (rowTime width size positions states + 2) + 2 ≤
      (timeBound width).eval size := by
    rw [timeBound_eval]
    dsimp [rowTime, positiveRowTime]
    gcongr <;> lia
  vcgen [writeHeadChoices, hr]
  all_goals
    simp_all [AtInput, ChoiceIteration.layout, parts, word, counterLeft]
    all_goals lia

private def numericName (time : Nat) (control : Nat × Nat) : SAT.Variable :=
  Naming.bits .head (Computability.encodingNatBool.encode time)
    (Computability.encodingNatBool.encode control.1)
    (Computability.encodingNatBool.encode control.2)

private def numericChoices (positions states : Nat) : List (Nat × Nat) :=
  (List.range positions).flatMap fun position =>
    (List.range states).map fun control => (position, control)

private def rowFormula (time positions states : Nat) : CNF SAT.Variable :=
  (CNF.exactlyOne (numericChoices positions states)).rename (numericName time)

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem positiveNames_word (code : CodeSymbol → List Γ) (time : Nat)
    (names : List (Nat × Nat)) :
    (certificateEncoding.encode
      (names.map (fun name => Literal.pos (numericName time name)))).flatMap code =
      names.flatMap (fun name => positiveWord code time name.1 name.2) ++ code (.inr 3) := by
  induction names with
  | nil => simp [certificateEncoding_encode_nil]
  | cons first rest ih =>
    simp_all [certificateEncoding_encode_pos, positiveWord, numericName,
      List.flatMap_append, List.flatMap_map, List.append_assoc]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem pairAt_encode (code : CodeSymbol → List Γ) (time : Nat)
    (first second : Nat × Nat) :
    pairAt code time first.1 first.2 second.1 second.2 =
      if second = first then [] else
        ((certificateEncoding.encode [.neg (numericName time first),
          .neg (numericName time second)]) ++ [(.inr 4 : CodeSymbol)]).flatMap code := by
  by_cases heq : second = first
  · subst second
    simp [pairAt, pairWord, sameChoice]
  · have hcoords : ¬(first.1 = second.1 ∧ first.2 = second.2) := by
      intro h
      exact heq (Prod.ext h.1 h.2).symm
    simp [pairAt, pairWord, sameChoice, hcoords, heq, literalWord, headName, numericName,
      certificateEncoding_encode_neg, certificateEncoding_encode_nil,
      List.flatMap_append, List.flatMap_map, List.append_assoc]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem negativeNames_word (code : CodeSymbol → List Γ) (time : Nat)
    (first : Nat × Nat) (names : List (Nat × Nat)) :
    ((names.filter (fun second => !decide (second = first))).flatMap fun second =>
      (certificateEncoding.encode [.neg (numericName time first),
        .neg (numericName time second)]).flatMap code ++ code (.inr 4)) =
      names.flatMap (fun second => pairAt code time first.1 first.2 second.1 second.2) := by
  induction names with
  | nil => rfl
  | cons second rest ih =>
    by_cases heq : second = first <;> simp_all [pairAt_encode]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem exactlyOne_names_word (code : CodeSymbol → List Γ) (time : Nat)
    (names : List (Nat × Nat)) :
    (formulaPrefix ((CNF.exactlyOne names).rename (numericName time))).flatMap code =
      names.flatMap (fun name => positiveWord code time name.1 name.2) ++ code (.inr 3) ++
        code (.inr 4) ++ names.flatMap (fun first =>
          names.flatMap (fun second => pairAt code time first.1 first.2 second.1 second.2)) := by
  simp [CNF.exactlyOne, CNF.atMostOne, Clause.atLeastOne, Clause.forbid,
    CNF.rename, Clause.rename, Literal.rename, Function.comp_def, formulaPrefix, List.map_flatMap,
    List.map_map, List.flatMap_assoc, List.flatMap_map, List.flatMap_append,
    positiveNames_word, negativeNames_word, List.append_assoc]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem rowParts_eq_formula (code : CodeSymbol → List Γ) (time positions states : Nat) :
    rowParts code time positions states = (formulaPrefix (rowFormula time positions states)).flatMap
      code := by
  rw [rowFormula, exactlyOne_names_word]
  simp [rowParts, numericChoices, positiveRow, positiveAt, ChoiceIteration.rowWord,
    List.flatMap_assoc, List.flatMap_map]

omit [Inhabited Γ] [Fintype Γ] in
/-- The writer's word is exactly the existing head-choice clauses with their existing names. -/
theorem word_eq_headClauses [Encodable Γ] (code : CodeSymbol → List Γ)
    (problem : BoundedVerification Γ) :
    word code (problem.time + 1) (NPToTMSAT.width problem) (problem.verifier.states + 2) =
      (formulaPrefix ((headClauses problem).rename Variable.name)).flatMap code := by
  let controlCode := fun control : Fin (NPToTMSAT.width problem) ×
      Option (Fin (problem.verifier.states + 1)) => (control.1.val, Encodable.encode control.2)
  have hchoices : numericChoices (NPToTMSAT.width problem) (problem.verifier.states + 2) =
      (controlChoices problem).map controlCode := (controlChoices_codes problem).symm
  have hmap (time : Fin (problem.time + 1)) :
      (CNF.exactlyOne ((controlChoices problem).map (Variable.head time))).rename Variable.name =
        rowFormula time.val (NPToTMSAT.width problem) (problem.verifier.states + 2) := by
    rw [← CNF.rename_exactlyOne (Variable.head time) (by intro first second h; cases h; rfl)]
    rw [rowFormula, hchoices,
      ← CNF.rename_exactlyOne controlCode (controlCode_injective problem)]
    simp only [CNF.rename, Clause.rename, List.map_map, Function.comp_def]
    congr 1
    funext clause
    congr 1
    funext literal
    cases literal <;> simp [Literal.rename, numericName, controlCode,
      Naming.bits_head_eq_name]
  have hformula : (headClauses problem).rename Variable.name =
      (List.finRange (problem.time + 1)).flatMap (fun time =>
        rowFormula time.val (NPToTMSAT.width problem) (problem.verifier.states + 2)) := by
    simp only [headClauses, CNF.rename, List.map_flatMap]
    congr 1
    funext time
    exact hmap time
  have htimes : (List.finRange (problem.time + 1)).map Fin.val =
      List.range (problem.time + 1) := by ext i; simp
  rw [hformula]
  simp only [word, rowParts_eq_formula]
  have hrange := congrArg (List.flatMap (fun time =>
    (formulaPrefix (rowFormula time (NPToTMSAT.width problem)
      (problem.verifier.states + 2))).flatMap code)) htimes
  simpa only [List.flatMap_map, Function.comp_def, formulaPrefix, List.flatMap_assoc] using
    hrange.symm

/--
The fixed program writes the head-choice clauses for the specified bounded computation.
The bounds occur only in this statement; the program reads them from the tape.
-/
theorem writeHeadClauses_spec [Encodable Γ]
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (problem : BoundedVerification Γ) (input output : List Γ) (size : Nat)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let times := problem.time + 1
    let positions := NPToTMSAT.width problem
    let states := problem.verifier.states + 2
    let written := (formulaPrefix ((headClauses problem).rename Variable.name)).flatMap code
    times + 2 * positions + 2 * states + input.length + (output ++ written).length + 32 ≤ size →
    ⦃ fun cost current => AtInput tick times positions states input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeHeadChoices tm zero one tick code different equal extra
    ⦃ fun _ cost final => AtInput tick times positions states input (output ++ written)
        (some different) origin final ∧ cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  dsimp only
  intro hsize
  simpa only [word_eq_headClauses] using writeHeadChoices_spec (tm := tm) zero one hne tick
    code width hwidth different equal extra hfirst hlast hother (problem.time + 1)
    (NPToTMSAT.width problem) (problem.verifier.states + 2) input output size
    (by simpa only [word_eq_headClauses] using hsize) label origin elapsed


end Algolean.Algorithms.NPToTMSAT.HeadChoices
