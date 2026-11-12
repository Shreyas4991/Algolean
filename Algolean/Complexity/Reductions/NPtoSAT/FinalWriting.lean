/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.PositionIteration
public import Algolean.Complexity.Reductions.NPToTMSAT.LiteralWriting
public import Algolean.Complexity.Reductions.NPToTMSAT.ChoiceIteration
public import Algolean.Complexity.Reductions.NPToTMSAT.Formula

/-!
# Writing the final acceptance clauses

* `writeFinalClauses` visits the last recorded time and writes the existing acceptance clauses.
  One clause requires a halted head somewhere. Two clauses at each position require the
  accepting symbol under that head and blanks everywhere else.
* `writeFinalClauses_spec` gives the exact appended SAT word and proves that every source word
  and the head position are preserved.
* `timeBound` is a cubic bound in the source and completed output lengths.

The program reads the time and width from unary words on the tape. The alphabet symbols and
accepting symbol are fixed when constructing the containing machine.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.FinalWriting

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open NPToTMSAT NPToTMSAT.HeadChoices NPToTMSAT.LiteralWriting PositionIteration
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def pairWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (positive : Bool) (symbol : Option (TapeSymbol Γ)) : List Γ :=
  headLiteralWord code choice positive false false ++
    tapeLiteralWord code choice true false false symbol ++ code (.inr 3) ++ code (.inr 4)

private def writePair (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (positive : Bool) (symbol : Option (TapeSymbol Γ)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  writeHeadLiteralAtTime tm zero one tick code positive false false
  writeTapeLiteral tm zero one tick code true false false symbol
  appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2

private theorem writePair_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (positive : Bool) (symbol : Option (TapeSymbol Γ)) (choice : ActiveChoices)
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ pairWord code choice positive symbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writePair (tm := tm) zero one tick code positive symbol
    ⦃ fun _ cost final => AtPair tick choice input (output ++ pairWord code choice positive symbol)
        label origin final ∧ cost.steps ≤ elapsed + 10 * markedNumberBudget width size ⦄ := by
  let first := output ++ headLiteralWord code choice positive false false
  let second := first ++ tapeLiteralWord code choice true false false symbol
  have hs₁ : choice.size + input.length + first.length + 32 ≤ size := by
    simp only [pairWord, first, List.length_append] at hsize ⊢
    lia
  have hs₂ : choice.size + input.length + second.length + 32 ≤ size := by
    simp only [pairWord, second, first, List.length_append] at hsize ⊢
    lia
  have hs₃ : choice.size + input.length +
      (second ++ (code (.inr 3) ++ code (.inr 4))).length + 32 ≤ size := by
    simpa only [pairWord, second, first, List.append_assoc] using hsize
  vcgen [writePair,
    writeHeadLiteralAtTime_spec (tm := tm) zero one hne tick code width hwidth choice
      positive false false input output size hs₁ label origin elapsed,
    writeTapeLiteral_spec (tm := tm) zero one hne tick code width hwidth choice true false false
      symbol input first size hs₂ label origin (elapsed + 5 * markedNumberBudget width size),
    appendPart_spec (tm := tm) (code (.inr 3) ++ code (.inr 4)) tick choice input second
      width size hs₃ label origin (elapsed + 9 * markedNumberBudget width size)]
  all_goals simp_all [pairWord, first, second, tapeLiteralTime, List.append_assoc]
  all_goals lia

private def cellWord (code : CodeSymbol → List Γ) (choice : ActiveChoices) (yes : Γ) : List Γ :=
  pairWord code choice false (some (.inl yes)) ++ pairWord code choice true none

private def writeCell (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes : Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writePair zero one tick code false (some (.inl yes))
  writePair zero one tick code true none

private theorem writeCell_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes : Γ) (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + (output ++ cellWord code choice yes).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeCell (tm := tm) zero one tick code yes
    ⦃ fun _ cost final => AtPair tick choice input (output ++ cellWord code choice yes)
        label origin final ∧ cost.steps ≤ elapsed + 20 * markedNumberBudget width size ⦄ := by
  have hs₁ : choice.size + input.length +
      (output ++ pairWord code choice false (some (.inl yes))).length + 32 ≤ size := by
    simp only [cellWord, List.length_append] at hsize ⊢
    lia
  have hs₂ : choice.size + input.length +
      (output ++ pairWord code choice false (some (.inl yes)) ++
        pairWord code choice true none).length + 32 ≤ size := by
    simpa only [cellWord, List.append_assoc] using hsize
  vcgen [writeCell,
    writePair_spec (tm := tm) zero one hne tick code width hwidth false (some (.inl yes))
      choice input output size hs₁ label origin elapsed,
    writePair_spec (tm := tm) zero one hne tick code width hwidth true none choice input
      (output ++ pairWord code choice false (some (.inl yes))) size hs₂ label origin
      (elapsed + 10 * markedNumberBudget width size)]
  all_goals simp_all [cellWord, List.append_assoc]
  all_goals lia

private def partWord (code : CodeSymbol → List Γ) (yes : Γ) (cells : Bool)
    (time position : Nat) : List Γ :=
  let choice : ActiveChoices := ⟨(time, 0), (position, 0), (0, 0), (0, 0), (0, 0)⟩
  if cells then cellWord code choice yes else headLiteralWord code choice true false false

private def writePart (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes : Γ)
    (cells : Bool) : Prog (TMQuery tm) Unit :=
  forSelectedTimePositions tm tick (if cells then writeCell zero one tick code yes
    else writeHeadLiteralAtTime tm zero one tick code true false false)

private theorem writePart_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes : Γ) (cells : Bool) (time positions states : Nat)
    (hpositions : 0 < positions) (hstates : 0 < states) (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ (List.range positions).flatMap (partWord code yes cells time)).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writePart (tm := tm) zero one tick code yes cells
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input
          (output ++ (List.range positions).flatMap (partWord code yes cells time))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positionIterationMoves size (20 * markedNumberBudget width size) ⦄ := by
  have hleaf : PositionSpec tick time 0 positions states input (partWord code yes cells time)
      label (if cells then writeCell (tm := tm) zero one tick code yes else
        writeHeadLiteralAtTime tm zero one tick code true false false)
      size (20 * markedNumberBudget width size) := by
    intro position rest hp written hcap place steps
    let choice : ActiveChoices := ⟨(time, 0), (position, rest), (0, states - 1),
      (0, positions - 1), (0, states - 1)⟩
    have he : partWord code yes cells time position =
        if cells then cellWord code choice yes else
          headLiteralWord code choice true false false := by
      cases cells <;> simp [partWord, cellWord, pairWord, headLiteralWord, tapeLiteralWord,
        headNameAtTime, tapeName, choice]
    have hdata : choice.size + input.length +
        (written ++ partWord code yes cells time position).length + 32 ≤ size := by
      dsimp [choice, ActiveChoices.size]
      lia
    cases cells with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hs := writeHeadLiteralAtTime_spec (tm := tm) zero one hne tick code width hwidth choice
        true false false input written size
        (by simpa only [he, Bool.false_eq_true, ite_false] using hdata)
        label place steps
      vcgen [hs]
      all_goals simp_all
      all_goals lia
    | true =>
      simpa only [ite_true, he] using writeCell_spec (tm := tm) zero one hne tick code width hwidth
        yes choice input written size (by simpa only [he, ite_true] using hdata) label place steps
  vcgen [writePart, forSelectedTimePositions_spec tick
    (if cells then writeCell (tm := tm) zero one tick code yes else
      writeHeadLiteralAtTime tm zero one tick code true false false)
    time 0 positions states hpositions hstates input output (partWord code yes cells time)
    label size (20 * markedNumberBudget width size) hleaf (by simpa using hsize) origin elapsed]

private def finishFirstClause (tm : SingleTapeTM Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := appendAcross tm (code (.inr 3) ++ code (.inr 4)) 6

omit [Encodable Γ] in
private theorem finishFirstClause_spec (tick : Γ) (code : CodeSymbol → List Γ)
    (time positions states : Nat) (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ (code (.inr 3) ++ code (.inr 4))).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finishFirstClause tm code
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input
          (output ++ (code (.inr 3) ++ code (.inr 4)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 4 * (size + 16) ⦄ := by
  have hs := appendAcross_le_spec (tm := tm) (code (.inr 3) ++ code (.inr 4))
    [[], List.replicate positions tick, List.replicate states tick, List.replicate positions tick,
      List.replicate states tick, input] output
    (StackTape.prepend (List.replicate time tick).reverse (counterLeft [] [])) label origin elapsed
  simp only [List.length_cons, List.length_nil] at hs
  vcgen [finishFirstClause, hs]
  all_goals simp_all [selectionTape, markedUnaryTape, regionSpan]
  all_goals lia

private def word (code : CodeSymbol → List Γ) (yes : Γ) (time positions : Nat) : List Γ :=
  (List.range positions).flatMap (partWord code yes false time) ++ code (.inr 3) ++ code (.inr 4) ++
    (List.range positions).flatMap (partWord code yes true time)

private def atLastTime (tick : Γ) (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Left
  markFirst tick action
  seekLeftEnd tm

omit [Encodable Γ] in
private theorem atLastTime_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (before : List Γ) (tail resultTail : StackTape Γ) (label : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment (StackTape.prepend before.reverse StackTape.nil) []
            (StackTape.cons none tail)⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label,
          BiTape.segment (StackTape.prepend before.reverse StackTape.nil) []
            (StackTape.cons none resultTail)⟩ ∧ final.headPos = origin ∧
          cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (before ++ [tick]) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      atLastTime (tm := tm) tick action
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (before ++ [tick]) resultTail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 * before.length + 4 ⦄ := by
  have hmove (side : StackTape Γ) :
      (BiTape.segment (StackTape.mapSome (tick :: before.reverse)) [] side).moveLeft =
        BiTape.segment (StackTape.mapSome before.reverse) [tick] side :=
    BiTape.segment_moveLeft (StackTape.mapSome before.reverse) tick [] side
  have hm := markFirst_spec (tm := tm) tick action
    (StackTape.prepend before.reverse StackTape.nil) [] tail resultTail label bound
    (by simpa using haction) (origin + before.length) (elapsed + before.length + 2)
  vcgen [atLastTime,
    seekRightBlank_le_spec (tm := tm) StackTape.nil tail (before ++ [tick]) label origin elapsed,
    hm, seekLeftEnd_le_spec (tm := tm) StackTape.nil resultTail before.reverse [tick] label
      (origin + before.length) (elapsed + before.length + 2 + bound)]
  all_goals
    simp_all [TMState.move, TMState.moveCost, List.reverse_append]
    all_goals lia

private def writeLastParts (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes : Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writePart zero one tick code yes false
  finishFirstClause tm code
  writePart zero one tick code yes true

/-- This template writes the final acceptance clauses and restores the input words and head. -/
def writeFinalClauses (tm : SingleTapeTM Γ) (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (yes : Γ) : Prog (TMQuery tm) Unit :=
  atLastTime tick (writeLastParts zero one tick code yes)

private def lastMoves (width size : Nat) : Nat :=
  2 * positionIterationMoves size (20 * markedNumberBudget width size) + 4 * (size + 16)

private theorem writeLastParts_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes : Γ) (time positions states : Nat) (hpositions : 0 < positions) (hstates : 0 < states)
    (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ word code yes time positions).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeLastParts (tm := tm) zero one tick code yes
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick [] (time, 0) [positions, states, positions, states] input
          (output ++ word code yes time positions)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + lastMoves width size ⦄ := by
  let first := output ++ (List.range positions).flatMap (partWord code yes false time)
  let second := first ++ (code (.inr 3) ++ code (.inr 4))
  have hs₁ : time + 2 * positions + 2 * states + input.length + first.length + 32 ≤ size := by
    simp only [word, first, List.length_append] at hsize ⊢
    lia
  have hs₂ : time + 2 * positions + 2 * states + input.length + second.length + 32 ≤ size := by
    simp only [word, second, first, List.length_append] at hsize ⊢
    lia
  have hs₃ : time + 2 * positions + 2 * states + input.length +
      (second ++ (List.range positions).flatMap
        (partWord code yes true time)).length + 32 ≤ size := by
    simpa only [word, second, first, List.append_assoc] using hsize
  vcgen [writeLastParts,
    writePart_spec (tm := tm) zero one hne tick code width hwidth yes false time positions states
      hpositions hstates input output size hs₁ label origin elapsed,
    finishFirstClause_spec (tm := tm) tick code time positions states input first size hs₂ label
      origin (elapsed + positionIterationMoves size (20 * markedNumberBudget width size)),
    writePart_spec (tm := tm) zero one hne tick code width hwidth yes true time positions states
      hpositions hstates input second size hs₃ label origin
      (elapsed + positionIterationMoves size (20 * markedNumberBudget width size) +
        4 * (size + 16))]
  all_goals simp_all [word, first, second, lastMoves, List.append_assoc]
  all_goals lia

private theorem writeWords_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (yes : Γ) (time positions states : Nat) (hpositions : 0 < positions) (hstates : 0 < states)
    (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ word code yes time positions).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ChoiceIteration.layout tick (time + 1) positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeFinalClauses tm zero one tick code yes
    ⦃ fun _ cost final => final.config = ⟨label,
        ChoiceIteration.layout tick (time + 1) positions states input
          (output ++ word code yes time positions)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + lastMoves width size + 2 * time + 4 ⦄ := by
  let parts := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  have hs := atLastTime_spec (tm := tm) tick (writeLastParts zero one tick code yes)
    (List.replicate time tick) (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts (StackTape.mapSome (output ++ word code yes time positions)))
    label (lastMoves width size) (by
      intro place steps
      have ha := writeLastParts_spec (tm := tm) zero one hne tick code width hwidth yes time
        positions states hpositions hstates input output size hsize label place steps
      simpa [parts, selectionTape, markedUnaryTape, counterLeft] using ha) origin elapsed
  vcgen [writeFinalClauses, hs]
  all_goals simp_all [ChoiceIteration.layout, parts, List.replicate_succ', Nat.add_assoc]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem word_eq_finalClauses (code : CodeSymbol → List Γ)
    (problem : BoundedVerification Γ) (yes : Γ) :
    word code yes problem.time (NPToTMSAT.width problem) =
      (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap code := by
  have hindices : (List.finRange (NPToTMSAT.width problem)).map Fin.val =
      List.range (NPToTMSAT.width problem) := by
    ext index
    simp
  simp only [word, ← hindices, List.flatMap_map]
  simp [Formula.finalClauses, CNF.rename, Clause.rename, Literal.rename, formulaPrefix,
    certificateEncoding_encode_eq_flatMap, literalPrefix, partWord, cellWord, pairWord,
    headLiteralWord, headNameAtTime, tapeLiteralWord, tapeName, Variable.name, Naming.bits,
    Clause.atLeastOne, Clause.implies, Clause.forbid, List.flatMap_append, List.flatMap_map,
    List.map_flatMap, List.flatMap_assoc, List.append_assoc, Function.comp_def]

/-- This cubic polynomial bounds writing all final acceptance clauses. -/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  Polynomial.C (1048576 * (width + 1)) * (Polynomial.X + 16) ^ 3

private theorem lastMoves_le (width size time : Nat) (htime : time ≤ size) :
    lastMoves width size + 2 * time + 4 ≤ (timeBound width).eval size := by
  simp only [timeBound, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
  dsimp [lastMoves, positionIterationMoves, markedNumberBudget]
  ring_nf
  lia

/--
The writer appends exactly the existing acceptance clauses. It preserves the source words and
head position, and its number of moves is bounded by the displayed cubic polynomial.
-/
@[spec] theorem writeFinalClauses_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (problem : BoundedVerification Γ) (yes : Γ) (input output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToTMSAT.width problem + 2 * (problem.verifier.states + 2) +
      input.length + (output ++
        (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap
          code).length +
          32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToTMSAT.width problem)
          (problem.verifier.states + 2) input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeFinalClauses tm zero one tick code yes
    ⦃ fun _ cost final => final.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToTMSAT.width problem)
          (problem.verifier.states + 2) input (output ++
            (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap
              code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  have hs := writeWords_spec (tm := tm) zero one hne tick code width hwidth yes problem.time
    (NPToTMSAT.width problem) (problem.verifier.states + 2) (by dsimp [NPToTMSAT.width]; lia)
    (by lia) input output size (by simpa only [word_eq_finalClauses] using hsize) label
      origin elapsed
  have ht := lastMoves_le width size problem.time (by lia)
  vcgen [hs]
  all_goals simp_all only [word_eq_finalClauses]
  all_goals lia

end Algolean.Algorithms.NPToSAT.FinalWriting
