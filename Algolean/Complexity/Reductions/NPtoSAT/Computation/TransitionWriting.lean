/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.LiteralWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.HeadChoices
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.TransitionClauses
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.ChoiceIteration
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CellMarking

/-!
# Writing the requirements for verifier transitions

* `writeTapeUpdateClause` writes the requirement that a selected cell has its specified next
  symbol when the selected head position and old cell symbol hold.
* Its specification uses the existing implication clause and SAT encoding. It preserves the
  input, selected indices, and head position and gives a quadratic bound on head moves.
* `writeUnchangedClauses` repeats these requirements for every transition, head position,
  state, and different tape cell. It restores the unary bounds and the original head position.

The containing program includes these templates for the finitely many symbol choices of its
fixed alphabet. It chooses between them by reading the verifier description. The indices and
bounds are read from the tape, rather than chosen when constructing the program.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Computation.TransitionWriting

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open HeadChoices LiteralWriting
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the existing encoded implication for the old and next symbols of a selected cell. -/
@[expose] def tapeUpdateWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (second : Bool) (oldSymbol newSymbol : Option (TapeSymbol Γ)) : List Γ :=
  (formulaPrefix [Clause.implies
    [headName choice false, tapeName choice false second oldSymbol]
    (tapeName choice true second newSymbol)]).flatMap code

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem tapeUpdateWord_eq (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (second : Bool) (oldSymbol newSymbol : Option (TapeSymbol Γ)) :
    tapeUpdateWord code choice second oldSymbol newSymbol =
      literalWord code choice false false ++
      tapeLiteralWord code choice false false second oldSymbol ++
      tapeLiteralWord code choice true true second newSymbol ++ code (.inr 3) ++ code (.inr 4) := by
  simp [tapeUpdateWord, formulaPrefix, Clause.implies, Clause.forbid,
    certificateEncoding_encode_neg, certificateEncoding_encode_pos,
    certificateEncoding_encode_nil, literalWord, tapeLiteralWord,
    List.flatMap_append, List.flatMap_map, List.append_assoc]

/--
This writes the clause requiring the selected cell's next symbol when the current head and
old symbol are as selected. Its two symbols and choice of position word are fixed with the
containing machine. The time, position, and state indices are read from the tape.
-/
def writeTapeUpdateClause (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (second : Bool)
    (oldSymbol newSymbol : Option (TapeSymbol Γ)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  writeHeadLiteral tm zero one tick code false false
  writeTapeLiteral tm zero one tick code false false second oldSymbol
  writeTapeLiteral tm zero one tick code true true second newSymbol
  appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2

/-- This bounds writing the three literals and the two symbols that finish their clause. -/
@[expose] def tapeUpdateTime (width size : Nat) : Nat :=
  2 * literalTime width size + 2 * tapeLiteralTime width size

/-- Writing a cell-update requirement appends exactly the existing SAT clause. -/
@[spec] theorem writeTapeUpdateClause_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (second : Bool) (oldSymbol newSymbol : Option (TapeSymbol Γ))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ tapeUpdateWord code choice second oldSymbol newSymbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeTapeUpdateClause tm zero one tick code second oldSymbol newSymbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ tapeUpdateWord code choice second oldSymbol newSymbol) label origin final ∧
        cost.steps ≤ elapsed + tapeUpdateTime width size ⦄ := by
  let first := output ++ literalWord code choice false false
  let secondOutput := first ++ tapeLiteralWord code choice false false second oldSymbol
  let third := secondOutput ++ tapeLiteralWord code choice true true second newSymbol
  let ending := code (.inr 3) ++ code (.inr 4)
  have hdata : choice.size + input.length + (third ++ ending).length + 32 ≤ size := by
    simpa only [tapeUpdateWord_eq, third, secondOutput, first, ending,
      List.length_append, Nat.add_assoc] using hsize
  have hfirst : choice.size + input.length + first.length + 32 ≤ size := by
    simp only [List.length_append, third, secondOutput] at hdata
    lia
  have hsecond : choice.size + input.length + secondOutput.length + 32 ≤ size := by
    simp only [List.length_append, third] at hdata
    lia
  have hthird : choice.size + input.length + third.length + 32 ≤ size := by
    simp only [List.length_append] at hdata
    lia
  have hf := writeHeadLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
    false false input output size hfirst label origin elapsed
  have hs := writeTapeLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
    false false second oldSymbol input first size hsecond label origin
    (elapsed + literalTime width size)
  have ht := writeTapeLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
    true true second newSymbol input secondOutput size hthird label origin
    (elapsed + literalTime width size + tapeLiteralTime width size)
  have he := appendAtPair_spec (tm := tm) ending tick choice input third width size
    hdata label origin (elapsed + literalTime width size + 2 * tapeLiteralTime width size)
  dsimp only [ending] at he
  vcgen [writeTapeUpdateClause, hf, hs, ht, he]
  all_goals simp_all [tapeUpdateWord_eq, first, secondOutput, third, ending,
    tapeUpdateTime, List.append_assoc]
  all_goals lia

private def writeUnchangedSymbols (zero one tick : Γ) (code : CodeSymbol → List Γ) :
    List (Option (TapeSymbol Γ)) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: rest => do [TMQuery tm]
    writeTapeUpdateClause tm zero one tick code true symbol symbol
    writeUnchangedSymbols zero one tick code rest

private def unchangedSymbolsWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbols : List (Option (TapeSymbol Γ))) : List Γ :=
  symbols.flatMap fun symbol => tapeUpdateWord code choice true symbol symbol

private theorem writeUnchangedSymbols_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (symbols : List (Option (TapeSymbol Γ)))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ unchangedSymbolsWord code choice symbols).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeUnchangedSymbols (tm := tm) zero one tick code symbols
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ unchangedSymbolsWord code choice symbols) label origin final ∧
        cost.steps ≤ elapsed + symbols.length * tapeUpdateTime width size ⦄ := by
  induction symbols generalizing output elapsed with
  | nil =>
    vcgen [writeUnchangedSymbols]
    simp_all [unchangedSymbolsWord]
  | cons symbol rest ih =>
    have hfirst : choice.size + input.length +
        (output ++ tapeUpdateWord code choice true symbol symbol).length + 32 ≤ size := by
      simp only [unchangedSymbolsWord, List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    have hrest : choice.size + input.length +
        (output ++ tapeUpdateWord code choice true symbol symbol ++
          unchangedSymbolsWord code choice rest).length + 32 ≤ size := by
      simpa only [unchangedSymbolsWord, List.flatMap_cons, List.append_assoc] using hsize
    rw [writeUnchangedSymbols]
    vcgen [writeTapeUpdateClause_spec (tm := tm) zero one hne tick code width hwidth choice
      true symbol symbol input output size hfirst label origin elapsed,
      ih (output ++ tapeUpdateWord code choice true symbol symbol) hrest
        (elapsed + tapeUpdateTime width size)]
    all_goals simp_all [unchangedSymbolsWord, List.append_assoc, Nat.succ_mul]
    all_goals lia

private def whenPreviousBlank (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  ifₜ tape =ₜ none then
    moveₜ .Right
    action
  else
    moveₜ .Right

omit [Encodable Γ] in
private theorem whenPreviousBlank_spec (action : Prog (TMQuery tm) Unit)
    (view result : BiTape Γ) (label : Option tm.State) (condition : Prop) [Decidable condition]
    (hcondition : view.moveLeft.head = none ↔ condition) (bound : Nat)
    (haction : condition → ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label, result⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      whenPreviousBlank action
    ⦃ fun _ cost final => final.config = ⟨label, if condition then result else view⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 ⦄ := by
  by_cases h : condition
  · vcgen [whenPreviousBlank, haction h origin (elapsed + 2)]
    all_goals simp_all [TMState.move, TMState.moveCost]
    all_goals lia
  · vcgen [whenPreviousBlank]
    all_goals simp_all [TMState.move, TMState.moveCost]
    all_goals lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem previousBlank_iff (tick : Γ) (choice : ActiveChoices) (input output : List Γ) :
    (pairTape tick choice input output).moveLeft.head = none ↔ choice.secondState.1 = 0 := by
  simp only [pairTape, markedUnaryTape, BiTape.moveLeft, BiTape.segment_left,
    List.reverse_replicate]
  cases h : choice.secondState.1 <;> simp [List.replicate_succ]

private noncomputable def writeOtherCell (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (different equal extra : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  comparePositions tm zero one tick different equal extra
  ifₜ state =ₜ some different then
    writeUnchangedSymbols zero one tick code symbols
  else
    pure ()
  state ←ₜ different

private def otherCellWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbols : List (Option (TapeSymbol Γ))) : List Γ :=
  if choice.firstPosition.1 = choice.secondPosition.1 then []
  else unchangedSymbolsWord code choice symbols

private theorem writeOtherCell_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (different equal extra : tm.State)
    (hfirst : different ≠ equal) (hlast : different ≠ extra) (hother : equal ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ otherCellWord code choice symbols).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeOtherCell (tm := tm) zero one tick code symbols different equal extra
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ otherCellWord code choice symbols) (some different) origin final ∧
        cost.steps ≤ elapsed + comparisonTime size +
          symbols.length * tapeUpdateTime width size ⦄ := by
  have hcap : choice.size + input.length + output.length + 32 ≤ size := by
    simp only [List.length_append] at hsize
    lia
  have hc := comparePositions_spec (tm := tm) zero one hne tick different equal extra
    hfirst hlast hother choice input output size hcap label origin elapsed
  by_cases hpos : choice.firstPosition.1 = choice.secondPosition.1
  · vcgen [writeOtherCell, hc, Spec.branch_false_spec]
    refine ⟨by simp_all [AtPair, Ne.symm hfirst], ?_⟩
    vcgen
    all_goals simp_all [otherCellWord, AtPair]
    all_goals lia
  · have hs := writeUnchangedSymbols_spec (tm := tm) zero one hne tick code width hwidth
      choice symbols input output size (by simpa [otherCellWord, hpos] using hsize)
      (some different) origin (elapsed + comparisonTime size)
    vcgen [writeOtherCell, hc, hs]
    all_goals simp_all [otherCellWord, AtPair]

private noncomputable def writeUnchangedLeaf (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (different equal extra : tm.State) :
    Prog (TMQuery tm) Unit :=
  whenPreviousBlank (writeOtherCell zero one tick code symbols different equal extra)

private def unchangedLeafWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbols : List (Option (TapeSymbol Γ))) : List Γ :=
  if choice.secondState.1 = 0 then otherCellWord code choice symbols else []

private theorem writeUnchangedLeaf_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (different equal extra : tm.State)
    (hfirst : different ≠ equal) (hlast : different ≠ extra) (hother : equal ≠ extra)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ unchangedLeafWord code choice symbols).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some different) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeUnchangedLeaf (tm := tm) zero one tick code symbols different equal extra
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ unchangedLeafWord code choice symbols) (some different) origin final ∧
        cost.steps ≤ elapsed + comparisonTime size +
          symbols.length * tapeUpdateTime width size + 2 ⦄ := by
  have hr := whenPreviousBlank_spec (tm := tm)
    (writeOtherCell zero one tick code symbols different equal extra)
    (pairTape tick choice input output)
    (pairTape tick choice input (output ++ otherCellWord code choice symbols))
    (some different) (choice.secondState.1 = 0) (previousBlank_iff tick choice input output)
    (comparisonTime size + symbols.length * tapeUpdateTime width size) (by
      intro hzero position steps
      have hs := writeOtherCell_spec (tm := tm) zero one hne tick code width hwidth symbols
        different equal extra hfirst hlast hother choice input output size
        (by simpa [unchangedLeafWord, hzero] using hsize) (some different) position steps
      simpa [AtPair, and_assoc, Nat.add_assoc] using hs) origin elapsed
  vcgen [writeUnchangedLeaf, hr]
  all_goals by_cases hzero : choice.secondState.1 = 0
  all_goals simp_all [AtPair, unchangedLeafWord, and_assoc, Nat.add_assoc]

private def indexChoice (time position control otherPosition otherControl : Nat) : ActiveChoices :=
  ⟨(time, 0), (position, 0), (control, 0), (otherPosition, 0), (otherControl, 0)⟩

private def unchangedPiece (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ)))
    (time position control otherPosition otherControl : Nat) : List Γ :=
  unchangedLeafWord code (indexChoice time position control otherPosition otherControl) symbols

/-- This lists the cell-preservation clauses in increasing time, head, state, and cell order. -/
def unchangedWord (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (times positions states : Nat) : List Γ :=
  ChoiceIteration.word (unchangedPiece code symbols) times positions states

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem unchangedLeafWord_indices (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbols : List (Option (TapeSymbol Γ))) :
    unchangedLeafWord code choice symbols = unchangedPiece code symbols choice.time.1
      choice.firstPosition.1 choice.firstState.1 choice.secondPosition.1 choice.secondState.1 := rfl

/--
This writes the clauses requiring every tape cell away from the verifier's head to keep its
symbol. It reads all bounds from the tape. The first time tick is temporarily set aside so
that a word of `t + 1` ticks gives exactly `t` transitions, and that tick is restored afterward.
-/
noncomputable def writeUnchangedClauses (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (symbols : List (Option (TapeSymbol Γ)))
    (different equal extra : tm.State) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ different
  markFirst tick (ChoiceIteration.afterFirstTime tm tick
    (writeUnchangedLeaf zero one tick code symbols different equal extra))

/-- This is the leaf's position comparison and the fixed list of cell-preservation clauses. -/
@[expose] def unchangedLeafTime (width size symbols : Nat) : Nat :=
  comparisonTime size + symbols * tapeUpdateTime width size + 2

/-- This bounds all cell-preservation clauses, including the temporary first time tick. -/
@[expose] def unchangedTime (width size symbols : Nat) : Nat :=
  ChoiceIteration.iterationMoves size (unchangedLeafTime width size symbols) + 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
/-- The total move bound is polynomial in the source and complete output lengths. -/
theorem unchangedTime_le (width size symbols : Nat) :
    unchangedTime width size symbols ≤
      4194304 * (symbols + 1) * (width + 1) * (size + 16) ^ 7 := by
  have hi := ChoiceIteration.iterationMoves_le size (unchangedLeafTime width size symbols)
  have hl : unchangedLeafTime width size symbols + 1 ≤
      131072 * (symbols + 1) * (width + 1) * (size + 16) ^ 2 := by
    dsimp [unchangedLeafTime, comparisonTime, tapeUpdateTime, literalTime,
      tapeLiteralTime, markedNumberBudget]
    ring_nf
    lia
  calc
    _ ≤ 16 * (size + 1) ^ 5 * (unchangedLeafTime width size symbols + 1) + 2 := by
      exact Nat.add_le_add_right hi 2
    _ ≤ 16 * (size + 16) ^ 5 *
        (131072 * (symbols + 1) * (width + 1) * (size + 16) ^ 2) + 2 := by
      gcongr
      lia
    _ ≤ _ := by ring_nf; lia

/-- The cell-preservation writer appends its ordered clauses and restores all source words. -/
@[spec] theorem writeUnchangedClauses_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (different equal extra : tm.State)
    (hfirst : different ≠ equal) (hlast : different ≠ extra) (hother : equal ≠ extra)
    (times positions states : Nat) (input output : List Γ) (size : Nat)
    (hsize : times + 2 * positions + 2 * states + input.length +
      (output ++ unchangedWord code symbols times positions states).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, ChoiceIteration.layout tick (times + 1) positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeUnchangedClauses tm zero one tick code symbols different equal extra
    ⦃ fun _ cost final => final.config = ⟨some different,
        ChoiceIteration.layout tick (times + 1) positions states input
          (output ++ unchangedWord code symbols times positions states)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          unchangedTime width size symbols.length ⦄ := by
  let action := writeUnchangedLeaf (tm := tm) zero one tick code symbols different equal extra
  let piece := unchangedPiece code symbols
  let bound := unchangedLeafTime width size symbols.length
  have hleaf : ChoiceIteration.LeafSpec tick times positions states input piece
      (some different) action size bound := by
    intro time timeRest position positionRest control controlRest otherPosition otherPositionRest
      otherControl otherControlRest ht hp hs hop hos out hcap positionHead steps
    let choice : ActiveChoices := ⟨(time, timeRest), (position, positionRest),
      (control, controlRest), (otherPosition, otherPositionRest), (otherControl, otherControlRest)⟩
    have hdata : choice.size + input.length +
        (out ++ unchangedLeafWord code choice symbols).length + 32 ≤ size := by
      rw [unchangedLeafWord_indices]
      dsimp [choice, ActiveChoices.size]
      dsimp [piece] at hcap
      lia
    have ha := writeUnchangedLeaf_spec (tm := tm) zero one hne tick code width hwidth symbols
      different equal extra hfirst hlast hother choice input out size hdata positionHead steps
    simpa [AtPair, pairTape, ActiveChoices.leftWords, ActiveChoices.rightWords, choice,
      unchangedLeafWord_indices, piece, action, bound, unchangedLeafTime, and_assoc,
      Nat.add_assoc] using ha
  have hrun (positionHead : ℤ) (steps : Nat) := ChoiceIteration.forFiveChoices_spec tick action
    times positions states input output piece (some different) size bound hleaf
    (by simpa only [unchangedWord, piece] using hsize) positionHead steps
  have hafter (positionHead : ℤ) (steps : Nat) := ChoiceIteration.afterFirstTime_spec tick action
    times positions states input output (output ++
      unchangedWord code symbols times positions states)
    (some different) (ChoiceIteration.iterationMoves size bound) (by
      simpa only [unchangedWord, piece] using hrun) positionHead steps
  have hmark := markFirst_spec tick (ChoiceIteration.afterFirstTime tm tick action) StackTape.nil
    (List.replicate times tick)
    (StackTape.separateWords [List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input] (StackTape.mapSome output))
    (StackTape.separateWords [List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input]
      (StackTape.mapSome (output ++ unchangedWord code symbols times positions states)))
    (some different) (ChoiceIteration.iterationMoves size bound + 2)
    hafter origin elapsed
  dsimp only [action] at hmark
  vcgen [writeUnchangedClauses, hmark]
  all_goals simp_all [ChoiceIteration.layout, List.replicate_succ,
    unchangedTime, bound]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem unchangedPiece_eq (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ)))
    (time position control otherPosition otherControl : Nat) :
    unchangedPiece code symbols time position control otherPosition otherControl =
      if otherControl = 0 then
        if position = otherPosition then []
        else unchangedSymbolsWord code (indexChoice time position control otherPosition 0) symbols
      else [] := rfl

omit [Inhabited Γ] [DecidableEq Γ] in
/-- The cell-preservation writer uses exactly the existing finite-computation clauses. -/
theorem unchangedWord_eq (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ) :
    unchangedWord code (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
      problem.time (NPToSAT.Computation.width problem) (problem.verifier.states + 2) =
        (formulaPrefix ((unchangedClauses problem).rename Variable.name)).flatMap code := by
  have hfirst (text : List Γ) :
      (List.range (problem.verifier.states + 2)).flatMap
        (fun index => if index = 0 then text else []) = text := by
    rw [List.range_succ_eq_map]
    simp
  have hindices (count : Nat) : (List.finRange count).map Fin.val = List.range count := by
    ext index
    simp
  have hfilter {α : Type} (values : List α) (predicate : α → Bool) (f : α → List Γ) :
      (values.filter predicate).flatMap f =
        values.flatMap (fun value => if predicate value then f value else []) := by
    rw [← List.filterMap_eq_filter, List.filterMap_eq_flatMap_toList, List.flatMap_assoc]
    congr 1
    funext value
    cases h : predicate value <;> simp [h]
  have hclause (time : Fin problem.time)
      (position otherPosition : Fin (NPToSAT.Computation.width problem))
      (control : Option (Fin (problem.verifier.states + 1)))
      (symbol : Option (TapeSymbol Γ)) :
      (certificateEncoding.encode
        ((Clause.implies [Variable.head time.castSucc (position, control),
          Variable.tape time.castSucc otherPosition symbol]
          (Variable.tape time.succ otherPosition symbol)).rename Variable.name) ++
            [(Sum.inr 4 : CodeSymbol)]).flatMap
            code = tapeUpdateWord code
              (indexChoice time.val position.val (Encodable.encode control) otherPosition.val 0)
              true symbol symbol := by
    simp [tapeUpdateWord, formulaPrefix, Clause.rename, Clause.implies, Clause.forbid,
      Literal.rename, Variable.name, headName, tapeName, indexChoice, Naming.bits]
  simp only [unchangedWord, ChoiceIteration.word, unchangedPiece_eq, hfirst]
  rw [← stateChoices_codes problem]
  simp_rw [← hindices, List.flatMap_map]
  simp only [unchangedClauses, CNF.rename, controlChoices, formulaPrefix,
    List.map_flatMap, List.flatMap_map, List.flatMap_assoc]
  simp_rw [hfilter]
  simp only [unchangedSymbolsWord, hclause]
  simp only [ne_eq, Fin.ext_iff, decide_not]
  congr 1
  funext time
  congr 1
  funext position
  congr 1
  funext control
  congr 1
  funext otherPosition
  by_cases h : position.val = otherPosition.val <;> simp [h, eq_comm]

end Algolean.Algorithms.NPToSAT.Computation.TransitionWriting
