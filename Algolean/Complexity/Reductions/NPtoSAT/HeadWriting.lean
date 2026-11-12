/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.LiteralWriting
public import Algolean.Complexity.Reductions.NPToTMSAT.ChoiceIteration
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CellMarking

/-!
# Writing the initial head clause

The initial input begins at recorded position `t`, where `t` is the transition bound. The
program reads that number from the unary time word and writes the clause placing the head
there at time zero. The initial state is fixed when constructing the reduction program.

The bounds and input remain on the tape. The head returns to the first time cell, and the
number of moves is bounded by a quadratic polynomial in the source and output lengths.
-/

public section

namespace Algolean.Algorithms.NPToSAT.HeadWriting

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT Computability
open NPToTMSAT Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def front (code : CodeSymbol → List Γ) : List Γ :=
  code (.inr 0) ++ code (.inl true) ++ code (.inl true) ++ code (.inl false)

private def ending (code : CodeSymbol → List Γ) (initialCode : Nat) : List Γ :=
  (encodingNatBool.encode initialCode).flatMap (fun bit => code (.inl bit)) ++
    code (.inr 2) ++ code (.inr 3) ++ code (.inr 4)

/-- This is the initial head clause, with time zero and recorded position equal to the bound. -/
@[expose] def word (code : CodeSymbol → List Γ) (initialCode time : Nat) : List Γ :=
  code (.inr 0) ++ code (.inl true) ++ code (.inl true) ++ code (.inl false) ++
    (unaryNumberBits true time).flatMap (fun bit => code (.inl bit)) ++
    (encodingNatBool.encode initialCode).flatMap (fun bit => code (.inl bit)) ++
    code (.inr 2) ++ code (.inr 3) ++ code (.inr 4)

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem word_eq (code : CodeSymbol → List Γ) (initialCode time : Nat) :
    word code initialCode time = front code ++
      (unaryNumberBits true time).flatMap (fun bit => code (.inl bit)) ++
        ending code initialCode := by
  simp [word, front, ending, List.append_assoc]

private noncomputable def writeAtMark (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (initialCode : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendAcross tm (front code) 6
  moveₜ .Right
  appendUnaryNumber tm zero one tick [] (fun bit => code (.inl bit)) true 0 6
  moveₜ .Left
  appendAcross tm (ending code initialCode) 6

/-- This writes the initial head clause using the transition bound already on the tape. -/
noncomputable def writeHead (tm : SingleTapeTM Γ)
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (initialCode : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  markFirst tick (writeAtMark zero one tick code initialCode)

/-- This quadratic polynomial bounds the complete initial head writer. -/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  C (8192 * (width + 1)) * (X + 16) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem writeNumber_moves_le (width size count before extra : Nat)
    (parts : List (List Γ))
    (hsize : count + regionSpan parts + before + extra + 16 ≤ size) :
    2 * (count + 1 + regionSpan parts + before) + 8 + 1 +
      unaryNumberMoves true width 1 count [] parts before + 1 +
      2 * (count + 1 + regionSpan parts + before + extra) + 8 ≤
        (timeBound width).eval size := by
  have hn := unaryNumberMoves_le true width 1 count ([] : List (List Γ)) parts before
  have hmono := Nat.mul_le_mul_left (1024 * (width + 1))
    (Nat.pow_le_pow_left (show count + regionSpan parts + before + 3 ≤ size + 16 by lia) 2)
  norm_num only [regionSpan_nil, Nat.add_zero] at hn
  simp only [timeBound, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_ofNat]
  ring_nf at hn hmono ⊢
  lia

private theorem writeAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (initialCode time positions states : Nat) (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ word code initialCode time).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let parts := [List.replicate positions tick, List.replicate states tick,
      List.replicate positions tick, List.replicate states tick, input]
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil [] (StackTape.prepend (List.replicate time tick)
          (StackTape.cons none (StackTape.separateWords parts (StackTape.mapSome output))))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeAtMark (tm := tm) zero one tick code initialCode
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil [] (StackTape.prepend (List.replicate time tick)
          (StackTape.cons none (StackTape.separateWords parts
            (StackTape.mapSome (output ++ word code initialCode time)))))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  dsimp only
  let parts := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  let first := output ++ front code
  let middle := first ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit))
  let allParts := List.replicate time tick :: parts
  let firstMoves := 2 * (regionSpan allParts + output.length + (front code).length) + 8
  let numberMoves := unaryNumberMoves true width 1 time [] parts first.length
  have ha := appendAcross_le_spec (tm := tm) (front code) allParts output StackTape.nil
    label origin elapsed
  have hn := appendUnaryNumber_spec (tm := tm) zero one hne tick []
    (fun bit => code (.inl bit)) width (fun bit => hwidth (.inl bit)) true time [] parts first
    label (origin + 1) (elapsed + firstMoves + 1)
  have he := appendAcross_le_spec (tm := tm) (ending code initialCode) allParts middle
    StackTape.nil label origin (elapsed + firstMoves + 1 + numberMoves + 1)
  have hcap : time + regionSpan parts + first.length +
      ((unaryNumberBits true time).flatMap (fun bit => code (.inl bit))).length +
        (ending code initialCode).length + 16 ≤ size := by
    simp only [parts, regionSpan_cons, regionSpan_nil, List.length_replicate, first, word_eq,
      List.length_append] at hsize ⊢
    lia
  have htime := writeNumber_moves_le width size time first.length
    (((unaryNumberBits true time).flatMap (fun bit => code (.inl bit))).length +
      (ending code initialCode).length) parts (by simpa only [Nat.add_assoc] using hcap)
  simp only [allParts, parts, List.length_cons, List.length_nil] at ha hn he
  vcgen [writeAtMark, ha, hn, he]
  all_goals
    cases time
    all_goals
      simp_all [parts, allParts, first, middle, word_eq, firstMoves, numberMoves,
        StackTape.separateWords, unaryWord, counterLeft, TMState.move, TMState.moveCost,
        BiTape.segment,
        BiTape.moveRight, BiTape.moveLeft, List.replicate_succ, List.append_assoc]
    all_goals lia

/-- The writer appends the initial head clause and restores every source word and the head. -/
@[spec] theorem writeHead_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (initialCode time positions states : Nat) (input output : List Γ) (size : Nat)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ word code initialCode time).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (time + 1) positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeHead tm zero one tick code initialCode
    ⦃ fun _ cost final => final.config = ⟨label,
        ChoiceIteration.layout tick (time + 1) positions states input
          (output ++ word code initialCode time)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  let parts := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  have hm := markFirst_spec (tm := tm) tick (writeAtMark zero one tick code initialCode)
    StackTape.nil (List.replicate time tick)
    (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts (StackTape.mapSome (output ++ word code initialCode time)))
    label ((timeBound width).eval size) (by
      intro position steps
      exact writeAtMark_spec zero one hne tick code width hwidth initialCode time positions states
        input output size hsize label position steps) origin elapsed
  vcgen [writeHead, hm]
  all_goals simp_all [ChoiceIteration.layout, parts, List.replicate_succ]

end Algolean.Algorithms.NPToSAT.HeadWriting
