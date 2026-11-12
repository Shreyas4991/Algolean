/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.EarlierWords
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting

/-!
# Writing one more than a unary count

* `appendUnarySuccessor` reads a count stored as repetitions of one fixed symbol and appends
  the binary encoding of one more than that count. It can also write the number of binary
  digits before those digits.
* The specification preserves the unary source, neighboring words, and initial head position.
  The temporary counter is empty again when the program finishes.

This is a machine template. The digit symbols, output symbol words, and numbers of intervening
words are fixed when constructing the containing machine. The count is read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This reads a unary count, adds one, and writes the result in binary at the output. The source
and head position are restored. All parameters are fixed with the containing machine, while
the number of repetitions is read from the tape.
-/
def appendUnarySuccessor (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : Bool → List Γ) (header : Bool) (near distance : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onCounter tm (incrementLeft tm zero one) near
  countBlocks tm zero one tick [] near
  onCounter tm (appendCounterNumber zero one code header distance) near

/-- This bounds counting the source, writing its successor, and clearing the temporary counter. -/
@[expose] def unarySuccessorMoves (header : Bool) (width count : Nat)
    (near parts : List (List Γ)) (output : Nat) : Nat :=
  countBlocksMoves 1 1 count (regionSpan near) +
    counterNumberMoves header width (count + 1).size
      (regionSpan near + count + 1 + regionSpan parts) output +
    (count + 1).size + 4 * (near.map List.length).sum + 8 * near.length + 14

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- The successor writer's move bound is quadratic in the lengths of the words it crosses. -/
theorem unarySuccessorMoves_le (header : Bool) (width count : Nat)
    (near parts : List (List Γ)) (output : Nat) :
    unarySuccessorMoves header width count near parts output ≤
      1024 * (width + 1) *
        (count + regionSpan near + regionSpan parts + output + 4) ^ 2 := by
  let total := count + regionSpan near + regionSpan parts + output + 3
  have hc : count ≤ total := by dsimp [total]; lia
  have hn : regionSpan near ≤ total := by dsimp [total]; lia
  have ho : output ≤ total := by dsimp [total]; lia
  have hs : (count + 1).size ≤ total := by
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [total]; lia)
  have hd : regionSpan near + count + 1 + regionSpan parts ≤ total := by dsimp [total]; lia
  have hl : (near.map List.length).sum ≤ total := by dsimp [total, regionSpan]; lia
  have hh : near.length ≤ total := by dsimp [total, regionSpan]; lia
  have hcount : countBlocksMoves 1 1 count (regionSpan near) ≤
      countBlocksMoves 1 1 total total := by dsimp [countBlocksMoves]; gcongr
  have hcounter : counterNumberMoves header width (count + 1).size
      (regionSpan near + count + 1 + regionSpan parts) output ≤
      counterNumberMoves header width total total total := by
    cases header <;> simp only [counterNumberMoves, Bool.false_eq_true,
      ite_false, ite_true, lengthHeaderMoves, copyBitsMoves]
    all_goals gcongr
  have hmain : unarySuccessorMoves header width count near parts output ≤
      countBlocksMoves 1 1 total total +
        counterNumberMoves header width total total total + 13 * total + 14 := by
    dsimp only [unarySuccessorMoves]
    lia
  calc
    _ ≤ _ := hmain
    _ ≤ 1024 * (width + 1) * (total + 1) ^ 2 := by
      cases header <;> simp only [counterNumberMoves, Bool.false_eq_true,
        ite_false, ite_true, countBlocksMoves, lengthHeaderMoves, copyBitsMoves]
      all_goals ring_nf
      all_goals lia
    _ = _ := rfl

private theorem initializeCounter_spec (zero one : Γ) (hne : zero ≠ one)
    (near : List (List Γ)) (source : List Γ) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (counterLeft [] near) source tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onCounter tm (incrementLeft tm zero one) near.length
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (counterLeft (counterWord zero one 1) near) source tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          2 * (near.map List.length).sum + 4 * near.length + 10 ⦄ := by
  have ha (position : ℤ) (steps : Nat) := incrementCounterWord_spec (tm := tm)
    zero one hne 0 (counterRight near source tail) label position steps
  vcgen [onCounter_spec (tm := tm) (incrementLeft tm zero one) [] (counterWord zero one 1)
    near source tail tail label label 5 (by
      intro position steps
      simpa [counterWord] using ha position steps) origin elapsed]
  all_goals simp_all [counterWord]
  all_goals lia

/-- Writing a successor appends its existing binary encoding and preserves the source and head. -/
@[spec] theorem appendUnarySuccessor_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (near parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft [] near) (List.replicate count tick)
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendUnarySuccessor tm zero one tick code header near.length
        (near.length + 1 + parts.length)
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (counterLeft [] near) (List.replicate count tick)
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header (count + 1)).flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          unarySuccessorMoves header width count near parts output.length ⦄ := by
  let source := List.replicate count tick
  let allParts := near.reverse ++ source :: parts
  let written := output ++ (unaryNumberBits header (count + 1)).flatMap code
  let budget := counterNumberMoves header width (count + 1).size
    (regionSpan allParts) output.length
  have hspan : regionSpan allParts = regionSpan near + count + 1 + regionSpan parts := by
    simp [allParts, source, regionSpan, List.map_append, List.sum_append]
    ring
  have ha (position : ℤ) (steps : Nat) := appendCounterNumber_le_spec (tm := tm)
    zero one hne code width hwidth header (count + 1) allParts output label position steps
  have hvisit := onCounter_spec (tm := tm)
    (appendCounterNumber zero one code header (near.length + 1 + parts.length))
    (counterWord zero one (count + 1)) [] near source
    (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts (StackTape.mapSome written)) label label budget (by
      intro position steps
      simpa [allParts, counterRight, StackTape.separateWords_append, written, budget,
        counterWord, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ha position steps) origin
    (elapsed + 2 * (near.map List.length).sum + 4 * near.length + 10 +
      countBlocksMoves 1 1 count (regionSpan near))
  vcgen [appendUnarySuccessor,
    initializeCounter_spec zero one hne near source
      (StackTape.separateWords parts (StackTape.mapSome output)) label origin elapsed,
    countBlocks_spec (tm := tm) zero one hne tick [] 1 count near
      (StackTape.separateWords parts (StackTape.mapSome output)) label origin
      (elapsed + 2 * (near.map List.length).sum + 4 * near.length + 10), hvisit]
  all_goals simp_all [source, unaryWord, written, unarySuccessorMoves, budget,
    counterWord, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
  all_goals lia

/-- This writes one more than an earlier word's count and returns to the starting head position. -/
def appendEarlierUnarySuccessor (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : Bool → List Γ) (header : Bool) (before between distance : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onCounter tm (appendUnarySuccessor tm zero one tick code header before distance) between

/-- This includes the successor writer and the outward and return visits to the earlier word. -/
@[expose] def earlierUnarySuccessorMoves (header : Bool) (width count : Nat)
    (before between : List (List Γ)) (current : List Γ) (parts : List (List Γ))
    (output : Nat) : Nat :=
  unarySuccessorMoves header width count before (between.reverse ++ current :: parts) output +
    2 * count + 2 * (between.map List.length).sum + 4 * between.length + 4

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- Writing an earlier count's successor uses at most the common quadratic allowance. -/
theorem appendEarlierSuccessorAtMark_moves_le (header : Bool) (width count size : Nat)
    (before between : List (List Γ)) (crossed : List Γ) (parts : List (List Γ)) (output : Nat)
    (hsize : count + regionSpan before + regionSpan between + crossed.length +
      regionSpan parts + output ≤ size) :
    2 * crossed.length + 2 +
      earlierUnarySuccessorMoves header width count before between crossed parts output ≤
        markedNumberBudget width size := by
  have hu := unarySuccessorMoves_le header width count before
    (between.reverse ++ crossed :: parts) output
  have hsum : regionSpan (between.reverse ++ crossed :: parts) =
      regionSpan between + crossed.length + 1 + regionSpan parts := by
    simp [Nat.add_assoc]
  have hb : unarySuccessorMoves header width count before
      (between.reverse ++ crossed :: parts) output ≤
        1024 * (width + 1) * (size + 5) ^ 2 := by
    apply hu.trans
    rw [hsum]
    calc
      _ = 1024 * (width + 1) *
          (count + regionSpan before + regionSpan between + crossed.length +
            regionSpan parts + output + 5) ^ 2 := by ring
      _ ≤ _ := by gcongr
  simp only [earlierUnarySuccessorMoves]
  have hsumlen : (between.map List.length).sum + between.length ≤ size := by
    dsimp [regionSpan] at hsize
    lia
  dsimp [markedNumberBudget]
  ring_nf at hb ⊢
  lia

/-- Writing the earlier count's successor preserves the source words and the starting head. -/
@[spec] theorem appendEarlierUnarySuccessor_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (before between : List (List Γ))
    (current : List Γ) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let left := counterLeft [] (between ++ List.replicate count tick :: before)
    ⦃ fun cost machineState => machineState.config =
        ⟨label, BiTape.segment left current
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendEarlierUnarySuccessor tm zero one tick code header before.length between.length
        (before.length + between.length + parts.length + 2)
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment left current
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header (count + 1)).flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          earlierUnarySuccessorMoves header width count before between current parts
            output.length ⦄ := by
  dsimp only
  let source := List.replicate count tick
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let written := output ++ (unaryNumberBits header (count + 1)).flatMap code
  let resultTail := StackTape.separateWords parts (StackTape.mapSome written)
  let allParts := between.reverse ++ current :: parts
  let bound := unarySuccessorMoves header width count before allParts output.length
  have ha (position : ℤ) (steps : Nat) := appendUnarySuccessor_spec (tm := tm) zero one hne tick
    code width hwidth header count before allParts output label position steps
  have hv := onEarlierWord_spec (tm := tm)
    (appendUnarySuccessor tm zero one tick code header before.length
      (before.length + between.length + parts.length + 2))
    (counterLeft [] before).tail (counterLeft [] before).tail source between current tail resultTail
    label label bound (by
      intro position steps
      simpa [allParts, source, counterRight, tail, resultTail, written, bound,
        List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using ha position steps)
    origin elapsed
  vcgen [appendEarlierUnarySuccessor, hv]
  all_goals
    simp_all [earlierLeft_counterLeft, earlierUnarySuccessorMoves, allParts, source, tail,
      resultTail, written, bound, Nat.add_assoc]

/-- This writes the earlier count's successor and returns to the current blank. -/
def appendEarlierSuccessorAtMark (zero one tick : Γ) (code : Bool → List Γ)
    (header : Bool) (before between distance : Nat) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm
    (appendEarlierUnarySuccessor tm zero one tick code header before between distance)

/-- Writing an earlier count's successor preserves the marked position and every source word. -/
@[spec] theorem appendEarlierSuccessorAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (before between : List (List Γ))
    (crossed : List Γ) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let near := between ++ List.replicate count tick :: before
    ⦃ fun cost current => current.config = ⟨label, markedUnaryTape near crossed parts output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendEarlierSuccessorAtMark (tm := tm) zero one tick code header
        before.length between.length (before.length + between.length + parts.length + 2)
    ⦃ fun _ cost final => final.config = ⟨label, markedUnaryTape near crossed parts
        (output ++ (unaryNumberBits header (count + 1)).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * crossed.length + 2 +
          earlierUnarySuccessorMoves header width count before between crossed parts
            output.length ⦄ := by
  dsimp only
  apply onPrefixAtMark_output_spec
    (appendEarlierUnarySuccessor tm zero one tick code header before.length between.length
      (before.length + between.length + parts.length + 2))
    (between ++ List.replicate count tick :: before) crossed parts output
    (output ++ (unaryNumberBits header (count + 1)).flatMap code) label label
    (earlierUnarySuccessorMoves header width count before between crossed parts output.length)
  intro position steps
  exact appendEarlierUnarySuccessor_spec zero one hne tick code width hwidth header count
    before between crossed parts output label position steps

/--
This writes an earlier count, optionally increased by one, and returns to the current blank.
The containing machine fixes `successor` once. The count itself is read from the tape.
-/
def appendEarlierOffsetAtMark (zero one tick : Γ) (code : Bool → List Γ)
    (header successor : Bool) (before between distance : Nat) : Prog (TMQuery tm) Unit :=
  if successor then appendEarlierSuccessorAtMark zero one tick code header before between distance
  else appendEarlierAtMark zero one tick code header before between distance

/-- Both fixed choices write the requested number and satisfy the same quadratic bound. -/
@[spec] theorem appendEarlierOffsetAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header successor : Bool) (count : Nat) (before between : List (List Γ))
    (crossed : List Γ) (parts : List (List Γ)) (output : List Γ) (size : Nat)
    (hsize : count + regionSpan before + regionSpan between + crossed.length +
      regionSpan parts + output.length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let near := between ++ List.replicate count tick :: before
    ⦃ fun cost current => current.config = ⟨label, markedUnaryTape near crossed parts output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendEarlierOffsetAtMark (tm := tm) zero one tick code header successor
        before.length between.length (before.length + between.length + parts.length + 2)
    ⦃ fun _ cost final => final.config = ⟨label, markedUnaryTape near crossed parts
        (output ++ (unaryNumberBits header (count + successor.toNat)).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + markedNumberBudget width size ⦄ := by
  dsimp only
  cases successor
  · have hm := appendEarlierAtMark_moves_le header width count size before between
      crossed parts output.length hsize
    vcgen [appendEarlierOffsetAtMark, appendEarlierAtMark_spec (tm := tm) zero one hne tick
      code width hwidth header count before between crossed parts output label origin elapsed]
    all_goals simp_all
    all_goals lia
  · have hm := appendEarlierSuccessorAtMark_moves_le header width count size before between
      crossed parts output.length hsize
    vcgen [appendEarlierOffsetAtMark, appendEarlierSuccessorAtMark_spec (tm := tm)
      zero one hne tick code width hwidth header count before between crossed parts output
      label origin elapsed]
    all_goals simp_all
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
