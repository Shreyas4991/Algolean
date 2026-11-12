/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.EarlierUnaryWriting

/-!
# Writing unary counts from a blank-marked position

* `onPrefixAtMark` runs a fixed program on the word before the current blank and returns to
  that blank. The program may change the surrounding tape while preserving that word.
* `appendCurrentAtMark` writes the count immediately before the current blank.
* `appendEarlierAtMark` writes a count stored farther left on the same tape.

Each count is stored by repeating one fixed symbol. Both templates write the count in binary
and can write the number of binary digits before those digits. They preserve the source words,
erase the temporary counter, and return to the original blank. The containing machine fixes
the digit symbols, output representations, and
numbers of intervening words once. The counts are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This writes an earlier unary count while preserving the current blank-marked position. -/
def appendEarlierAtMark (zero one tick : Γ) (code : Bool → List Γ)
    (header : Bool) (before between distance : Nat) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (appendEarlierUnary tm zero one tick code header before between distance)

/-- This writes the unary count just before the current blank-marked position. -/
def appendCurrentAtMark (zero one tick : Γ) (code : Bool → List Γ)
    (header : Bool) (before distance : Nat) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (appendUnaryNumber tm zero one tick [] code header before distance)

/-- A blank marks the head position after the displayed unary prefix. -/
@[expose] def markedUnaryTape (near : List (List Γ)) (crossed : List Γ)
    (parts : List (List Γ)) (output : List Γ) (counter : List Γ := []) : BiTape Γ :=
  BiTape.segment (StackTape.prepend crossed.reverse (counterLeft counter near)) []
    (StackTape.separateWords parts (StackTape.mapSome output))

/-- Returning to the blank preserves the prefix and adds only the outward and return moves. -/
theorem onPrefixAtMark_output_spec (action : Prog (TMQuery tm) Unit)
    (near : List (List Γ)) (crossed : List Γ) (parts : List (List Γ))
    (output written : List Γ) (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (position : ℤ) (steps : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment (counterLeft [] near) crossed
            (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
          current.headPos = position ∧ cost.steps ≤ steps ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result,
          BiTape.segment (counterLeft [] near) crossed
            (StackTape.separateWords parts (StackTape.mapSome written))⟩ ∧
          final.headPos = position ∧ cost.steps ≤ steps + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, markedUnaryTape near crossed parts output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onPrefixAtMark tm action
    ⦃ fun _ cost final => final.config = ⟨result, markedUnaryTape near crossed parts written⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * crossed.length + 2 + bound ⦄ := by
  simpa only [markedUnaryTape] using onPrefixAtMark_spec action
    (counterLeft [] near) (counterLeft [] near) (by simp) crossed
    (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts (StackTape.mapSome written))
    label result bound haction origin elapsed

/-- Writing the current unary count preserves the marked position and every source word. -/
@[spec] theorem appendCurrentAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (near parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, markedUnaryTape near (List.replicate count tick) parts output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendCurrentAtMark (tm := tm) zero one tick code header near.length
        (near.length + 1 + parts.length)
    ⦃ fun _ cost final => final.config =
        ⟨label, markedUnaryTape near (List.replicate count tick) parts
          (output ++ (unaryNumberBits header count).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * count + 2 +
          unaryNumberMoves header width 1 count near parts output.length ⦄ := by
  have ha (position : ℤ) (steps : Nat) := appendUnaryNumber_spec (tm := tm)
    zero one hne tick [] code width hwidth header count near parts output label position steps
  have hp := onPrefixAtMark_output_spec
    (appendUnaryNumber tm zero one tick [] code header near.length
      (near.length + 1 + parts.length))
    near (List.replicate count tick) parts output
    (output ++ (unaryNumberBits header count).flatMap code) label label
    (unaryNumberMoves header width 1 count near parts output.length)
    (by intro position steps; simpa [unaryWord] using ha position steps) origin elapsed
  simpa only [appendCurrentAtMark, List.length_replicate] using hp

/-- Writing an earlier unary count preserves the marked position and every source word. -/
@[spec] theorem appendEarlierAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (before between : List (List Γ))
    (crossed : List Γ) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let near := between ++ List.replicate count tick :: before
    ⦃ fun cost current => current.config = ⟨label, markedUnaryTape near crossed parts output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendEarlierAtMark (tm := tm) zero one tick code header before.length between.length
        (before.length + between.length + parts.length + 2)
    ⦃ fun _ cost final => final.config = ⟨label, markedUnaryTape near crossed parts
        (output ++ (unaryNumberBits header count).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * crossed.length + 2 +
          earlierUnaryMoves header width count before between crossed parts output.length ⦄ := by
  dsimp only
  apply onPrefixAtMark_output_spec
    (appendEarlierUnary tm zero one tick code header before.length between.length
      (before.length + between.length + parts.length + 2))
    (between ++ List.replicate count tick :: before) crossed parts output
    (output ++ (unaryNumberBits header count).flatMap code) label label
    (earlierUnaryMoves header width count before between crossed parts output.length)
  intro position steps
  exact appendEarlierUnary_spec zero one hne tick code width hwidth header count
    before between crossed parts output label position steps

/-- This is a common quadratic allowance for writing one count from a marked position. -/
@[expose] def markedNumberBudget (width size : Nat) : Nat :=
  4096 * (width + 1) * (size + 16) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- Writing an earlier count uses at most the common quadratic allowance. -/
theorem appendEarlierAtMark_moves_le (header : Bool) (width count size : Nat)
    (before between : List (List Γ)) (crossed : List Γ) (parts : List (List Γ)) (output : Nat)
    (hsize : count + regionSpan before + regionSpan between + crossed.length +
      regionSpan parts + output ≤ size) :
    2 * crossed.length + 2 +
      earlierUnaryMoves header width count before between crossed parts output ≤
        markedNumberBudget width size := by
  have hu := unaryNumberMoves_le header width 1 count before
    (between.reverse ++ crossed :: parts) output
  have hsum : regionSpan (between.reverse ++ crossed :: parts) =
      regionSpan between + crossed.length + 1 + regionSpan parts := by
    simp [Nat.add_assoc]
  have hb : unaryNumberMoves header width 1 count before
      (between.reverse ++ crossed :: parts) output ≤
        1024 * (width + 1) * (size + 4) ^ 2 := by
    apply hu.trans
    rw [hsum]
    calc
      _ = 1024 * (width + 1) *
          (count + regionSpan before + regionSpan between + crossed.length +
            regionSpan parts + output + 4) ^ 2 := by ring
      _ ≤ _ := by gcongr
  simp only [earlierUnaryMoves]
  have hsumlen : (between.map List.length).sum + between.length ≤ size := by
    dsimp [regionSpan] at hsize
    lia
  dsimp [markedNumberBudget]
  ring_nf at hb ⊢
  lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- Writing the current count uses at most the common quadratic allowance. -/
theorem appendCurrentAtMark_moves_le (header : Bool) (width count size : Nat)
    (near parts : List (List Γ)) (output : Nat)
    (hsize : count + regionSpan near + regionSpan parts + output ≤ size) :
    2 * count + 2 + unaryNumberMoves header width 1 count near parts output ≤
      markedNumberBudget width size := by
  have hu := unaryNumberMoves_le header width 1 count near parts output
  have hb : unaryNumberMoves header width 1 count near parts output ≤
      1024 * (width + 1) * (size + 4) ^ 2 := by
    apply hu.trans
    calc
      _ = 1024 * (width + 1) *
          (count + regionSpan near + regionSpan parts + output + 3) ^ 2 := by ring
      _ ≤ _ := by gcongr; lia
  dsimp [markedNumberBudget]
  ring_nf at hb ⊢
  lia


end Algolean.Algorithms.SingleTapeTuringMachines
