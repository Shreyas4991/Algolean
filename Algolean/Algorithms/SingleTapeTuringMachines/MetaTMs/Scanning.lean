/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Basic
public import Algolean.Models.SingleTapeTM.Composition.While

/-!
# Moving across a contiguous block

This file defines Turing machine programs that move the head without changing any tape symbols.
`seekRightSymbol` moves right until it reaches a specified symbol. `seekRightBlank` moves right
until it reaches a blank, and `seekLeftBlank` does the same to the left. Both stop immediately
if their starting cell is blank. `seekLeftEnd` first moves
left, scans to the blank before the block, and then moves right onto its first symbol. It can
therefore return from the blank immediately after a block as well as from inside it.

The correctness theorems state the final head position and exact number of head moves for each
program. They apply with the tape and cell histories left by an earlier computation.
The two `Component` values store the rightward scan and return-to-start program with these proofs.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This Turing machine program moves right until the head is on `symbol`, leaving every tape
symbol unchanged. If it starts on `symbol`, it makes no moves. The correctness theorem requires
that `symbol` occurs at or to the right of the starting cell.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekRightSymbol (tm : SingleTapeTM Symbol) (symbol : Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some symbol) do
    moveₜ .Right

/-- The scan stops at the next chosen symbol and records its exact move count. -/
@[spec] theorem seekRightSymbol_spec (symbol : Symbol) (left crossed suffix : List Symbol)
    (hprefix : symbol ∉ crossed) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current =>
        current.config = ⟨label, cursor left (crossed ++ symbol :: suffix)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekRightSymbol tm symbol
    ⦃ fun _ cost final =>
        final.config = ⟨label, cursor (crossed.reverse ++ left) (symbol :: suffix)⟩ ∧
        final.headPos = origin + crossed.length ∧ cost.steps = elapsed + crossed.length ⦄ := by
  induction crossed generalizing left origin elapsed with
  | nil =>
    unfold seekRightSymbol
    vcgen [Spec.while_false_spec]
    simp_all
  | cons first crossed ih =>
    have hparts : symbol ≠ first ∧ symbol ∉ crossed := by simpa using hprefix
    unfold seekRightSymbol
    vcgen [Spec.while_step_spec (loop := seekRightSymbol tm symbol) (hloop := rfl),
      ih (first :: left) hparts.2 (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost,
      List.reverse_cons, List.append_assoc, add_assoc]
    all_goals lia

/--
If `crossed` contains no `symbol`, the program crosses exactly that crossed and stops on the
following occurrence of `symbol`. It preserves the tape and state and uses `crossed.length` moves.
-/
theorem seekRightSymbol_correct (symbol : Symbol) (left crossed suffix : List Symbol)
    (s : TMState tm) (htape : s.config.BiTape = cursor left (crossed ++ symbol :: suffix))
    (hprefix : symbol ∉ crossed) :
    Runs (seekRightSymbol tm symbol) s (cursor (crossed.reverse ++ left) (symbol :: suffix))
      (s.headPos + crossed.length) crossed.length := by
  apply Spec.runs
  vcgen [seekRightSymbol_spec symbol left crossed suffix hprefix s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`seekRightBlank tm` is a Turing machine program that repeatedly moves the head right while the
current cell is occupied. It stops on the first blank without changing any tape symbols. If the
initial cell is blank, it finishes without moving.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekRightBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Right

/-- The rightward scan preserves the word and uses one move per remaining symbol. -/
@[spec] theorem seekRightBlank_spec (left right : List Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekRightBlank tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor (right.reverse ++ left) []⟩ ∧
        final.headPos = origin + right.length ∧ cost.steps = elapsed + right.length ⦄ := by
  induction right generalizing left origin elapsed with
  | nil =>
    unfold seekRightBlank
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit right ih =>
    unfold seekRightBlank
    vcgen [Spec.while_step_spec (loop := seekRightBlank tm) (hloop := rfl),
      ih (bit :: left) (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost,
      List.reverse_cons, List.append_assoc, add_assoc]
    all_goals lia

/--
Starting from `cursor left right`, the rightward scan crosses every symbol of `right` and stops on
the blank immediately after it. The tape contents are unchanged, the head moves right by
`right.length`, and the program uses exactly that many head moves.
-/
theorem seekRightBlank_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekRightBlank tm) s (cursor (right.reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  apply Spec.runs
  vcgen [seekRightBlank_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`seekLeftBlank tm` is a Turing machine program that repeatedly moves the head left while the current
cell is occupied. It stops on the first blank and leaves all tape symbols unchanged. If it starts on
a blank, it does not move.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekLeftBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Left

/-- A leftward scan starting on a blank leaves the entire machine state unchanged. -/
private theorem seekLeftBlank_blank_spec (view : BiTape Symbol) (hblank : view.head = none)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekLeftBlank tm
    ⦃ fun _ cost final => final.config = ⟨label, view⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  unfold seekLeftBlank
  vcgen [Spec.while_false_spec]
  simp_all

/-- The leftward scan preserves the word and stops on its preceding blank. -/
@[spec] theorem seekLeftBlank_spec (left : List Symbol) (bit : Symbol) (right : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left (bit :: right)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekLeftBlank tm
    ⦃ fun _ cost final => final.config = ⟨label, before (left.reverse ++ bit :: right)⟩ ∧
        final.headPos = origin - (left.length + 1 : Nat) ∧
        cost.steps = elapsed + left.length + 1 ⦄ := by
  induction left generalizing bit right origin elapsed with
  | nil =>
    unfold seekLeftBlank
    vcgen [Spec.while_step_spec (loop := seekLeftBlank tm) (hloop := rfl),
      seekLeftBlank_blank_spec (before (bit :: right)) rfl label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, sub_eq_add_neg]
  | cons previous left ih =>
    unfold seekLeftBlank
    vcgen [Spec.while_step_spec (loop := seekLeftBlank tm) (hloop := rfl),
      ih previous (bit :: right) (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, List.reverse_cons,
      List.append_assoc, sub_eq_add_neg, add_assoc]
    all_goals lia

/--
Starting on the displayed `bit`, the leftward scan crosses that symbol and all of `left` before
stopping on the blank preceding the block. It preserves the entire block and uses exactly
`left.length + 1` head moves.
-/
theorem seekLeftBlank_correct (left : List Symbol) (bit : Symbol) (right : List Symbol)
    (s : TMState tm)
    (hs : s.config.BiTape = cursor left (bit :: right)) :
    Runs (seekLeftBlank tm) s (before (left.reverse ++ bit :: right))
      (s.headPos - (left.length + 1 : ℕ)) (left.length + 1) := by
  apply Spec.runs
  vcgen [seekLeftBlank_spec left bit right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`seekLeftEnd tm` is a Turing machine program that moves left once, scans left to a blank, and then
moves right once. For a contiguous block, it finishes on the first symbol even when it starts on the
blank just after the block. If the block is empty, it returns to its starting cell after two moves.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekLeftEnd (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftBlank tm
  moveₜ .Right

/-- Returning to the first symbol preserves the word and counts both end moves. -/
@[spec] theorem seekLeftEnd_spec (left right : List Symbol) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekLeftEnd tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor [] (left.reverse ++ right)⟩ ∧
        final.headPos = origin - left.length ∧ cost.steps = elapsed + left.length + 2 ⦄ := by
  cases left with
  | nil =>
    vcgen [seekLeftEnd,
      seekLeftBlank_blank_spec (before right) rfl label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, sub_eq_add_neg]
  | cons bit left =>
    vcgen [seekLeftEnd, seekLeftBlank_spec left bit right label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, List.reverse_cons,
      List.append_assoc, sub_eq_add_neg, add_assoc]
    all_goals lia

/--
Starting from `cursor left right`, this program preserves the block and finishes on its first
symbol, or on the starting blank when the block is empty. Its final coordinate is `s.headPos -
left.length`, and it uses exactly `left.length + 2` head moves.
-/
theorem seekLeftEnd_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekLeftEnd tm) s (cursor [] (left.reverse ++ right))
      (s.headPos - left.length) (left.length + 2) := by
  apply Spec.runs
  vcgen [seekLeftEnd_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This value stores the rightward scan with its proof that the tape is preserved and the head stops
on the blank after `right`. The scan uses exactly `right.length` head moves.
-/
@[simps program]
def seekRightBlankComponent :
    Component tm (fun p : List Symbol × List Symbol => fun s => s.config.BiTape = cursor p.1 p.2)
      (fun p s cost final =>
        final.config = {s.config with BiTape := cursor (p.2.reverse ++ p.1) []} ∧
        final.headPos = s.headPos + p.2.length ∧ cost.steps = p.2.length) where
  program := seekRightBlank tm
  correct p s hs := seekRightBlank_correct p.1 p.2 s hs

/--
This value stores the return-to-start program with its proof that the tape is preserved and the
head returns to the first cell. The program uses exactly `left.length + 2` head moves.
-/
@[simps program]
def seekLeftEndComponent :
    Component tm (fun p : List Symbol × List Symbol => fun s => s.config.BiTape = cursor p.1 p.2)
      (fun p s cost final =>
        final.config = {s.config with BiTape := cursor [] (p.1.reverse ++ p.2)} ∧
        final.headPos = s.headPos - p.1.length ∧ cost.steps = p.1.length + 2) where
  program := seekLeftEnd tm
  correct p s hs := seekLeftEnd_correct p.1 p.2 s hs

end Algolean.Algorithms.SingleTapeTuringMachines
