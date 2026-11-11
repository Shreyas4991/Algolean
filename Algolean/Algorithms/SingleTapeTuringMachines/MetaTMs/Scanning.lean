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

/--
If `crossed` contains no `symbol`, the program crosses exactly that crossed and stops on the
following occurrence of `symbol`. It preserves the tape and state and uses `crossed.length` moves.
-/
theorem seekRightSymbol_correct (symbol : Symbol) (left crossed suffix : List Symbol)
    (s : TMState tm) (htape : s.config.BiTape = cursor left (crossed ++ symbol :: suffix))
    (hprefix : symbol ∉ crossed) :
    Runs (seekRightSymbol tm symbol) s (cursor (crossed.reverse ++ left) (symbol :: suffix))
      (s.headPos + crossed.length) crossed.length := by
  induction crossed generalizing left s with
  | nil =>
    unfold seekRightSymbol
    apply Spec.runs
    vcgen [Spec.while_false_spec]
    cases hcfg : s.config
    simp_all
  | cons first crossed ih =>
    have hparts : symbol ≠ first ∧ symbol ∉ crossed := by simpa using hprefix
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih (first :: left) (s.move .Right)
      (by simp [TMState.move, htape]) hparts.2
    unfold seekRightSymbol
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekRightSymbol tm symbol) (hloop := rfl),
      Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, List.reverse_cons,
      List.append_assoc, add_comm, add_left_comm]

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

/--
Starting from `cursor left right`, the rightward scan crosses every symbol of `right` and stops on
the blank immediately after it. The tape contents are unchanged, the head moves right by
`right.length`, and the program uses exactly that many head moves.
-/
theorem seekRightBlank_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekRightBlank tm) s (cursor (right.reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil =>
    unfold seekRightBlank
    apply Spec.runs
    vcgen [Spec.while_false_spec]
    cases hcfg : s.config
    simp_all
  | cons bit right ih =>
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih (bit :: left) (s.move .Right)
      (by simp [TMState.move, hs])
    unfold seekRightBlank
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekRightBlank tm) (hloop := rfl),
      Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost,
      List.reverse_cons, List.append_assoc, add_comm, add_left_comm]

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
  induction left generalizing bit right s with
  | nil =>
    have hc : Completes (seekLeftBlank tm) (s.move .Left) 0 (s.move .Left) :=
      completes_while_false _ _ _ (by simp [TMState.move, hs])
    unfold seekLeftBlank
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekLeftBlank tm) (hloop := rfl),
      Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, sub_eq_add_neg]
  | cons prev left ih =>
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := ih prev (bit :: right) (s.move .Left)
      (by simp [TMState.move, hs])
    unfold seekLeftBlank
    apply Spec.runs
    vcgen [Spec.while_step_spec (loop := seekLeftBlank tm) (hloop := rfl),
      Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, List.reverse_cons,
      List.append_assoc, sub_eq_add_neg, add_comm, add_left_comm]

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

/--
Starting from `cursor left right`, this program preserves the block and finishes on its first
symbol, or on the starting blank when the block is empty. Its final coordinate is `s.headPos -
left.length`, and it uses exactly `left.length + 2` head moves.
-/
theorem seekLeftEnd_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekLeftEnd tm) s (cursor [] (left.reverse ++ right))
      (s.headPos - left.length) (left.length + 2) := by
  cases left with
  | nil =>
    have hc : Completes (seekLeftBlank tm) (s.move .Left) 0 (s.move .Left) :=
      completes_while_false _ _ _ (by simp [TMState.move, hs])
    apply Spec.runs
    vcgen [seekLeftEnd, Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, sub_eq_add_neg]
  | cons bit left =>
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := seekLeftBlank_correct left bit right
      (s.move .Left) (by simp [TMState.move, hs])
    apply Spec.runs
    vcgen [seekLeftEnd, Spec.steps hc 1]
    all_goals simp_all [TMState.move, TMState.moveCost, List.reverse_cons,
      List.append_assoc, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

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
