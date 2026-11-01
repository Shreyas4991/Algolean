/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Preparing the first word of an encoded pair

`firstWord` keeps the original symbols before the first separator, erases the rest of the tape,
and returns the head to its starting position. It works for every input word: a missing
separator means that the whole input is kept. No Lean continuation reads the tape.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM (Augmented Symbol)} [DecidableEq tm.State]

/-- Find the first separator, inserting one at the right blank if none is present. -/
def seekSeparator (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some .separator) do
    ifₜ tape =ₜ none then
      tape ←ₜ some .separator
    else
      moveₜ .Right

theorem seekSeparator_correct (left right : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekSeparator tm) s
      (cursor ((Augmented.firstWord right).reverse.map .symbol ++ left)
        (.separator :: Augmented.afterSeparator right))
      (s.headPos + (Augmented.firstWord right).length) (Augmented.firstWord right).length := by
  induction right generalizing left s with
  | nil =>
    unfold seekSeparator
    apply runs_while_step (by simp [hs])
    apply Runs.branch_seq
    have h : Runs (seekSeparator tm) (s.write (some .separator))
        (cursor left [.separator]) s.headPos 0 := by
      simp [seekSeparator, TMState.write, hs]
    simpa [seekSeparator, hs, Augmented.firstWord, Augmented.afterSeparator] using h.prepend_write
  | cons a right ih =>
    cases a with
    | separator => simp [seekSeparator, hs, Augmented.firstWord, Augmented.afterSeparator]
    | symbol a =>
      unfold seekSeparator
      apply runs_while_step (by simp [hs])
      apply Runs.branch_seq
      have h := ih (.symbol a :: left) (s.move .Right) (by simp [TMState.move, hs])
      simpa [seekSeparator, hs, Augmented.firstWord, Augmented.afterSeparator, TMState.move,
        List.reverse_cons, List.append_assoc, add_assoc, add_comm, add_left_comm] using
        h.prepend_move

variable [Inhabited Symbol]

/-- Overwrite a suffix with ordinary symbols so it cannot contain additional separators. -/
def fillRight (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ some (.symbol (default : Symbol))
    moveₜ .Right

theorem fillRight_correct (left right : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (fillRight tm) s
      (cursor (List.replicate right.length (.symbol (default : Symbol)) ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil => simp [fillRight, hs]
  | cons a right ih =>
    unfold fillRight
    apply runs_while_step (by simp [hs])
    have h := ih (.symbol default :: left)
      ((s.write (some (.symbol default))).move .Right) (by simp [TMState.move, TMState.write, hs])
    have h := h.prepend_move.prepend_write
    simp only [fillRight, TMState.move_headPos, TMState.write_headPos, Dir.offset,
      List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append,
      bind_assoc] at h ⊢
    grind

/-- Erase leftwards until the separator is under the head, leaving that separator in place. -/
def eraseToSeparator (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some .separator) do
    tape ←ₜ none
    moveₜ .Left

theorem eraseToSeparator_correct (n : ℕ) (left : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor
      (List.replicate n (.symbol (default : Symbol)) ++ .separator :: left) [.symbol default]) :
    Runs (eraseToSeparator tm) s (cursor left [.separator])
      (s.headPos - (n + 1 : ℕ)) (n + 1) := by
  induction n generalizing s with
  | zero =>
    unfold eraseToSeparator
    apply runs_while_step (by simp [hs])
    have h : Runs (eraseToSeparator tm) ((s.write none).move .Left)
        (cursor left [.separator]) (s.headPos - 1) 0 := by
      simp [eraseToSeparator, TMState.move, TMState.write, hs, sub_eq_add_neg]
    simpa [eraseToSeparator] using h.prepend_move.prepend_write
  | succ n ih =>
    unfold eraseToSeparator
    apply runs_while_step (by simp [hs])
    have h := ih ((s.write none).move .Left)
      (by simp [TMState.move, TMState.write, hs, List.replicate_succ])
    have h := h.prepend_move.prepend_write
    simp only [eraseToSeparator, TMState.move_headPos, TMState.write_headPos, Dir.offset,
      Nat.cast_add, Nat.cast_one, bind_assoc] at h ⊢
    grind

/-- Finish erasing an overwritten suffix, including the separator that precedes it. -/
def finishDiscard (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  eraseToSeparator tm
  tape ←ₜ none

theorem finishDiscard_correct (n : ℕ) (left : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor
      (List.replicate n (.symbol (default : Symbol)) ++ .separator :: left) []) :
    Runs (finishDiscard tm) s (cursor left []) (s.headPos - (n + 1 : ℕ)) (n + 1) := by
  cases n with
  | zero =>
    have h : Runs (eraseToSeparator tm) (s.move .Left)
        (cursor left [.separator]) (s.headPos - 1) 0 := by
      simp [eraseToSeparator, TMState.move, hs, sub_eq_add_neg]
    simpa [finishDiscard] using (h.append_write none).prepend_move
  | succ n =>
    have h := eraseToSeparator_correct n left (s.move .Left)
      (by simp [TMState.move, hs, List.replicate_succ])
    have h := (h.append_write none).prepend_move
    simp only [finishDiscard, cursor_erase_last, TMState.move_headPos, Dir.offset] at h ⊢
    grind

/-- Remove the separator and everything to its right, preserving the word to its left. -/
def discardRight (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Right
  fillRight tm
  finishDiscard tm

theorem discardRight_correct (left right : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left (.separator :: right)) :
    Runs (discardRight tm) s (cursor left []) s.headPos (2 * right.length + 2) := by
  have h := (fillRight_correct (.separator :: left) right (s.move .Right)
    (by simp [TMState.move, hs])).prepend_move
  have hr := h.seq (q := finishDiscard tm) (second := cursor left [])
    (pos₂ := s.headPos) (time₂ := right.length + 1) (by
      intro t ht hp
      convert finishDiscard_correct right.length left t (by simp [ht]) using 1
      simp only [TMState.move_headPos, Dir.offset] at hp
      grind)
  simp only [discardRight, bind_assoc] at hr ⊢
  grind

/-- Keep the first word of a pair and return to its first cell. A missing separator keeps the
entire word. The program also terminates on words containing several separators. -/
def firstWord (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekSeparator tm
  discardRight tm
  seekLeftEnd tm

/-- Preparing the first component is a uniform machine computation with a linear time bound. -/
theorem firstWord_computes :
    Computes (firstWord tm) (fun input => (Augmented.firstWord input).map .symbol)
      (fun input => 2 * input.length + 4) := by
  intro input s hs
  have h := seekSeparator_correct [] input s (by simpa [cursor_start] using hs)
  refine ⟨(Augmented.firstWord input).length +
    (2 * (Augmented.afterSeparator input).length + 2 + ((Augmented.firstWord input).length + 2)),
    ?_, ?_⟩
  · unfold firstWord
    refine h.seq ?_
    intro t ht hp
    refine (discardRight_correct ((Augmented.firstWord input).reverse.map .symbol)
      (Augmented.afterSeparator input) t
      (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht)).seq ?_
    intro u hu hup
    simpa [List.map_reverse, cursor_start, hp, hup, sub_eq_add_neg, add_assoc] using
      seekLeftEnd_correct ((Augmented.firstWord input).reverse.map Augmented.symbol) [] u
        (by simp [hu])
  · have := Augmented.lengths_le input
    grind

/-- A reusable machine interface for extracting the first encoded word. -/
@[simps! program]
def firstWordComputer : Computer tm (fun input => (Augmented.firstWord input).map .symbol)
    (fun input => 2 * input.length + 4) :=
  Computer.ofComputes firstWord_computes

end Algolean.Algorithms.SingleTapeTuringMachines
