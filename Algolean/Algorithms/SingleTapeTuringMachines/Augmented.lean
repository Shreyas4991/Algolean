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
    have hw : Runs (branch (.tapeIs none) (FreeM.lift (.write (some .separator)))
        (FreeM.lift (.move .Right))) s (cursor left [.separator]) s.headPos 0 := by
      apply Runs.branch
      simpa [hs, cursor, BiTape.write] using write_correct s (some .separator)
    simpa [seekSeparator, Augmented.firstWord, Augmented.afterSeparator] using hw.seq
      (q := seekSeparator tm) (second := cursor left [.separator]) (pos₂ := s.headPos)
      (time₂ := 0) (by
        intro t ht hp
        simpa [seekSeparator, ht, hp] using runs_while_false
          (.not (.tapeIs (some .separator)))
          (branch (.tapeIs none) (FreeM.lift (.write (some .separator)))
            (FreeM.lift (.move .Right))) t (by simp [ht]))
  | cons a right ih =>
    cases a with
    | separator =>
      simpa [seekSeparator, hs, Augmented.firstWord, Augmented.afterSeparator] using
        runs_while_false (.not (.tapeIs (some .separator)))
          (branch (.tapeIs none) (FreeM.lift (.write (some .separator)))
            (FreeM.lift (.move .Right))) s (by simp [hs])
    | symbol a =>
      unfold seekSeparator
      apply runs_while_step (by simp [hs])
      have hm : Runs (branch (.tapeIs none) (FreeM.lift (.write (some .separator)))
          (FreeM.lift (.move .Right))) s (cursor (.symbol a :: left) right)
          (s.headPos + 1) 1 := by
        apply Runs.branch
        simpa [hs, TMState.move] using move_correct s .Right
      have hr := hm.seq (q := seekSeparator tm)
        (second := cursor ((Augmented.firstWord (.symbol a :: right)).reverse.map .symbol ++ left)
          (.separator :: Augmented.afterSeparator (.symbol a :: right)))
        (pos₂ := s.headPos + (Augmented.firstWord (.symbol a :: right)).length)
        (time₂ := (Augmented.firstWord right).length) (by
          intro t ht hp
          simpa [Augmented.firstWord, Augmented.afterSeparator, ht, hp, List.reverse_cons,
            List.map_append, List.append_assoc, add_assoc, add_comm, add_left_comm] using
            ih (.symbol a :: left) t (by simp [ht]))
      simpa [seekSeparator, Augmented.firstWord, Nat.add_comm] using hr

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
  | nil =>
    simpa [fillRight, hs] using
      runs_while_false (tm := tm) (.not (.tapeIs none))
        (do FreeM.lift (.write (some (.symbol (default : Symbol)))); FreeM.lift (.move .Right))
        s (by simp [hs])
  | cons a right ih =>
    unfold fillRight
    apply runs_while_step (by simp [hs])
    have hw : Runs (FreeM.lift (.write (some (.symbol (default : Symbol))))) s
        (cursor left (.symbol default :: right)) s.headPos 0 := by
      simpa [hs, cursor, BiTape.write] using write_correct s (some (.symbol (default : Symbol)))
    have hm := hw.seq (q := FreeM.lift (.move .Right))
      (second := cursor (.symbol default :: left) right) (pos₂ := s.headPos + 1)
      (time₂ := 1) (by
        intro t ht hp
        simpa [TMState.move, ht, hp] using move_correct t .Right)
    have hr := hm.seq (q := fillRight tm)
      (second := cursor (List.replicate (a :: right).length (.symbol default) ++ left) [])
      (pos₂ := s.headPos + (a :: right).length) (time₂ := right.length) (by
        intro t ht hp
        convert ih (.symbol default :: left) t (by simp [ht]) using 1 <;>
          simp [hp, List.replicate_succ', List.append_assoc, add_assoc]
        ring)
    simpa [fillRight, Nat.add_comm] using hr

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
    have hw : Runs (FreeM.lift (.write none)) s (cursor (.separator :: left) [])
        s.headPos 0 := by simpa [hs, cursor, BiTape.write] using write_correct s none
    have hm := hw.seq (q := FreeM.lift (.move .Left)) (second := cursor left [.separator])
      (pos₂ := s.headPos - 1) (time₂ := 1) (by
        intro t ht hp
        simpa [TMState.move, ht, hp, sub_eq_add_neg] using move_correct t .Left)
    simpa [eraseToSeparator] using hm.seq
      (q := eraseToSeparator tm) (second := cursor left [.separator])
      (pos₂ := s.headPos - 1) (time₂ := 0) (by
        intro t ht hp
        simpa [eraseToSeparator, ht, hp] using runs_while_false
          (.not (.tapeIs (some .separator)))
          (do FreeM.lift (.write none); FreeM.lift (.move .Left)) t (by simp [ht]))
  | succ n ih =>
    unfold eraseToSeparator
    apply runs_while_step (by simp [hs])
    have hw : Runs (FreeM.lift (.write none)) s
        (cursor (List.replicate (n + 1) (.symbol default) ++ .separator :: left) [])
        s.headPos 0 := by simpa [hs, cursor, BiTape.write] using write_correct s none
    have hm := hw.seq (q := FreeM.lift (.move .Left))
      (second := cursor (List.replicate n (.symbol default) ++ .separator :: left)
        [.symbol default]) (pos₂ := s.headPos - 1) (time₂ := 1) (by
        intro t ht hp
        simpa [TMState.move, ht, hp, sub_eq_add_neg, List.replicate_succ] using
          move_correct t .Left)
    have hr := hm.seq (q := eraseToSeparator tm) (second := cursor left [.separator])
      (pos₂ := s.headPos - (n + 1 + 1 : ℕ)) (time₂ := n + 1) (by
        intro t ht hp
        convert ih t (by simp [ht]) using 1
        simp [hp, sub_eq_add_neg, add_assoc]
        ring)
    simpa [eraseToSeparator, Nat.add_comm] using hr

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
    have hm : Runs (FreeM.lift (.move .Left)) s (cursor left [.separator])
        (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := do eraseToSeparator tm; FreeM.lift (.write none))
      (second := cursor left []) (pos₂ := s.headPos - 1) (time₂ := 0) (by
        intro t ht hp
        have he : Runs (eraseToSeparator tm) t (cursor left [.separator]) t.headPos 0 := by
          simpa [eraseToSeparator, ht] using runs_while_false
            (.not (.tapeIs (some .separator)))
            (do FreeM.lift (.write none); FreeM.lift (.move .Left)) t (by simp [ht])
        simpa [hp] using he.seq (q := FreeM.lift (.write none))
          (second := cursor left []) (pos₂ := t.headPos) (time₂ := 0) (by
            intro u hu hup
            simpa [hu, hup, cursor, BiTape.write] using write_correct u none))
    simpa [finishDiscard] using hr
  | succ n =>
    have hm : Runs (FreeM.lift (.move .Left)) s
        (cursor (List.replicate n (.symbol default) ++ .separator :: left) [.symbol default])
        (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg, List.replicate_succ] using move_correct s .Left
    have hr := hm.seq (q := do eraseToSeparator tm; FreeM.lift (.write none))
      (second := cursor left []) (pos₂ := s.headPos - (n + 1 + 1 : ℕ))
      (time₂ := n + 1) (by
        intro t ht hp
        have he := eraseToSeparator_correct n left t (by simp [ht])
        have hw := he.seq (q := FreeM.lift (.write none)) (second := cursor left [])
          (pos₂ := s.headPos - (n + 1 + 1 : ℕ)) (time₂ := 0) (by
            intro u hu hup
            convert write_correct u none using 1 <;>
              simp [hu, hup, hp, cursor, BiTape.write, sub_eq_add_neg, add_assoc]
            ring)
        simpa using hw)
    simpa [finishDiscard, Nat.add_comm] using hr

/-- Remove the separator and everything to its right, preserving the word to its left. -/
def discardRight (tm : SingleTapeTM (Augmented Symbol)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Right
  fillRight tm
  finishDiscard tm

theorem discardRight_correct (left right : List (Augmented Symbol)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left (.separator :: right)) :
    Runs (discardRight tm) s (cursor left []) s.headPos (2 * right.length + 2) := by
  have hm : Runs (FreeM.lift (.move .Right)) s (cursor (.separator :: left) right)
      (s.headPos + 1) 1 := by
    simpa [TMState.move, hs] using move_correct s .Right
  have hr := hm.seq (q := do fillRight tm; finishDiscard tm) (second := cursor left [])
    (pos₂ := s.headPos) (time₂ := right.length + (right.length + 1)) (by
      intro t ht hp
      have hf := fillRight_correct (.separator :: left) right t (by simp [ht])
      have he := hf.seq (q := finishDiscard tm) (second := cursor left [])
        (pos₂ := s.headPos) (time₂ := right.length + 1) (by
          intro u hu hup
          convert finishDiscard_correct right.length left u (by simp [hu]) using 1
          lia)
      exact he)
  convert hr using 1
  · simp [discardRight]
  · lia

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
  let leftWord := (Augmented.firstWord input).reverse.map Augmented.symbol
  let tail := Augmented.afterSeparator input
  have hseek := seekSeparator_correct [] input s (by simpa [cursor_start] using hs)
  have hr := hseek.seq (q := do discardRight tm; seekLeftEnd tm)
    (second := BiTape.mk₁ ((Augmented.firstWord input).map .symbol)) (pos₂ := s.headPos)
    (time₂ := (2 * tail.length + 2) + ((Augmented.firstWord input).length + 2)) (by
      intro t ht hp
      have hd := discardRight_correct leftWord tail t (by
        simpa [leftWord, tail] using congrArg SingleTapeTM.Cfg.BiTape ht)
      have hl := hd.seq (q := seekLeftEnd tm)
        (second := BiTape.mk₁ ((Augmented.firstWord input).map .symbol))
        (pos₂ := s.headPos) (time₂ := (Augmented.firstWord input).length + 2) (by
          intro u hu hup
          convert seekLeftEnd_correct leftWord [] u (by simp [hu]) using 1 <;>
            simp [leftWord, List.map_reverse, cursor_start, hup, hp, sub_eq_add_neg, add_assoc])
      exact hl)
  refine ⟨_, by simpa [firstWord] using hr, ?_⟩
  have := Augmented.lengths_le input
  dsimp [tail]
  lia

/-- A reusable machine interface for extracting the first encoded word. -/
@[simps! program]
def firstWordComputer : Computer tm (fun input => (Augmented.firstWord input).map .symbol)
    (fun input => 2 * input.length + 4) :=
  Computer.ofComputes firstWord_computes

end Algolean.Algorithms.SingleTapeTuringMachines
