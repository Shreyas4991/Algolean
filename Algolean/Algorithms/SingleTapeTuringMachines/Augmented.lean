/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.Functions
public import Algolean.Models.SingleTapeTM.Alphabet.Pair

/-!
# Keeping the first word of a separator-encoded input

The Turing machine program `firstWord` keeps the symbols before the first separator and erases the
separator and the entire suffix. For example, a tape containing `a b # c # d` becomes `a b`, with
the head returned to the first output cell. The alphabet is `Alphabet.Extended Symbol 1`, so
ordinary symbols are `.inl symbol`, the separator is `.inr 0`, and a blank cell is `none`.

The machine first finds the separator, inserting one at the right blank if it is missing. It then
overwrites the suffix with ordinary symbols before erasing backward, so that any extra separators in
the suffix cannot stop the erasure early. Finally, it erases the first separator and returns to the
beginning. If there is no separator, the original word is preserved; if the input is empty or begins
with a separator, the output is empty.

The pure Lean functions in `Alphabet` describe the expected prefix and suffix for the proofs. The
executable program inspects the tape through machine tests. Its verified Turing machine program
preserves the control state and uses at most `2 * input.length + 4` head moves.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Alphabet
open scoped TMQuery


variable {Symbol : Type} [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM (Extended Symbol 1)} [DecidableEq tm.State]

/--
`seekSeparator tm` is a Turing machine program that moves right across ordinary symbols and stops on
the first separator. If it reaches a blank first, it writes a separator there and stops without
moving past it. The symbols already crossed are preserved.
-/
def seekSeparator (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some (.inr 0)) do
    ifₜ tape =ₜ none then
      tape ←ₜ some (.inr 0)
    else
      moveₜ .Right

/--
The separator scan preserves the ordinary prefix and stops on the first separator, or on the
separator it inserts at the end when none exists. It moves right once for each symbol of
`Alphabet.firstWord right` and preserves the control state.
-/
theorem seekSeparator_correct (left right : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekSeparator tm) s
      (cursor ((Alphabet.firstWord right).reverse.map .inl ++ left)
        ((.inr 0) :: Alphabet.afterMarker right))
      (s.headPos + (Alphabet.firstWord right).length) (Alphabet.firstWord right).length := by
  induction right generalizing left s with
  | nil =>
    unfold seekSeparator
    apply runs_while_step (by simp [hs])
    apply Runs.branch_seq
    have h : Runs (seekSeparator tm) (s.write (some (.inr 0)))
        (cursor left [(.inr 0)]) s.headPos 0 := by
      simp [seekSeparator, TMState.write, hs]
    simpa [seekSeparator, hs] using h.prepend_write
  | cons a right ih =>
    cases a with
    | inr marker =>
      have hm : marker = 0 := Fin.eq_zero marker
      subst marker
      simp [seekSeparator, hs]
    | inl a =>
      unfold seekSeparator
      apply runs_while_step (by simp [hs])
      apply Runs.branch_seq
      have h := ih (.inl a :: left) (s.move .Right) (by simp [TMState.move, hs])
      simpa [seekSeparator, hs, TMState.move,
        List.reverse_cons, List.append_assoc, add_assoc, add_comm, add_left_comm] using
        h.prepend_move

variable [Inhabited Symbol]

/--
`fillRight tm` is a Turing machine program that overwrites every occupied cell from the head to the
first blank with `.inl default`, moving right after each write. It stops on that blank. Replacing
every suffix symbol this way removes extra separators while keeping the suffix contiguous for
backward erasure.
-/
def fillRight (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ some (.inl (default : Symbol))
    moveₜ .Right

/--
The overwrite phase replaces the whole suffix `right` with the same number of ordinary default
symbols, leaving `left` unchanged. It stops on the following blank after exactly `right.length` head
moves and preserves the control state.
-/
theorem fillRight_correct (left right : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (fillRight tm) s
      (cursor (List.replicate right.length (.inl (default : Symbol)) ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil => simp [fillRight, hs]
  | cons a right ih =>
    unfold fillRight
    apply runs_while_step (by simp [hs])
    have h := ih (.inl default :: left)
      ((s.write (some (.inl default))).move .Right) (by simp [TMState.move, TMState.write, hs])
    have h := h.prepend_move.prepend_write
    simp only [fillRight, TMState.move_headPos, TMState.write_headPos, Dir.offset,
      List.length_cons, List.replicate_succ', List.append_assoc, List.singleton_append,
      bind_assoc] at h ⊢
    grind

/--
`eraseToSeparator tm` is a Turing machine program that erases the current cell and moves left until
it reaches a separator, which it leaves in place under the head. In the intended use, the suffix has
already been overwritten by `fillRight`, so no intervening separator can stop this scan early.
-/
def eraseToSeparator (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some (.inr 0)) do
    tape ←ₜ none
    moveₜ .Left

/--
Starting on an ordinary default symbol with `n` more such symbols before the separator, this program
erases all `n + 1` symbols and stops on the separator. It preserves the prefix to the separator's
left and uses exactly `n + 1` head moves.
-/
theorem eraseToSeparator_correct (n : ℕ) (left : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor
      (List.replicate n (.inl (default : Symbol)) ++ (.inr 0) :: left) [.inl default]) :
    Runs (eraseToSeparator tm) s (cursor left [(.inr 0)])
      (s.headPos - (n + 1 : ℕ)) (n + 1) := by
  induction n generalizing s with
  | zero =>
    unfold eraseToSeparator
    apply runs_while_step (by simp [hs])
    have h : Runs (eraseToSeparator tm) ((s.write none).move .Left)
        (cursor left [(.inr 0)]) (s.headPos - 1) 0 := by
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

/--
`finishDiscard tm` is a Turing machine program that starts on the blank after an overwritten suffix.
It moves left, erases back to the separator, and erases the separator too. It leaves the head at the
separator's former coordinate, with the prefix to its left preserved.
-/
def finishDiscard (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  eraseToSeparator tm
  tape ←ₜ none

/--
Starting just after `n` overwritten suffix symbols, this program erases those symbols and their
preceding separator. It finishes `n + 1` cells to the left of the starting position, uses exactly `n
+ 1` head moves, and leaves the prefix unchanged.
-/
theorem finishDiscard_correct (n : ℕ) (left : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor
      (List.replicate n (.inl (default : Symbol)) ++ (.inr 0) :: left) []) :
    Runs (finishDiscard tm) s (cursor left []) (s.headPos - (n + 1 : ℕ)) (n + 1) := by
  cases n with
  | zero =>
    have h : Runs (eraseToSeparator tm) (s.move .Left)
        (cursor left [(.inr 0)]) (s.headPos - 1) 0 := by
      simp [eraseToSeparator, TMState.move, hs, sub_eq_add_neg]
    simpa [finishDiscard] using (h.append_write none).prepend_move
  | succ n =>
    have h := eraseToSeparator_correct n left (s.move .Left)
      (by simp [TMState.move, hs, List.replicate_succ])
    have h := (h.append_write none).prepend_move
    simp only [finishDiscard, cursor_erase_last, TMState.move_headPos, Dir.offset] at h ⊢
    grind

/--
`discardRight tm` is a Turing machine program that starts on a separator and removes it and the
entire suffix to its right. It first overwrites that suffix with ordinary symbols, then erases
backward to the separator so that extra separators in the suffix cause no ambiguity. It finishes at
the starting coordinate, now blank, and preserves all symbols to its left.
-/
def discardRight (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Right
  fillRight tm
  finishDiscard tm

/--
Starting on the displayed separator, the discard program erases that separator and all of `right`,
preserving `left`. It returns to the separator's coordinate, preserves the control state, and uses
exactly `2 * right.length + 2` head moves.
-/
theorem discardRight_correct (left right : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left ((.inr 0) :: right)) :
    Runs (discardRight tm) s (cursor left []) s.headPos (2 * right.length + 2) := by
  have h := (fillRight_correct ((.inr 0) :: left) right (s.move .Right)
    (by simp [TMState.move, hs])).prepend_move
  have hr := h.seq (q := finishDiscard tm) (second := cursor left [])
    (pos₂ := s.headPos) (time₂ := right.length + 1) (by
      intro t ht hp
      convert finishDiscard_correct right.length left t (by simp [ht]) using 1
      simp only [TMState.move_headPos, Dir.offset] at hp
      grind)
  simp only [discardRight, bind_assoc] at hr ⊢
  grind

/--
`firstWord tm` is a Turing machine program that starts at the beginning of a word, keeps the
ordinary symbols before the first separator, and erases that separator and everything after it. It
finishes at the original head coordinate, with the retained symbols still tagged by `.inl`. A
missing separator leaves the original word intact, and additional separators in the suffix are
erased.
-/
def firstWord (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekSeparator tm
  discardRight tm
  seekLeftEnd tm

/--
The first-word program computes the ordinary prefix before the first separator, leaving that prefix
tagged by `.inl` on the tape. For every input it restores the starting head coordinate, preserves
the control state, and uses at most `2 * input.length + 4` head moves.
-/
theorem firstWord_computes :
    Computes (firstWord tm) (fun input => (Alphabet.firstWord input).map .inl)
      (fun input => 2 * input.length + 4) := by
  intro input s hs
  have h := seekSeparator_correct [] input s (by simpa [cursor_start] using hs)
  refine ⟨(Alphabet.firstWord input).length +
    (2 * (Alphabet.afterMarker input).length + 2 + ((Alphabet.firstWord input).length + 2)),
    ?_, ?_⟩
  · unfold firstWord
    refine h.seq ?_
    intro t ht hp
    refine (discardRight_correct ((Alphabet.firstWord input).reverse.map .inl)
      (Alphabet.afterMarker input) t
      (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht)).seq ?_
    intro u hu hup
    simpa [List.map_reverse, cursor_start, hp, hup, sub_eq_add_neg, add_assoc] using
      seekLeftEnd_correct ((Alphabet.firstWord input).reverse.map Sum.inl) [] u
        (by simp [hu])
  · have := Alphabet.lengths_firstWord_afterMarker_le input
    grind

/--
This value contains a verified Turing machine program that keeps the ordinary prefix before the
first separator and erases the remainder. It packages the first-word program with a proof that it
restores the head coordinate and obeys the linear bound `2 * input.length + 4` on head moves.
-/
@[simps! program]
def firstWordComputer : Computer tm (fun input => (Alphabet.firstWord input).map .inl)
    (fun input => 2 * input.length + 4) :=
  Computer.ofComputes firstWord_computes

end Algolean.Algorithms.SingleTapeTuringMachines
