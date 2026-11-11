/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning
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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM (Extended Symbol 1)} [DecidableEq tm.State]

/--
`seekSeparator tm` is a Turing machine program that moves right across ordinary symbols and stops on
the first separator. If it reaches a blank first, it writes a separator there and stops without
moving past it. The symbols already crossed are preserved.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def seekSeparator (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some (.inr 0)) do
    ifₜ tape =ₜ none then
      tape ←ₜ some (.inr 0)
    else
      moveₜ .Right

private theorem seekSeparator_marker_spec (left right : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left ((.inr 0) :: right)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekSeparator tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor left ((.inr 0) :: right)⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  unfold seekSeparator
  vcgen [Spec.while_false_spec]
  simp_all

/-- The scan finds the first separator or writes one at the ending blank. -/
@[spec] theorem seekSeparator_spec (left right : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      seekSeparator tm
    ⦃ fun _ cost final => final.config = ⟨label,
        cursor ((Alphabet.firstWord right).reverse.map .inl ++ left)
          ((.inr 0) :: Alphabet.afterMarker right)⟩ ∧
        final.headPos = origin + (Alphabet.firstWord right).length ∧
        cost.steps = elapsed + (Alphabet.firstWord right).length ⦄ := by
  induction right generalizing left origin elapsed with
  | nil =>
    unfold seekSeparator
    vcgen [Spec.while_step_spec (loop := seekSeparator tm) (hloop := rfl),
      seekSeparator_marker_spec left [] label origin elapsed]
    all_goals simp_all [TMState.write]
  | cons symbol right ih =>
    cases symbol with
    | inr marker =>
      have hm : marker = 0 := Fin.eq_zero marker
      subst marker
      vcgen [seekSeparator_marker_spec left right label origin elapsed]
      all_goals simp_all
    | inl symbol =>
      unfold seekSeparator
      vcgen [Spec.while_step_spec (loop := seekSeparator tm) (hloop := rfl),
        ih (.inl symbol :: left) (origin + 1) (elapsed + 1)]
      all_goals simp_all [TMState.move, TMState.moveCost,
        List.reverse_cons, List.append_assoc, add_assoc]
      all_goals lia

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
  apply Spec.runs
  vcgen [seekSeparator_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

variable [Inhabited Symbol]

/--
`fillRight tm` is a Turing machine program that overwrites every occupied cell from the head to the
first blank with `.inl default`, moving right after each write. It stops on that blank. Replacing
every suffix symbol this way removes extra separators while keeping the suffix contiguous for
backward erasure.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def fillRight (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ some (.inl (default : Symbol))
    moveₜ .Right

/-- Overwriting the suffix removes its separators and uses one move per cell. -/
@[spec] theorem fillRight_spec (left right : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left right⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      fillRight tm
    ⦃ fun _ cost final => final.config =
        ⟨label, cursor (List.replicate right.length (.inl (default : Symbol)) ++ left) []⟩ ∧
        final.headPos = origin + right.length ∧ cost.steps = elapsed + right.length ⦄ := by
  induction right generalizing left origin elapsed with
  | nil =>
    unfold fillRight
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol right ih =>
    unfold fillRight
    vcgen [Spec.while_step_spec (loop := fillRight tm) (hloop := rfl),
      ih (.inl default :: left) (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      List.replicate_succ', List.append_assoc, add_assoc]
    all_goals lia

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
  apply Spec.runs
  vcgen [fillRight_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`eraseToSeparator tm` is a Turing machine program that erases the current cell and moves left until
it reaches a separator, which it leaves in place under the head. In the intended use, the suffix has
already been overwritten by `fillRight`, so no intervening separator can stop this scan early.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def eraseToSeparator (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some (.inr 0)) do
    tape ←ₜ none
    moveₜ .Left

omit [Inhabited Symbol] in
private theorem eraseToSeparator_marker_spec (left : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left [(.inr 0)]⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseToSeparator tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor left [(.inr 0)]⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  unfold eraseToSeparator
  vcgen [Spec.while_false_spec]
  simp_all

/-- Erasing backward stops at the separator and preserves the prefix before it. -/
@[spec] theorem eraseToSeparator_spec (n : Nat) (left : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor
        (List.replicate n (.inl (default : Symbol)) ++ (.inr 0) :: left) [.inl default]⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseToSeparator tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor left [(.inr 0)]⟩ ∧
        final.headPos = origin - (n + 1 : Nat) ∧ cost.steps = elapsed + n + 1 ⦄ := by
  induction n generalizing origin elapsed with
  | zero =>
    unfold eraseToSeparator
    vcgen [Spec.while_step_spec (loop := eraseToSeparator tm) (hloop := rfl),
      eraseToSeparator_marker_spec left label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost, sub_eq_add_neg]
  | succ n ih =>
    unfold eraseToSeparator
    vcgen [Spec.while_step_spec (loop := eraseToSeparator tm) (hloop := rfl),
      ih (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      List.replicate_succ, sub_eq_add_neg, add_assoc]
    all_goals lia

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
  apply Spec.runs
  vcgen [eraseToSeparator_spec n left s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`finishDiscard tm` is a Turing machine program that starts on the blank after an overwritten suffix.
It moves left, erases back to the separator, and erases the separator too. It leaves the head at the
separator's former coordinate, with the prefix to its left preserved.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def finishDiscard (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Left
  eraseToSeparator tm
  tape ←ₜ none

/-- The final erasure clears the suffix and its separator with one move per removed cell. -/
@[spec] theorem finishDiscard_spec (n : Nat) (left : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor
        (List.replicate n (.inl (default : Symbol)) ++ (.inr 0) :: left) []⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      finishDiscard tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor left []⟩ ∧
        final.headPos = origin - (n + 1 : Nat) ∧ cost.steps = elapsed + n + 1 ⦄ := by
  cases n with
  | zero =>
    vcgen [finishDiscard, eraseToSeparator_marker_spec left label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost, sub_eq_add_neg]
  | succ n =>
    vcgen [finishDiscard, eraseToSeparator_spec n left label (origin - 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
      List.replicate_succ, sub_eq_add_neg, add_assoc]
    all_goals lia

/--
Starting just after `n` overwritten suffix symbols, this program erases those symbols and their
preceding separator. It finishes `n + 1` cells to the left of the starting position, uses exactly `n
+ 1` head moves, and leaves the prefix unchanged.
-/
theorem finishDiscard_correct (n : ℕ) (left : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor
      (List.replicate n (.inl (default : Symbol)) ++ (.inr 0) :: left) []) :
    Runs (finishDiscard tm) s (cursor left []) (s.headPos - (n + 1 : ℕ)) (n + 1) := by
  apply Spec.runs
  vcgen [finishDiscard_spec n left s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`discardRight tm` is a Turing machine program that starts on a separator and removes it and the
entire suffix to its right. It first overwrites that suffix with ordinary symbols, then erases
backward to the separator so that extra separators in the suffix cause no ambiguity. It finishes at
the starting coordinate, now blank, and preserves all symbols to its left.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def discardRight (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  moveₜ .Right
  fillRight tm
  finishDiscard tm

/-- Removing the suffix preserves the prefix and returns to the separator's former position. -/
@[spec] theorem discardRight_spec (left right : List (Extended Symbol 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor left ((.inr 0) :: right)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      discardRight tm
    ⦃ fun _ cost final => final.config = ⟨label, cursor left []⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * right.length + 2 ⦄ := by
  vcgen [discardRight, fillRight_spec ((.inr 0) :: left) right label (origin + 1) (elapsed + 1),
    finishDiscard_spec right.length left label (origin + 1 + right.length)
      (elapsed + 1 + right.length)]
  all_goals simp_all [TMState.move, TMState.moveCost]
  all_goals lia

/--
Starting on the displayed separator, the discard program erases that separator and all of `right`,
preserving `left`. It returns to the separator's coordinate, preserves the control state, and uses
exactly `2 * right.length + 2` head moves.
-/
theorem discardRight_correct (left right : List (Extended Symbol 1)) (s : TMState tm)
    (hs : s.config.BiTape = cursor left ((.inr 0) :: right)) :
    Runs (discardRight tm) s (cursor left []) s.headPos (2 * right.length + 2) := by
  apply Spec.runs
  vcgen [discardRight_spec left right s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
`firstWord tm` is a Turing machine program that starts at the beginning of a word, keeps the
ordinary symbols before the first separator, and erases that separator and everything after it. It
finishes at the original head coordinate, with the retained symbols still tagged by `.inl`. A
missing separator leaves the original word intact, and additional separators in the suffix are
erased.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def firstWord (tm : SingleTapeTM (Extended Symbol 1)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekSeparator tm
  discardRight tm
  seekLeftEnd tm

/-- Keeping the first word restores the head and takes at most twice the input length plus four. -/
@[spec] theorem firstWord_spec (input : List (Extended Symbol 1)) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      firstWord tm
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.mk₁ ((Alphabet.firstWord input).map .inl)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * input.length + 4 ⦄ := by
  have hlen := Alphabet.lengths_firstWord_afterMarker_le input
  vcgen [firstWord, seekSeparator_spec [] input label origin elapsed,
    discardRight_spec ((Alphabet.firstWord input).reverse.map .inl) (Alphabet.afterMarker input)
      label (origin + (Alphabet.firstWord input).length)
      (elapsed + (Alphabet.firstWord input).length),
    seekLeftEnd_spec ((Alphabet.firstWord input).reverse.map Sum.inl) [] label
      (origin + (Alphabet.firstWord input).length)
      (elapsed + (Alphabet.firstWord input).length + 2 * (Alphabet.afterMarker input).length + 2)]
  all_goals simp_all [List.map_reverse, cursor_start]
  all_goals lia

/--
The first-word program computes the ordinary prefix before the first separator, leaving that prefix
tagged by `.inl` on the tape. For every input it restores the starting head coordinate, preserves
the control state, and uses at most `2 * input.length + 4` head moves.
-/
theorem firstWord_computes :
    Computes (firstWord tm) (fun input => (Alphabet.firstWord input).map .inl)
      (fun input => 2 * input.length + 4) := by
  intro input s hs
  obtain ⟨cost, final, hc, hf, hh, hb⟩ :
      ∃ cost final, Completes (firstWord tm) s cost final ∧
        final.config = ⟨s.config.state, BiTape.mk₁ ((Alphabet.firstWord input).map .inl)⟩ ∧
        final.headPos = s.headPos ∧ cost.steps ≤ 2 * input.length + 4 := by
    apply Spec.completes
    vcgen [firstWord_spec input s.config.state s.headPos 0]
    all_goals
      cases hcfg : s.config
      simp_all
  exact ⟨cost.steps, ⟨cost, final, hc, hf, hh, rfl⟩, hb⟩

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
