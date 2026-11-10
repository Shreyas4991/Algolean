/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Writing

/-!
# Making room for the symbols of an encoding

* `shiftRight` shifts a word one cell to the right and leaves a blank at its old starting cell.
* The alphabet comparisons are fixed once with the program and cover its finite alphabet.
* Its correctness proof preserves the arbitrary contents beyond the blank to the left.

The serializer uses this shift to replace each input symbol with its fixed, nonempty code word.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private def shiftSymbolRight (symbol : Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right
  tape ←ₜ some symbol
  moveₜ .Left
  moveₜ .Left

private theorem shiftSymbolRight_correct (left : StackTape Symbol) (symbol : Symbol)
    (word : List Symbol) (tail : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = (segment (StackTape.cons none left) (symbol :: word) tail).mirror) :
    Runs (shiftSymbolRight (tm := tm) symbol) s
      (segment (StackTape.cons none (StackTape.cons (some symbol) left)) word tail).mirror
      (s.headPos - 1) 3 := by
  refine ⟨_, _, ⟨5, rfl⟩, ?_, ?_, ?_⟩
  · cases word <;>
      simp [TMQuery.step, hs, Copying.segment, BiTape.segment, BiTape.mirror, BiTape.write,
        BiTape.moveLeft, BiTape.moveRight]
  · simp [TMQuery.step, sub_eq_add_neg, add_assoc]
  · rfl

private def shiftRightLoop (symbols : List Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    select symbols (fun symbol => .tapeIs (some symbol)) (shiftSymbolRight (tm := tm))

private theorem shiftRightLoop_correct (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (left : StackTape Symbol) (word : List Symbol)
    (tail : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = (segment (StackTape.cons none left) word tail).mirror) :
    Runs (shiftRightLoop (tm := tm) symbols) s
      (segment (StackTape.cons none (stackAppend word.reverse left)) [] tail).mirror
      (s.headPos - word.length) (3 * word.length) := by
  induction word generalizing left s with
  | nil => simp [shiftRightLoop, hs]
  | cons symbol word ih =>
    unfold shiftRightLoop
    apply runs_while_step (by simp [hs])
    have hb : Runs (select symbols (fun symbol => .tapeIs (some symbol))
        (shiftSymbolRight (tm := tm))) s
        (segment (StackTape.cons none (StackTape.cons (some symbol) left)) word tail).mirror
        (s.headPos - 1) 3 := by
      obtain ⟨cost, final, hc, ht, hp, hm⟩ :=
        shiftSymbolRight_correct left symbol word tail s hs
      exact ⟨cost, final, select_correct _ _ _ symbol s final cost (hcover symbol)
        (by intro candidate; simp [hs, eq_comm]) hc, ht, hp, hm⟩
    have hr := hb.seq (q := shiftRightLoop symbols)
      (second := (segment (StackTape.cons none (stackAppend (symbol :: word).reverse left)) []
        tail).mirror)
      (pos₂ := s.headPos - (symbol :: word).length) (time₂ := 3 * word.length) (by
        intro middle ht hp
        convert ih (StackTape.cons (some symbol) left) middle
          (congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
          simp [List.reverse_cons, stackAppend_append, hp, sub_eq_add_neg,
            add_comm, add_left_comm])
    simpa [shiftRightLoop, Nat.mul_add, Nat.add_comm] using hr

/--
This shifts the word under the head one cell to the right. A blank must separate it from the
region to its left. The head finishes on the blank at the word's former starting coordinate.
The fixed list `symbols` determines all alphabet comparisons.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def shiftRight (tm : SingleTapeTM Symbol) (symbols : List Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Left
  shiftRightLoop symbols
  moveₜ .Right

/-- Shifting preserves the word and the left region and uses `4 * word.length + 2` head moves. -/
theorem shiftRight_correct (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (left : StackTape Symbol) (word : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons none left) word StackTape.nil) :
    Runs (shiftRight tm symbols) s
      (segment (StackTape.cons none left) [] (StackTape.mapSome word))
      s.headPos (4 * word.length + 2) := by
  have hr := seekRightBlank_segment (StackTape.cons none left) word StackTape.nil s hs
  have hm := hr.append_move .Left
  have hl := hm.seq (q := shiftRightLoop symbols)
    (second := (segment (StackTape.cons none (StackTape.mapSome word)) [] left).mirror)
    (pos₂ := s.headPos - 1) (time₂ := 3 * word.length) (by
      intro middle ht hp
      have htape : middle.config.BiTape =
          (segment (StackTape.cons none StackTape.nil) word.reverse left).mirror := by
        have h := congrArg SingleTapeTM.Cfg.BiTape ht
        cases hw : word.reverse <;>
          simpa [hw, Copying.segment, BiTape.segment, BiTape.mirror, BiTape.moveLeft] using h
      have h := shiftRightLoop_correct symbols hcover StackTape.nil word.reverse left middle htape
      convert h using 1 <;>
        simp [hp, sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
  have hf := hl.append_move .Right
  convert hf using 1
  · simp [shiftRight, bind_assoc]
  · simp [Copying.segment, BiTape.segment, BiTape.mirror, BiTape.moveRight]
  · simp [sub_eq_add_neg]
  · lia


/--
This machine template writes a fixed word while moving left after each symbol. The containing
machine fixes the word when including the template and uses it for every input length.
-/
def writeLeft (tm : SingleTapeTM Symbol) : List Symbol → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: word => do [TMQuery tm]
    tape ←ₜ some symbol
    moveₜ .Left
    writeLeft tm word

/-- Writing left across blanks places the reversed word just to the right of the head. -/
theorem writeLeft_correct (word : List Symbol) (left right : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.blanks word.length left) [] right) :
    Runs (writeLeft tm word) s
      (segment left [] (stackAppend word.reverse right))
      (s.headPos - word.length) word.length := by
  induction word generalizing right s with
  | nil =>
    simp only [writeLeft, List.reverse_nil, List.length_nil, StackTape.prepend,
      StackTape.blanks] at hs ⊢
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    rw [← hs]
  | cons symbol word ih =>
    have hw : Runs (do
        FreeM.lift (.write (some symbol))
        FreeM.lift (.move .Left)) s
        (segment (StackTape.blanks word.length left) [] (StackTape.cons (some symbol) right))
        (s.headPos - 1) 1 := by
      simpa [hs, Copying.segment, BiTape.segment, BiTape.write, BiTape.moveLeft,
        StackTape.blanks_cons, sub_eq_add_neg] using
        (write_correct s (some symbol)).append_move .Left
    have hr := hw.seq (q := writeLeft tm word)
      (second := segment left [] (stackAppend (symbol :: word).reverse right))
      (pos₂ := s.headPos - (symbol :: word).length) (time₂ := word.length) (by
        intro middle ht hp
        convert ih (StackTape.cons (some symbol) right) middle
          (congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
          simp [List.reverse_cons, stackAppend_append, hp, sub_eq_add_neg,
            add_comm, add_left_comm])
    simpa [writeLeft, bind_assoc, Nat.add_comm] using hr

private def widen (symbols : List Symbol) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | k + 1 => do [TMQuery tm]
    moveₜ .Right
    shiftRight tm symbols
    widen symbols k

private theorem widen_correct (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (k : Nat) (left : StackTape Symbol) (suffix : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment left [] (StackTape.mapSome suffix)) :
    Runs (widen (tm := tm) symbols k) s
      (segment (StackTape.blanks k left) [] (StackTape.mapSome suffix))
      (s.headPos + k) (k * (4 * suffix.length + 3)) := by
  induction k generalizing left s with
  | zero =>
    simp only [widen, StackTape.blanks, Nat.cast_zero, add_zero, Nat.zero_mul]
    refine ⟨0, s, completes_pure s, ?_, rfl, rfl⟩
    change s.config = {s.config with BiTape := segment left [] (StackTape.mapSome suffix)}
    rw [← hs]
  | succ k ih =>
    have hm : Runs (FreeM.lift (.move .Right)) s
        (segment (StackTape.cons none left) suffix StackTape.nil) (s.headPos + 1) 1 := by
      simpa [hs] using move_correct s .Right
    have hshift := hm.seq (q := shiftRight tm symbols)
      (second := segment (StackTape.cons none left) [] (StackTape.mapSome suffix))
      (pos₂ := s.headPos + 1) (time₂ := 4 * suffix.length + 2) (by
        intro middle ht hp
        simpa [hp] using shiftRight_correct symbols hcover left suffix middle
          (congrArg SingleTapeTM.Cfg.BiTape ht))
    have hr := hshift.seq (q := widen symbols k)
      (second := segment (StackTape.blanks (k + 1) left) [] (StackTape.mapSome suffix))
      (pos₂ := s.headPos + (k + 1)) (time₂ := k * (4 * suffix.length + 3)) (by
        intro middle ht hp
        simpa [hp, add_assoc, add_comm, add_left_comm] using ih (StackTape.cons none left) middle
          (congrArg SingleTapeTM.Cfg.BiTape ht))
    have htime : (k + 1) * (4 * suffix.length + 3) =
        1 + (4 * suffix.length + 2) + k * (4 * suffix.length + 3) := by
      rw [Nat.add_mul, Nat.one_mul]
      lia
    simpa only [widen, bind_assoc, htime, Nat.cast_add, Nat.cast_one] using hr

/--
This machine template inserts a fixed word just beyond the blank under the head. It shifts the
word already to the right to make room, then returns to the same blank. The containing machine
fixes the inserted word and alphabet comparisons once, independently of every runtime input.
-/
def insertAfterBlank (tm : SingleTapeTM Symbol) (symbols word : List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  widen symbols word.length
  writeLeft tm word.reverse

/-- Inserting preserves both neighboring regions and takes linearly many moves in their size. -/
theorem insertAfterBlank_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (left : StackTape Symbol) (suffix : List Symbol)
    (s : TMState tm) (hs : s.config.BiTape = segment left [] (StackTape.mapSome suffix)) :
    Runs (insertAfterBlank tm symbols word) s
      (segment left [] (StackTape.mapSome (word ++ suffix))) s.headPos
      (word.length * (4 * suffix.length + 3) + word.length) := by
  have hw := widen_correct symbols hcover word.length left suffix s hs
  have hr := hw.seq (q := writeLeft tm word.reverse)
    (second := segment left [] (StackTape.mapSome (word ++ suffix)))
    (pos₂ := s.headPos) (time₂ := word.length) (by
      intro middle ht hp
      convert writeLeft_correct word.reverse left (StackTape.mapSome suffix) middle
        (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
        simp [hp])
  simpa [insertAfterBlank] using hr


/--
This machine template replaces the symbol under the head with a fixed nonempty word, leaving
one blank between that word and the unprocessed symbols to its left. The head then moves to
those symbols. There must already be a blank just to the right of the starting cell.
The containing machine fixes the replacement word and alphabet comparisons once for all inputs.
-/
def replaceBeforeBlank (tm : SingleTapeTM Symbol) (symbols word : List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right
  widen symbols word.tail.length
  writeLeft tm word.reverse
  moveₜ .Left

/-- Replacing preserves both neighboring words and moves to the next symbol on the left. -/
theorem replaceBeforeBlank_correct (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (first : Symbol) (rest : List Symbol)
    (symbol : Symbol) (remaining suffix : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape =
      (segment (StackTape.cons none (StackTape.mapSome suffix))
        (symbol :: remaining) StackTape.nil).mirror) :
    Runs (replaceBeforeBlank tm symbols (first :: rest)) s
      (segment (StackTape.cons none (StackTape.mapSome ((first :: rest) ++ suffix)))
        remaining StackTape.nil).mirror
      (s.headPos - 1) (rest.length * (4 * suffix.length + 3) + (first :: rest).length + 2) := by
  have hm : Runs (do
      FreeM.lift (.write none)
      FreeM.lift (.move .Right)) s
      (segment (StackTape.cons none (StackTape.mapSome remaining)) [] (StackTape.mapSome suffix))
      (s.headPos + 1) 1 := by
    simpa [hs, Copying.segment, BiTape.segment, BiTape.mirror, BiTape.write, BiTape.moveRight] using
      (write_correct s none).append_move .Right
  have hw := hm.seq (q := widen symbols rest.length)
    (second := segment (StackTape.blanks (first :: rest).length (StackTape.mapSome remaining)) []
      (StackTape.mapSome suffix))
    (pos₂ := s.headPos + 1 + rest.length) (time₂ := rest.length * (4 * suffix.length + 3)) (by
      intro middle ht hp
      simpa [hp] using widen_correct symbols hcover rest.length
        (StackTape.cons none (StackTape.mapSome remaining)) suffix middle
        (congrArg SingleTapeTM.Cfg.BiTape ht))
  have hf := hw.seq (q := writeLeft tm (first :: rest).reverse)
    (second := segment (StackTape.mapSome remaining) []
      (StackTape.mapSome ((first :: rest) ++ suffix)))
    (pos₂ := s.headPos) (time₂ := (first :: rest).length) (by
      intro middle ht hp
      convert writeLeft_correct (first :: rest).reverse (StackTape.mapSome remaining)
        (StackTape.mapSome suffix) middle
        (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
        simp [hp, sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
  have hl := hf.append_move .Left
  convert hl using 1
  · simp [replaceBeforeBlank, bind_assoc]
  · cases remaining <;>
      simp [Copying.segment, BiTape.segment, BiTape.mirror, BiTape.moveLeft]
  · simp [sub_eq_add_neg]
  · lia

end Algolean.Algorithms.SingleTapeTuringMachines
