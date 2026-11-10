/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Augmented
public import Algolean.Algorithms.SingleTapeTuringMachines.Erasing
public import Algolean.Algorithms.SingleTapeTuringMachines.Gaps
public import Algolean.Problems.Certificates

/-!
# Removing the extra symbols from a padded certificate

The verifier receives the original input, a separator, and a padded certificate. The program
keeps the original input and separator and moves the recovered certificate next to them. It
erases the unused suffix. A missing ending or an incomplete entry gives an empty output word.
Everything after the ending is ignored, including additional separators. The two certificate
symbols and all instructions are fixed independently of the input length.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.CertificatePadding

open Cslib Cslib.Turing TMQuery Alphabet
open scoped TMQuery

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

/-- This is the word that should be passed to the original verifier after removing padding. -/
def result (next stop : Γ) (word : List (Extended Γ 1)) : List (Extended Γ 1) :=
  match Problems.CertificatePadding.decode next stop (Alphabet.firstWord (afterMarker word)) with
  | none => []
  | some certificate => (wordPair Γ).encode (Alphabet.firstWord word, certificate)

omit [Fintype Γ] in
/-- On a padded input-certificate pair, successful decoding gives the original pair. -/
theorem result_wordPair (next stop : Γ) (input word : List Γ) :
    result next stop ((wordPair Γ).encode (input, word)) =
      match Problems.CertificatePadding.decode next stop word with
      | none => []
      | some certificate => (wordPair Γ).encode (input, certificate) := by
  simp only [result, wordPair_encode, afterMarker_append_marker, firstWord_append_marker]
  have hfirst (word : List Γ) :
      Alphabet.firstWord (word.map (Sum.inl : Γ → Extended Γ 1)) = word := by
    induction word <;> simp_all
  rw [hfirst]
  rfl

private def separated (leftWord : List (Extended Γ 1)) (gap : Nat)
    (remaining : List (Extended Γ 1)) :
    BiTape (Extended Γ 1) where
  head := remaining.head?
  left := StackTape.blanks gap (StackTape.mapSome leftWord)
  right := StackTape.mapSome remaining.tail

omit [Fintype Γ] [DecidableEq Γ] in
private theorem erase_advance_separated (leftWord : List (Extended Γ 1)) (gap : Nat)
    (symbol : Extended Γ 1) (remaining : List (Extended Γ 1)) :
    ((separated leftWord gap (symbol :: remaining)).write none).moveRight =
      separated leftWord (gap + 1) remaining := by
  cases remaining <;> simp [separated, BiTape.write, BiTape.moveRight]

variable {tm : SingleTapeTM (Extended Γ 1)} [DecidableEq tm.State]

private theorem eraseRight_separated (leftWord : List (Extended Γ 1)) (gap : Nat)
    (remaining : List (Extended Γ 1)) (s : TMState tm)
    (htape : s.config.BiTape = separated leftWord gap remaining) :
    Runs (eraseRight tm) s (separated leftWord (remaining.length + gap) [])
      (s.headPos + remaining.length) remaining.length := by
  induction remaining generalizing gap s with
  | nil => simp [eraseRight, htape, separated]
  | cons symbol remaining ih =>
    unfold eraseRight
    apply runs_while_step (by simp [htape, separated])
    have he : Runs (eraseAndMove tm) s (separated leftWord (gap + 1) remaining)
        (s.headPos + 1) 1 := by
      simpa only [eraseAndMove, htape, erase_advance_separated, Dir.offset, Nat.zero_add] using
        (write_correct s none).append_move .Right
    have hr := he.seq (q := eraseRight tm) (by
      intro middle hmiddle hpos
      simpa [hpos, Nat.add_assoc, add_assoc, add_comm, add_left_comm] using
        ih (gap + 1) middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
    simpa [eraseRight, eraseAndMove, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

private def finish (keep : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseRight tm
  seekLeftOccupied tm
  if keep then
    seekLeftEnd tm
  else
    eraseLeft tm
    moveₜ .Right

private theorem finish_correct (keep : Bool) (first : Extended Γ 1) (leftWord : List (Extended Γ 1))
    (gap : Nat) (remaining : List (Extended Γ 1)) (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) gap remaining) :
    Runs (finish (tm := tm) keep) s
      (if keep then BiTape.mk₁ (first :: leftWord).reverse else BiTape.nil)
      (s.headPos - (gap + (first :: leftWord).length : Nat))
      (2 * remaining.length + gap + (first :: leftWord).length + 2) := by
  have he := eraseRight_separated (first :: leftWord) gap remaining s htape
  have hs := he.seq (q := seekLeftOccupied tm)
    (second := cursor leftWord [first])
    (pos₂ := s.headPos - (gap + 1 : Nat)) (time₂ := remaining.length + gap + 1) (by
      intro middle hmiddle hpos
      have hm : middle.config.BiTape =
          ⟨none, StackTape.blanks (remaining.length + gap)
            (StackTape.cons (some first) (StackTape.mapSome leftWord)), StackTape.nil⟩ := by
        simpa [separated] using congrArg SingleTapeTM.Cfg.BiTape hmiddle
      have hr := seekLeftOccupied_correct (remaining.length + gap) first
        (StackTape.mapSome leftWord) StackTape.nil middle hm
      convert hr using 1 <;>
        simp [cursor, hpos, sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
  cases keep with
  | true =>
    have hr := hs.seq (q := seekLeftEnd tm)
      (second := BiTape.mk₁ (first :: leftWord).reverse)
      (pos₂ := s.headPos - (gap + (first :: leftWord).length : Nat))
      (time₂ := leftWord.length + 2) (by
        intro middle hmiddle hpos
        have ht := congrArg SingleTapeTM.Cfg.BiTape hmiddle
        have h := seekLeftEnd_correct leftWord [first] middle ht
        convert h using 1 <;>
          simp [cursor_start, List.reverse_cons, hpos, sub_eq_add_neg,
            add_assoc, add_comm])
    simpa [finish, two_mul, add_assoc, add_comm, add_left_comm] using hr
  | false =>
    have hr := hs.seq (q := do eraseLeft tm; FreeM.lift (.move .Right))
      (second := BiTape.nil)
      (pos₂ := s.headPos - (gap + (first :: leftWord).length : Nat))
      (time₂ := leftWord.length + 2) (by
        intro middle hmiddle hpos
        have ht := congrArg SingleTapeTM.Cfg.BiTape hmiddle
        have h := (eraseLeft_correct leftWord first middle ht).append_move .Right
        convert h using 1 <;>
          simp [hpos, BiTape.moveRight, BiTape.nil, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm])
    simpa [finish, two_mul, add_assoc, add_comm, add_left_comm] using hr

private def copySymbol (symbol : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ some (.inr 0)
  moveₜ .Left
  seekLeftOccupied tm
  moveₜ .Right
  tape ←ₜ some (.inl symbol)
  moveₜ .Right
  seekRightOccupied tm
  eraseAndMove tm

private theorem copySymbol_correct (symbol : Γ) (first : Extended Γ 1)
    (leftWord remaining : List (Extended Γ 1)) (gap : Nat) (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) (gap + 1)
      (.inl symbol :: remaining)) :
    Runs (copySymbol (tm := tm) symbol) s
      (separated (.inl symbol :: first :: leftWord) (gap + 1) remaining)
      (s.headPos + 1) (2 * gap + 5) := by
  have hfirst : Runs (do FreeM.lift (.write (some (.inr 0))); FreeM.lift (.move .Left)) s
      ⟨none, StackTape.blanks gap (StackTape.mapSome (first :: leftWord)),
        StackTape.cons (some (.inr 0)) (StackTape.mapSome remaining)⟩
      (s.headPos - 1) 1 := by
    simpa [htape, separated, BiTape.write, BiTape.moveLeft, sub_eq_add_neg] using
      (write_correct s (some (.inr 0))).append_move .Left
  have hleft := hfirst.seq (q := seekLeftOccupied tm)
    (second := ⟨some first, StackTape.mapSome leftWord,
      StackTape.blanks (gap + 1) (StackTape.cons (some (.inr 0))
        (StackTape.mapSome remaining))⟩)
    (pos₂ := s.headPos - (gap + 2 : Nat)) (time₂ := gap + 1) (by
      intro middle hmiddle hpos
      have h := seekLeftOccupied_correct gap first (StackTape.mapSome leftWord)
        (StackTape.cons (some (.inr 0)) (StackTape.mapSome remaining)) middle
        (by simpa using congrArg SingleTapeTM.Cfg.BiTape hmiddle)
      convert h using 1; simp [hpos, sub_eq_add_neg, add_comm, add_left_comm])
  have hwrite := hleft.seq
    (q := do FreeM.lift (.move .Right); FreeM.lift (.write (some (.inl symbol))))
    (second := ⟨some (.inl symbol), StackTape.mapSome (first :: leftWord),
      StackTape.blanks gap (StackTape.cons (some (.inr 0)) (StackTape.mapSome remaining))⟩)
    (pos₂ := s.headPos - (gap + 1 : Nat)) (time₂ := 1) (by
      intro middle hmiddle hpos
      simpa [hmiddle, BiTape.moveRight, BiTape.write, hpos, sub_eq_add_neg,
        add_assoc, add_comm, add_left_comm] using
        (move_correct middle .Right).append_write (some (.inl symbol)))
  let stack := StackTape.blanks gap
    (StackTape.cons (some (.inr 0)) (StackTape.mapSome remaining))
  have hmove := hwrite.append_move .Right
  have hright := hmove.seq (q := seekRightOccupied tm)
    (second := ⟨some (.inr 0),
      StackTape.blanks gap (StackTape.mapSome (.inl symbol :: first :: leftWord)),
      StackTape.mapSome remaining⟩)
    (pos₂ := s.headPos) (time₂ := gap) (by
      intro middle hmiddle hpos
      have h := seekRightOccupied_stack gap (.inr 0)
        (StackTape.mapSome (.inl symbol :: first :: leftWord))
        (StackTape.mapSome remaining) middle
        (by simpa [BiTape.moveRight, stack] using congrArg SingleTapeTM.Cfg.BiTape hmiddle)
      convert h using 1; simp [hpos, sub_eq_add_neg, add_comm, add_left_comm])
  have hr := hright.seq (q := eraseAndMove tm)
    (second := separated (.inl symbol :: first :: leftWord) (gap + 1) remaining)
    (pos₂ := s.headPos + 1) (time₂ := 1) (by
      intro middle hmiddle hpos
      have ht : middle.config.BiTape =
          separated (.inl symbol :: first :: leftWord) gap (.inr 0 :: remaining) := by
        simpa [separated] using congrArg SingleTapeTM.Cfg.BiTape hmiddle
      simpa [eraseAndMove, ht, hpos, erase_advance_separated] using
        (write_correct middle none).append_move .Right)
  simpa [copySymbol, two_mul, add_assoc, add_comm, add_left_comm] using hr

private def body (symbols : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseAndMove tm
  select symbols (fun symbol => .tapeIs (some (.inl symbol))) (copySymbol (tm := tm))

private def process (symbols : List Γ) (next stop : Γ) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (tape =ₜ some (.inl next)) do
    body symbols
  ifₜ tape =ₜ some (.inl stop) then
    finish true
  else
    finish false

private theorem body_correct (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next symbol : Γ) (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1))
    (gap : Nat) (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) gap
      (.inl next :: .inl symbol :: remaining)) :
    Runs (body (tm := tm) symbols) s
      (separated (.inl symbol :: first :: leftWord) (gap + 1) remaining)
      (s.headPos + 2) (2 * gap + 6) := by
  have he : Runs (eraseAndMove tm) s
      (separated (first :: leftWord) (gap + 1) (.inl symbol :: remaining))
      (s.headPos + 1) 1 := by
    simpa only [eraseAndMove, htape, erase_advance_separated, Dir.offset, Nat.zero_add] using
      (write_correct s none).append_move .Right
  have hr := he.seq
    (q := select symbols (fun symbol => .tapeIs (some (.inl symbol))) (copySymbol (tm := tm)))
    (second := separated (.inl symbol :: first :: leftWord) (gap + 1) remaining)
    (pos₂ := s.headPos + 2) (time₂ := 2 * gap + 5) (by
      intro middle hmiddle hpos
      obtain ⟨cost, final, hc, ht, hp, hs⟩ := copySymbol_correct symbol first leftWord remaining gap
        middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle)
      refine ⟨cost, final, select_correct _ _ _ symbol middle final cost (hsymbols symbol) ?_ hc,
        ht, ?_, hs⟩
      · intro candidate
        simp [hmiddle, separated, eq_comm]
      · simpa [hpos, add_assoc] using hp)
  simpa only [body, show 1 + (2 * gap + 5) = 2 * gap + 6 by lia] using hr

private theorem body_missing_symbol (symbols : List Γ) (next : Γ)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) gap (.inl next :: remaining))
    (hmissing : ∀ symbol : Γ, remaining.head? ≠ some (.inl symbol)) :
    Runs (body (tm := tm) symbols) s (separated (first :: leftWord) (gap + 1) remaining)
      (s.headPos + 1) 1 := by
  have he : Runs (eraseAndMove tm) s
      (separated (first :: leftWord) (gap + 1) remaining) (s.headPos + 1) 1 := by
    simpa only [eraseAndMove, htape, erase_advance_separated, Dir.offset, Nat.zero_add] using
      (write_correct s none).append_move .Right
  have hr := he.seq
    (q := select symbols (fun symbol => .tapeIs (some (.inl symbol))) (copySymbol (tm := tm)))
    (second := separated (first :: leftWord) (gap + 1) remaining)
    (pos₂ := s.headPos + 1) (time₂ := 0) (by
      intro middle hmiddle hpos
      refine ⟨0, middle, select_none _ _ _ middle ?_, ?_, hpos, rfl⟩
      · intro symbol _
        simp [hmiddle, separated, hmissing symbol]
      · simp [hmiddle])
  simpa [body] using hr

private theorem process_exit (symbols : List Γ) (next stop : Γ) (keep : Bool)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (s : TMState tm) (htape : s.config.BiTape = separated (first :: leftWord) gap remaining)
    (hnext : remaining.head? ≠ some (.inl next))
    (hstop : decide (remaining.head? = some (.inl stop)) = keep) :
    Runs (process (tm := tm) symbols next stop) s
      (if keep then BiTape.mk₁ (first :: leftWord).reverse else BiTape.nil)
      (s.headPos - (gap + (first :: leftWord).length : Nat))
      (2 * remaining.length + gap + (first :: leftWord).length + 2) := by
  have hf := finish_correct keep first leftWord gap remaining s htape
  have hb : Runs (branch (.tapeIs (some (.inl stop))) (finish (tm := tm) true) (finish false)) s
      (if keep then BiTape.mk₁ (first :: leftWord).reverse else BiTape.nil)
      (s.headPos - (gap + (first :: leftWord).length : Nat))
      (2 * remaining.length + gap + (first :: leftWord).length + 2) := by
    apply Runs.branch
    cases keep with
    | false =>
      have hn := of_decide_eq_false hstop
      simpa [htape, separated, hn] using hf
    | true =>
      have hy := of_decide_eq_true hstop
      simpa [htape, separated, hy] using hf
  have hcond : (TMCondition.tapeIs (tm := tm) (some (.inl next))).eval s.config = false := by
    simp [htape, separated, hnext]
  simpa [process] using hb.prepend
    (completes_while_false (.tapeIs (some (.inl next))) (body symbols) s hcond) rfl

private def output (next stop : Γ) (leftWord remaining : List (Extended Γ 1)) :
    BiTape (Extended Γ 1) :=
  match Problems.CertificatePadding.decode next stop (Alphabet.firstWord remaining) with
  | none => BiTape.nil
  | some certificate => BiTape.mk₁ (leftWord.reverse ++ certificate.map .inl)

private def budget (leftWord : List (Extended Γ 1)) (gap : Nat)
    (remaining : List (Extended Γ 1)) : Nat :=
  (remaining.length + 1) * (2 * (leftWord.length + gap + remaining.length) + 6)

private theorem process_stopped (symbols : List Γ) (next stop : Γ)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (s : TMState tm) (htape : s.config.BiTape = separated (first :: leftWord) gap remaining)
    (hnext : remaining.head? ≠ some (.inl next)) :
    ∃ moves, Runs (process (tm := tm) symbols next stop) s
      (output next stop (first :: leftWord) remaining)
      (s.headPos - (gap + (first :: leftWord).length : Nat)) moves ∧
      moves ≤ budget (first :: leftWord) gap remaining := by
  let keep := decide (remaining.head? = some (.inl stop))
  have hd : Problems.CertificatePadding.decode next stop (Alphabet.firstWord remaining) =
      if keep then some [] else none := by
    cases remaining with
    | nil => simp [keep, Problems.CertificatePadding.decode]
    | cons tag rest =>
      cases tag with
      | inr marker => simp [keep, Problems.CertificatePadding.decode]
      | inl tag =>
        by_cases hs : tag = stop
        · subst tag
          simp [keep]
        · have hn : tag ≠ next := by simpa using hnext
          simp [keep, hs, Alphabet.firstWord_symbol,
            Problems.CertificatePadding.decode_other next stop tag hs hn]
  have hr := process_exit symbols next stop keep first leftWord remaining gap s htape hnext rfl
  refine ⟨2 * remaining.length + gap + (first :: leftWord).length + 2, ?_, ?_⟩
  · cases hk : keep <;> simpa [output, hd, hk] using hr
  · have hmul : 2 * ((first :: leftWord).length + gap + remaining.length) + 6 ≤
        budget (first :: leftWord) gap remaining := by
      exact Nat.le_mul_of_pos_left _ (by lia)
    exact (by lia : 2 * remaining.length + gap + (first :: leftWord).length + 2 ≤
      2 * ((first :: leftWord).length + gap + remaining.length) + 6).trans hmul

private theorem process_invalid (symbols : List Γ) (next stop : Γ) (hne : next ≠ stop)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) gap (.inl next :: remaining))
    (hmissing : ∀ symbol : Γ, remaining.head? ≠ some (.inl symbol)) :
    ∃ moves, Runs (process (tm := tm) symbols next stop) s
      (output next stop (first :: leftWord) (.inl next :: remaining))
      (s.headPos - (gap + (first :: leftWord).length : Nat)) moves ∧
      moves ≤ budget (first :: leftWord) gap (.inl next :: remaining) := by
  have hword : Alphabet.firstWord remaining = [] := by
    cases remaining with
    | nil => rfl
    | cons tag rest =>
      cases tag with
      | inl symbol => exact False.elim (hmissing symbol rfl)
      | inr marker => rfl
  obtain ⟨cost, middle, hc, hm, hp, hs⟩ :=
    body_missing_symbol symbols next first leftWord remaining gap s htape hmissing
  obtain ⟨moves, hr, hb⟩ := process_stopped symbols next stop first leftWord remaining (gap + 1)
    middle (congrArg SingleTapeTM.Cfg.BiTape hm) (hmissing next)
  have hseq := hr.prepend hc (by simp [hm])
  have hloop : Runs (process (tm := tm) symbols next stop) s
      (output next stop (first :: leftWord) remaining)
      (middle.headPos - (gap + 1 + (first :: leftWord).length : Nat))
      (cost.steps + moves) := by
    apply Runs.while_step_seq (by simp [htape, separated])
    simpa only [process, bind_assoc] using hseq
  refine ⟨cost.steps + moves, ?_, ?_⟩
  · convert hloop using 1
    · simp [output, hword, Problems.CertificatePadding.decode, hne]
    · simp [hp, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · let B := 2 * ((first :: leftWord).length + gap + (remaining.length + 1)) + 6
    have hbound : moves ≤ (remaining.length + 1) * B := by
      simpa [budget, B, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
    have hB : 1 ≤ B := by dsimp [B]; lia
    have htotal := Nat.add_le_add (by simpa [hs] using hB) hbound
    rw [hs]
    apply htotal.trans
    simp only [budget, List.length_cons]
    dsimp [B]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    lia

private theorem process_correct (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next stop : Γ) (hne : next ≠ stop) (first : Extended Γ 1)
    (leftWord remaining : List (Extended Γ 1)) (gap : Nat) (s : TMState tm)
    (htape : s.config.BiTape = separated (first :: leftWord) gap remaining) :
    ∃ moves, Runs (process (tm := tm) symbols next stop) s
      (output next stop (first :: leftWord) remaining)
      (s.headPos - (gap + (first :: leftWord).length : Nat)) moves ∧
      moves ≤ budget (first :: leftWord) gap remaining := by
  by_cases hnext : remaining.head? ≠ some (.inl next)
  · exact process_stopped symbols next stop first leftWord remaining gap s htape hnext
  · have hhead : remaining.head? = some (.inl next) := by simpa using hnext
    cases remaining with
    | nil => simp at hhead
    | cons tag rest =>
      have htag : tag = .inl next := by simpa using hhead
      subst tag
      cases rest with
      | nil => exact process_invalid symbols next stop hne first leftWord [] gap s htape (by simp)
      | cons symbol remaining =>
        cases symbol with
        | inr marker =>
          exact process_invalid symbols next stop hne first leftWord (.inr marker :: remaining)
            gap s htape (by simp)
        | inl symbol =>
          obtain ⟨cost, middle, hc, hm, hp, hs⟩ :=
            body_correct symbols hsymbols next symbol first leftWord remaining gap s htape
          obtain ⟨moves, hr, hb⟩ := process_correct symbols hsymbols next stop hne (.inl symbol)
            (first :: leftWord) remaining (gap + 1) middle (congrArg SingleTapeTM.Cfg.BiTape hm)
          have hseq := hr.prepend hc (by simp [hm])
          have hloop : Runs (process (tm := tm) symbols next stop) s
              (output next stop (.inl symbol :: first :: leftWord) remaining)
              (middle.headPos - (gap + 1 + (.inl symbol :: first :: leftWord).length : Nat))
              (cost.steps + moves) := by
            apply Runs.while_step_seq (by simp [htape, separated])
            simpa only [process, bind_assoc] using hseq
          refine ⟨cost.steps + moves, ?_, ?_⟩
          · convert hloop using 1
            · simp only [output, Alphabet.firstWord_symbol,
                Problems.CertificatePadding.decode_next next stop hne]
              cases Problems.CertificatePadding.decode next stop (Alphabet.firstWord remaining) <;>
                simp [List.reverse_cons, List.append_assoc]
            · simp [hp, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
              lia
          · let N := (first :: leftWord).length + gap +
              (.inl next :: .inl symbol :: remaining).length
            have hspan : (.inl symbol :: first :: leftWord).length + (gap + 1) +
                remaining.length = N := by simp only [N, List.length_cons]; lia
            have hbound : moves ≤ (remaining.length + 1) * (2 * N + 6) := by
              simpa only [budget, hspan] using hb
            have hbody : cost.steps ≤ 2 * N + 6 := by
              simp only [N, List.length_cons] at *
              lia
            apply (Nat.add_le_add hbody hbound).trans
            change (2 * N + 6) + (remaining.length + 1) * (2 * N + 6) ≤
              ((.inl next :: .inl symbol :: remaining).length + 1) * (2 * N + 6)
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
            lia
termination_by remaining.length

/--
This removes certificate padding from the word on the tape. The list `symbols` supplies the
finite symbol comparisons and must cover the alphabet. It is chosen once with the program,
independently of the input word and its length. A failed decoding gives an empty output.
Successful decoding retains the input and recovered certificate and discards the unused suffix.
-/
def unpad (tm : SingleTapeTM (Extended Γ 1)) (symbols : List Γ) (next stop : Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekSeparator tm
  moveₜ .Right
  process symbols next stop

/--
The fixed decoding program computes `result` on every word, including incorrectly written words.
It returns the head to its starting coordinate, preserves the control state, and uses at most
`8 * (n + 2) ^ 2` head moves on an input of length `n`.
-/
theorem unpad_computes (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next stop : Γ) (hne : next ≠ stop) :
    Computes (unpad tm symbols next stop) (result next stop)
      (fun word => 8 * (word.length + 2) ^ 2) := by
  intro word s htape
  have hp := (seekSeparator_correct [] word s (by simpa [cursor_start] using htape)).append_move
    .Right
  obtain ⟨cost, middle, hc, hm, hpos, hsteps⟩ := hp
  have hmid : middle.config.BiTape =
      separated (.inr 0 :: (Alphabet.firstWord word).reverse.map .inl) 0
        (afterMarker word) := by
    simpa [cursor, separated, BiTape.moveRight] using congrArg SingleTapeTM.Cfg.BiTape hm
  obtain ⟨moves, hr, hb⟩ := process_correct symbols hsymbols next stop hne (.inr 0)
    ((Alphabet.firstWord word).reverse.map .inl) (afterMarker word) 0 middle hmid
  have hseq := hr.prepend hc (by simp [hm])
  refine ⟨cost.steps + moves, ?_, ?_⟩
  · convert hseq using 1
    · simp [unpad, bind_assoc]
    · simp only [output, result]
      cases Problems.CertificatePadding.decode next stop
          (Alphabet.firstWord (afterMarker word)) <;>
        simp [wordPair_encode, List.reverse_cons, List.map_reverse, BiTape.mk₁, BiTape.nil]
    · simp [hpos, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · have hlength := lengths_firstWord_afterMarker_le word
    have hspan : (.inr 0 :: (Alphabet.firstWord word).reverse.map
          (Sum.inl : Γ → Extended Γ 1)).length + 0 + (afterMarker word).length ≤
        word.length + 1 := by
      simp only [List.length_cons, List.length_map, List.length_reverse, Nat.add_zero]
      lia
    have hmoves : moves ≤ (word.length + 1) * (2 * (word.length + 1) + 6) :=
      hb.trans (Nat.mul_le_mul (by lia) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hspan) 6))
    have hcost : cost.steps ≤ word.length + 1 := by
      lia
    calc
      cost.steps + moves ≤ (word.length + 1) +
          (word.length + 1) * (2 * (word.length + 1) + 6) := Nat.add_le_add hcost hmoves
      _ = (word.length + 1) * (2 * (word.length + 1) + 7) := by ring
      _ ≤ (word.length + 2) * (8 * (word.length + 2)) :=
        Nat.mul_le_mul (by lia) (by lia)
      _ = 8 * (word.length + 2) ^ 2 := by ring

private abbrev control (Γ : Type) [Fintype Γ] : SingleTapeTM (Extended Γ 1) where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This packages the certificate decoder as a polynomial-time Turing machine. The chosen finite
alphabet determines its symbol comparisons; all inputs run the same program.
-/
noncomputable def computer (next stop : Γ) (hne : next ≠ stop) :
    PolyTimeComputable (result next stop) := by
  classical
  apply Computes.polyTimeComputable (tm := control Γ)
    (p := unpad (control Γ) Finset.univ.toList next stop)
    (poly := 8 * (Polynomial.X + 2) ^ 2)
  simpa using unpad_computes (tm := control Γ) (Finset.univ.toList) (by simp) next stop hne

end Algolean.Algorithms.SingleTapeTuringMachines.CertificatePadding
