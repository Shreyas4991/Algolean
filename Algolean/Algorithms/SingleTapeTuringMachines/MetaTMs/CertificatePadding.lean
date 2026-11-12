/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Augmented
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Gaps
public import Algolean.Problems.SingleTapeTM.Encodings.Certificates

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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

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

private theorem eraseRight_separated_spec (leftWord : List (Extended Γ 1)) (gap : Nat)
    (remaining : List (Extended Γ 1)) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, separated leftWord gap remaining⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      eraseRight tm
    ⦃ fun _ cost final => final.config =
        ⟨label, separated leftWord (remaining.length + gap) []⟩ ∧
        final.headPos = origin + remaining.length ∧ cost.steps = elapsed + remaining.length ⦄ := by
  vcgen [eraseRight_segment_spec (StackTape.blanks gap (StackTape.mapSome leftWord))
    StackTape.nil remaining label origin elapsed]
  all_goals cases remaining
  all_goals simp_all [separated, BiTape.segment, ← StackTape.blanks_add, add_comm]

private def finish (keep : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseRight tm
  seekLeftOccupied tm
  if keep then
    seekLeftEnd tm
  else
    eraseLeft tm
    moveₜ .Right

private theorem finish_spec (keep : Bool) (first : Extended Γ 1)
    (leftWord : List (Extended Γ 1)) (gap : Nat) (remaining : List (Extended Γ 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, separated (first :: leftWord) gap remaining⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      finish (tm := tm) keep
    ⦃ fun _ cost final => final.config =
        ⟨label, if keep then BiTape.mk₁ (first :: leftWord).reverse else BiTape.nil⟩ ∧
        final.headPos = origin - (gap + (first :: leftWord).length : Nat) ∧
        cost.steps = elapsed + 2 * remaining.length + gap + (first :: leftWord).length + 2 ⦄ := by
  cases keep <;>
    vcgen [finish, eraseRight_separated_spec (first :: leftWord) gap remaining label origin elapsed,
      seekLeftOccupied_spec (remaining.length + gap) first
        (StackTape.mapSome leftWord) StackTape.nil
        label (origin + remaining.length) (elapsed + remaining.length),
      seekLeftEnd_spec leftWord [first] label (origin - (gap + 1 : Nat))
        (elapsed + 2 * remaining.length + gap + 1),
      eraseLeft_spec leftWord first label (origin - (gap + 1 : Nat))
        (elapsed + 2 * remaining.length + gap + 1)]
  all_goals simp_all [← cursor_start, separated, cursor, TMState.move, TMState.moveCost,
    BiTape.moveRight, BiTape.nil, List.reverse_cons, sub_eq_add_neg]
  all_goals lia

private def copySymbol (symbol : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ some (.inr 0)
  moveₜ .Left
  seekLeftOccupied tm
  moveₜ .Right
  tape ←ₜ some (.inl symbol)
  moveₜ .Right
  seekRightOccupied tm
  eraseAndMove tm

private theorem copySymbol_spec (symbol : Γ) (first : Extended Γ 1)
    (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, separated (first :: leftWord) (gap + 1) (.inl symbol :: remaining)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copySymbol (tm := tm) symbol
    ⦃ fun _ cost final => final.config =
        ⟨label, separated (.inl symbol :: first :: leftWord) (gap + 1) remaining⟩ ∧
        final.headPos = origin + 1 ∧ cost.steps = elapsed + 2 * gap + 5 ⦄ := by
  vcgen [copySymbol,
    seekLeftOccupied_spec gap first (StackTape.mapSome leftWord)
      (StackTape.cons (some (.inr 0)) (StackTape.mapSome remaining))
      label (origin - 1) (elapsed + 1),
    seekRightOccupied_stack_spec gap (.inr 0)
      (StackTape.mapSome (.inl symbol :: first :: leftWord)) (StackTape.mapSome remaining)
      label (origin - gap) (elapsed + gap + 4), eraseAndMove_spec]
  all_goals cases remaining
  all_goals simp_all [separated, TMState.write, TMState.move, TMState.moveCost,
    BiTape.write, BiTape.moveLeft, BiTape.moveRight, sub_eq_add_neg]
  all_goals lia

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

private theorem body_spec (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next symbol : Γ) (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1))
    (gap : Nat) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, separated (first :: leftWord) gap (.inl next :: .inl symbol :: remaining)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      body (tm := tm) symbols
    ⦃ fun _ cost final => final.config =
        ⟨label, separated (.inl symbol :: first :: leftWord) (gap + 1) remaining⟩ ∧
        final.headPos = origin + 2 ∧ cost.steps = elapsed + 2 * gap + 6 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  vcgen [body, eraseAndMove_spec,
    Spec.select_spec symbols (fun symbol => .tapeIs (some (.inl symbol)))
      (copySymbol (tm := tm)) symbol (hsymbols symbol)]
  constructor
  · intro candidate
    simp [TMState.move, TMState.write, hcfg, separated, BiTape.write, BiTape.moveRight,
      eq_comm]
  · vcgen [copySymbol_spec symbol first leftWord remaining gap label (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.write, TMState.moveCost, erase_advance_separated]
    all_goals lia

private theorem body_missing_symbol_spec (symbols : List Γ) (next : Γ)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (hmissing : ∀ symbol : Γ, remaining.head? ≠ some (.inl symbol))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, separated (first :: leftWord) gap (.inl next :: remaining)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      body (tm := tm) symbols
    ⦃ fun _ cost final => final.config =
        ⟨label, separated (first :: leftWord) (gap + 1) remaining⟩ ∧
        final.headPos = origin + 1 ∧ cost.steps = elapsed + 1 ⦄ := by
  vcgen [body, eraseAndMove_spec, Spec.select_none_spec]
  cases remaining <;> simp_all [TMState.move, TMState.write, TMState.moveCost,
    separated, BiTape.write, BiTape.moveRight]

private theorem process_exit_spec (symbols : List Γ) (next stop : Γ) (keep : Bool)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (hnext : remaining.head? ≠ some (.inl next))
    (hstop : decide (remaining.head? = some (.inl stop)) = keep)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, separated (first :: leftWord) gap remaining⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      process (tm := tm) symbols next stop
    ⦃ fun _ cost final => final.config =
        ⟨label, if keep then BiTape.mk₁ (first :: leftWord).reverse else BiTape.nil⟩ ∧
        final.headPos = origin - (gap + (first :: leftWord).length : Nat) ∧
        cost.steps = elapsed + 2 * remaining.length + gap + (first :: leftWord).length + 2 ⦄ := by
  cases keep <;>
    apply Std.WP.Triple.intro <;>
    rintro initial current ⟨hcfg, hpos, hsteps⟩ <;>
    vcgen [process, Spec.while_false_spec]
  all_goals
    refine ⟨by simp [hcfg, separated, hnext], ?_⟩
    dsimp only [binderNameHint]
    vcgen [finish_spec true first leftWord gap remaining label origin elapsed,
      finish_spec false first leftWord gap remaining label origin elapsed]
    all_goals simp_all [separated]

private def output (next stop : Γ) (leftWord remaining : List (Extended Γ 1)) :
    BiTape (Extended Γ 1) :=
  match Problems.CertificatePadding.decode next stop (Alphabet.firstWord remaining) with
  | none => BiTape.nil
  | some certificate => BiTape.mk₁ (leftWord.reverse ++ certificate.map .inl)

private def budget (leftWord : List (Extended Γ 1)) (gap : Nat)
    (remaining : List (Extended Γ 1)) : Nat :=
  (remaining.length + 1) * (2 * (leftWord.length + gap + remaining.length) + 6)

private theorem process_stopped_spec (symbols : List Γ) (next stop : Γ)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (hnext : remaining.head? ≠ some (.inl next))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, separated (first :: leftWord) gap remaining⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      process (tm := tm) symbols next stop
    ⦃ fun _ cost final => final.config = ⟨label, output next stop (first :: leftWord) remaining⟩ ∧
        final.headPos = origin - (gap + (first :: leftWord).length : Nat) ∧
        cost.steps ≤ elapsed + budget (first :: leftWord) gap remaining ⦄ := by
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
  have hbudget : 2 * remaining.length + gap + (first :: leftWord).length + 2 ≤
      budget (first :: leftWord) gap remaining := by
    have hmul : 2 * ((first :: leftWord).length + gap + remaining.length) + 6 ≤
        budget (first :: leftWord) gap remaining :=
      Nat.le_mul_of_pos_left _ (by lia)
    lia
  vcgen [process_exit_spec symbols next stop keep first leftWord remaining gap hnext rfl
    label origin elapsed]
  all_goals cases hk : keep
  all_goals simp_all [output]
  all_goals lia

private theorem process_invalid_spec (symbols : List Γ) (next stop : Γ) (hne : next ≠ stop)
    (first : Extended Γ 1) (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (hmissing : ∀ symbol : Γ, remaining.head? ≠ some (.inl symbol))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, separated (first :: leftWord) gap (.inl next :: remaining)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      process (tm := tm) symbols next stop
    ⦃ fun _ cost final => final.config =
        ⟨label, output next stop (first :: leftWord) (.inl next :: remaining)⟩ ∧
        final.headPos = origin - (gap + (first :: leftWord).length : Nat) ∧
        cost.steps ≤ elapsed + budget (first :: leftWord) gap (.inl next :: remaining) ⦄ := by
  have hword : Alphabet.firstWord remaining = [] := by
    cases remaining with
    | nil => rfl
    | cons tag rest =>
      cases tag with
      | inl symbol => exact False.elim (hmissing symbol rfl)
      | inr marker => rfl
  have hbudget : 1 + budget (first :: leftWord) (gap + 1) remaining ≤
      budget (first :: leftWord) gap (.inl next :: remaining) := by
    simp only [budget, List.length_cons]
    ring_nf
    lia
  apply Std.WP.Triple.intro
  rintro initial current hpre
  apply (Spec.while_step_seq_spec (loop := process (tm := tm) symbols next stop)
    (hloop := rfl) (post := _)).le_wp initial current
  have htest : (TMCondition.tapeIs (tm := tm)
      (some (.inl next))).eval current.config = true := by
    simp [hpre.1, separated]
  simp only [htest, ite_true]
  vcgen [body_missing_symbol_spec symbols next first leftWord remaining gap hmissing
      label origin elapsed,
    process_stopped_spec symbols next stop first leftWord remaining (gap + 1)
      (hmissing next) label (origin + 1) (elapsed + 1)]
  all_goals simp_all [separated, output, Problems.CertificatePadding.decode]
  all_goals lia

private theorem process_spec (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next stop : Γ) (hne : next ≠ stop) (first : Extended Γ 1)
    (leftWord remaining : List (Extended Γ 1)) (gap : Nat)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, separated (first :: leftWord) gap remaining⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      process (tm := tm) symbols next stop
    ⦃ fun _ cost final => final.config = ⟨label, output next stop (first :: leftWord) remaining⟩ ∧
        final.headPos = origin - (gap + (first :: leftWord).length : Nat) ∧
        cost.steps ≤ elapsed + budget (first :: leftWord) gap remaining ⦄ := by
  by_cases hnext : remaining.head? ≠ some (.inl next)
  · exact process_stopped_spec symbols next stop first leftWord remaining gap hnext
      label origin elapsed
  · have hhead : remaining.head? = some (.inl next) := by simpa using hnext
    cases remaining with
    | nil => simp at hhead
    | cons tag rest =>
      have htag : tag = .inl next := by simpa using hhead
      subst tag
      cases rest with
      | nil =>
        exact process_invalid_spec symbols next stop hne first leftWord [] gap (by simp)
          label origin elapsed
      | cons symbol remaining =>
        cases symbol with
        | inr marker =>
          exact process_invalid_spec symbols next stop hne first leftWord (.inr marker :: remaining)
            gap (by simp) label origin elapsed
        | inl symbol =>
          have houtput : output next stop (.inl symbol :: first :: leftWord) remaining =
              output next stop (first :: leftWord) (.inl next :: .inl symbol :: remaining) := by
            simp only [output, Alphabet.firstWord_symbol,
              Problems.CertificatePadding.decode_next next stop hne]
            cases Problems.CertificatePadding.decode next stop (Alphabet.firstWord remaining) <;>
              simp [List.reverse_cons, List.append_assoc]
          have hbudget : 2 * gap + 6 +
              budget (.inl symbol :: first :: leftWord) (gap + 1) remaining ≤
                budget (first :: leftWord) gap (.inl next :: .inl symbol :: remaining) := by
            simp only [budget, List.length_cons]
            ring_nf
            lia
          apply Std.WP.Triple.intro
          rintro initial current hpre
          apply (Spec.while_step_seq_spec (loop := process (tm := tm) symbols next stop)
            (hloop := rfl) (post := _)).le_wp initial current
          have htest : (TMCondition.tapeIs (tm := tm)
              (some (.inl next))).eval current.config = true := by
            simp [hpre.1, separated]
          simp only [htest, ite_true]
          vcgen [body_spec symbols hsymbols next symbol first leftWord remaining gap
              label origin elapsed,
            process_spec symbols hsymbols next stop hne (.inl symbol) (first :: leftWord)
              remaining (gap + 1) label (origin + 2) (elapsed + 2 * gap + 6)]
          all_goals simp_all [separated]
          all_goals lia
termination_by remaining.length

/--
This template removes the extra certificate symbols, preserving the input and recovered
certificate and erasing the unused suffix. Failed decoding gives an empty output.
The containing machine fixes all parameters once. The list `symbols` must contain every
alphabet symbol so the program can test every possible certificate symbol.
-/
def unpad (tm : SingleTapeTM (Extended Γ 1)) (symbols : List Γ) (next stop : Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekSeparator tm
  moveₜ .Right
  process symbols next stop

/--
Removing padding returns the decoded input and certificate, or an empty word on a bad entry.
It restores the head and uses at most `8 * (word.length + 2) ^ 2` moves.
-/
@[spec] theorem unpad_spec (symbols : List Γ) (hsymbols : ∀ symbol, symbol ∈ symbols)
    (next stop : Γ) (hne : next ≠ stop) (word : List (Extended Γ 1))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ word⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      unpad tm symbols next stop
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.mk₁ (result next stop word)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 8 * (word.length + 2) ^ 2 ⦄ := by
  have hlength := lengths_firstWord_afterMarker_le word
  have hspan : (.inr 0 :: (Alphabet.firstWord word).reverse.map
        (Sum.inl : Γ → Extended Γ 1)).length + 0 + (afterMarker word).length ≤
      word.length + 1 := by
    simp only [List.length_cons, List.length_map, List.length_reverse, Nat.add_zero]
    lia
  have hbudget : budget (.inr 0 :: (Alphabet.firstWord word).reverse.map
        (Sum.inl : Γ → Extended Γ 1)) 0 (afterMarker word) ≤
      (word.length + 1) * (2 * (word.length + 1) + 6) := by
    apply Nat.mul_le_mul (by lia) (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hspan) 6)
  have htotal : word.length + 1 +
      (word.length + 1) * (2 * (word.length + 1) + 6) ≤ 8 * (word.length + 2) ^ 2 := by
    calc
      _ = (word.length + 1) * (2 * (word.length + 1) + 7) := by ring
      _ ≤ (word.length + 2) * (8 * (word.length + 2)) := Nat.mul_le_mul (by lia) (by lia)
      _ = _ := by ring
  vcgen [unpad, seekSeparator_spec [] word label origin elapsed,
    process_spec symbols hsymbols next stop hne (.inr 0)
      ((Alphabet.firstWord word).reverse.map .inl) (afterMarker word) 0 label
      (origin + (Alphabet.firstWord word).length + 1)
      (elapsed + (Alphabet.firstWord word).length + 1)]
  case vc1 => simp_all [cursor_start]
  case vc2 => simp_all [TMState.move, TMState.moveCost, cursor, separated, BiTape.moveRight]
  case vc3 =>
    cases hd : Problems.CertificatePadding.decode next stop (Alphabet.firstWord (afterMarker word))
    all_goals simp_all [output, result, wordPair_encode, List.reverse_cons, List.map_reverse,
      show BiTape.mk₁ ([] : List (Extended Γ 1)) = BiTape.nil from rfl]
    all_goals lia

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
  apply Spec.runs_le
  vcgen [unpad_spec symbols hsymbols next stop hne word s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

private abbrev control (Γ : Type) [Fintype Γ] : SingleTapeTM (Extended Γ 1) where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This packages the certificate decoder as a polynomial-time Turing machine. The chosen finite
alphabet determines its symbol comparisons; all inputs run the same program.
-/
noncomputable def computer (next stop : Γ) (hne : next ≠ stop) :
    PolyTimeComputable (result next stop) :=
  Computes.polyTimeComputable (tm := control Γ)
    (p := unpad (control Γ) Finset.univ.toList next stop)
    (poly := 8 * (Polynomial.X + 2) ^ 2)
    (by
      simpa using unpad_computes (tm := control Γ) (Finset.univ.toList) (by simp) next stop hne)

end Algolean.Algorithms.SingleTapeTuringMachines.CertificatePadding
