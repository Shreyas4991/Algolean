/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Parsing
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Increment

/-!
# Counting rows of an encoded transition table

The counter occupies the first region before the preserved input. Its most significant bit
comes first, and overflow uses a blank cell to the left. Counting a row temporarily erases
one already identified input cell to mark the return position. The cell is restored after
updating the counter.

`collect` reads the input's fixed-length symbol representations and counts row separators.
It can skip the first separator when counting the verifier's largest state number. That
choice and the two counter digits are fixed when constructing the containing Query machine.
The verifier's rows and the counter value remain data on the single tape.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Rows

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Alphabet Problems.TMSAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ]

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

private noncomputable def rowByte (zero : Γ) : Γ :=
  (code CodeSymbol.rowSeparator).headD zero

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
    SingleTapeTM.Description.MovementSymbol, Extended]

private def sourceView (zero one : Γ) (bits : List Bool) (marker : Γ)
    (crossed remaining : List Γ) (tail : StackTape Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend crossed.reverse
      (StackTape.cons (some marker)
        (StackTape.cons none
          (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))))
    remaining tail

private def visitIncrement (zero one restore : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  visitPreviousRegion (Parsing.machine (Γ := Γ)) restore
    (incrementLeft (Parsing.machine (Γ := Γ)) zero one)

omit [Nontrivial Γ] in
private theorem visitIncrement_correct (zero one : Γ) (hne : zero ≠ one) (restore marker : Γ)
    (bits : List Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (s : TMState (Parsing.machine (Γ := Γ)))
    (htape : s.config.BiTape = sourceView zero one bits marker crossed (restore :: suffix) tail) :
    ∃ moves, Runs (visitIncrement zero one restore) s
      (sourceView zero one (incrementBits bits.reverse).reverse marker crossed
        (restore :: suffix) tail) s.headPos moves ∧
      moves ≤ 8 * (crossed.length + bits.length + 2) := by
  let output := (incrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)
  have ha (neighbor : StackTape Γ) (position : ℤ) (elapsed : Nat) :
      ⦃ fun cost current => current.config = ⟨s.config.state, BiTape.segment StackTape.nil
          (bits.map (fun bit => if bit then one else zero)) neighbor⟩ ∧
          current.headPos = position ∧ cost.steps ≤ elapsed ⦄
        incrementLeft (Parsing.machine (Γ := Γ)) zero one
      ⦃ fun _ cost final => final.config =
          ⟨s.config.state, BiTape.segment StackTape.nil output neighbor⟩ ∧
          final.headPos = position + bits.length - output.length ∧
          cost.steps ≤ elapsed + 4 * bits.length + 5 ⦄ := by
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    have hcount := carryCount_le_length bits.reverse
    have hlength := length_incrementBits_le bits.reverse
    vcgen [incrementLeft_spec (counter := Parsing.machine (Γ := Γ)) zero one hne bits
      neighbor s.config.state position initial.steps]
    all_goals simp_all [output]
    all_goals lia
  have hlength := length_incrementBits_le bits.reverse
  apply Spec.runs_le
  vcgen [visitIncrement,
    visitPreviousRegion_spec restore (incrementLeft (Parsing.machine (Γ := Γ)) zero one)
      (bits.map (fun bit => if bit then one else zero)) output (marker :: crossed) suffix tail
      (4 * bits.length + 5) s.config.state s.config.state s.headPos 0
      (by simpa only [List.length_map, add_assoc] using ha)]
  all_goals cases hcfg : s.config
  all_goals simp_all [sourceView, output, List.reverse_cons, StackTape.prepend_append]
  all_goals lia

private def checkFirstRow (zero one restore : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  tape ←ₜ none
  seekLeftEnd (Parsing.machine (Γ := Γ))
  ifₜ tape =ₜ some zero then
    tape ←ₜ some one
    seekRightBlank (Parsing.machine (Γ := Γ))
    tape ←ₜ some restore
  else
    seekRightBlank (Parsing.machine (Γ := Γ))
    tape ←ₜ some restore
    visitIncrement zero one restore

omit [Nontrivial Γ] in
private theorem returnToCursor_correct (zero one restore marker : Γ) (bits : List Bool)
    (crossed suffix : List Γ) (tail : StackTape Γ) (s : TMState (Parsing.machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.cons none
        (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))
      (marker :: crossed) (StackTape.prepend suffix (StackTape.cons none tail))) :
    Runs (do seekRightBlank (Parsing.machine (Γ := Γ)); FreeM.lift (.write (some restore))) s
      (sourceView zero one bits marker crossed (restore :: suffix) tail)
      (s.headPos + (crossed.length + 1 : Nat)) (crossed.length + 1) := by
  apply Spec.runs
  vcgen [seekRightBlank_segment_spec
    (StackTape.cons none
      (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))
    (StackTape.prepend suffix (StackTape.cons none tail)) (marker :: crossed)
    s.config.state s.headPos 0]
  all_goals cases hcfg : s.config
  all_goals simp_all [sourceView, TMState.write, BiTape.segment, BiTape.write,
    List.reverse_cons, StackTape.prepend_append]

omit [Nontrivial Γ] in
private theorem checkFirstRow_correct (zero one : Γ) (hne : zero ≠ one) (restore : Γ)
    (bits : List Bool) (seen : Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (s : TMState (Parsing.machine (Γ := Γ)))
    (htape : s.config.BiTape = sourceView zero one bits (if seen then one else zero)
      crossed (restore :: suffix) tail) :
    let output := if seen then (incrementBits bits.reverse).reverse else bits
    ∃ moves, Runs (checkFirstRow zero one restore) s
      (sourceView zero one output one crossed (restore :: suffix) tail) s.headPos moves ∧
      moves ≤ 16 * (crossed.length + bits.length + 2) := by
  let marker := if seen then one else zero
  let rest := StackTape.prepend suffix (StackTape.cons none tail)
  have hs : Runs (do [TMQuery (Parsing.machine (Γ := Γ))]
      tape ←ₜ none
      seekLeftEnd (Parsing.machine (Γ := Γ))) s
      (BiTape.segment
        (StackTape.cons none
          (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))
        (marker :: crossed) rest)
      (s.headPos - (crossed.length + 1 : Nat)) (crossed.length + 3) := by
    apply Spec.runs
    vcgen [seekLeftEnd_segment_spec (tm := Parsing.machine (Γ := Γ))
      (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse)
      rest (crossed.reverse ++ [marker]) [] s.config.state s.headPos 0]
    all_goals cases hcfg : s.config
    all_goals simp_all [sourceView, marker, rest, TMState.write, BiTape.segment, BiTape.write,
      StackTape.prepend_append]
  obtain ⟨cost, middle, hc, hmiddle, hpos, hsteps⟩ := hs
  cases seen with
  | false =>
    have hw := (write_correct middle (some one)).seq
      (q := do seekRightBlank (Parsing.machine (Γ := Γ)); FreeM.lift (.write (some restore)))
      (second := sourceView zero one bits one crossed (restore :: suffix) tail)
      (pos₂ := s.headPos) (time₂ := crossed.length + 1) (by
        intro current hcurrent hcurrentPos
        simpa [hcurrentPos, hpos, Nat.cast_add, sub_eq_add_neg, add_assoc] using
          returnToCursor_correct zero one restore one bits crossed suffix tail current
            (by simp [hcurrent, hmiddle, rest, BiTape.segment, BiTape.write]))
    have hbranch : Runs
        (branch (tm := Parsing.machine (Γ := Γ)) (.tapeIs (some zero))
          (do FreeM.lift (.write (some one))
              seekRightBlank (Parsing.machine (Γ := Γ))
              FreeM.lift (.write (some restore)))
          (do seekRightBlank (Parsing.machine (Γ := Γ))
              FreeM.lift (.write (some restore))
              visitIncrement zero one restore)) middle _ s.headPos (0 + (crossed.length + 1)) :=
      Runs.branch (by simpa [hmiddle, marker] using hw)
    have hj := hbranch.prepend hc (by simp [hmiddle])
    refine ⟨cost.steps + (0 + (crossed.length + 1)), ?_, ?_⟩
    · simpa [checkFirstRow, bind_assoc] using hj
    · rw [hsteps]
      simp only [zero_add]
      lia
  | true =>
    have hr := returnToCursor_correct zero one restore one bits crossed suffix tail middle
      (by simp [hmiddle, marker, rest])
    obtain ⟨more, current, hreturn, hcurrent, hcurrentPos, hreturnMoves⟩ := hr
    obtain ⟨moves, hv, hb⟩ := visitIncrement_correct zero one hne restore one bits crossed suffix
      tail current (by simpa using congrArg SingleTapeTM.Cfg.BiTape hcurrent)
    have hbody := hv.prepend hreturn (by simp [hcurrent])
    have hbranch : Runs
        (branch (tm := Parsing.machine (Γ := Γ)) (.tapeIs (some zero))
          (do FreeM.lift (.write (some one))
              seekRightBlank (Parsing.machine (Γ := Γ))
              FreeM.lift (.write (some restore)))
          (do seekRightBlank (Parsing.machine (Γ := Γ))
              FreeM.lift (.write (some restore))
              visitIncrement zero one restore)) middle _ current.headPos (more.steps + moves) :=
      Runs.branch (by simpa [hmiddle, marker, Ne.symm hne] using hbody)
    have hj := hbranch.prepend hc (by simp [hmiddle])
    refine ⟨cost.steps + (more.steps + moves), ?_, ?_⟩
    · simpa [checkFirstRow, hpos, hcurrentPos, bind_assoc,
        Nat.cast_add, sub_eq_add_neg, add_assoc] using hj
    · rw [hsteps, hreturnMoves]
      lia

private noncomputable def countOne (zero one : Γ) (skipFirst : Bool) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  checkPrefix (Parsing.machine (Γ := Γ)) (.inl .rowEnd) (.inl .rowStart)
    (code CodeSymbol.rowSeparator)
  ifₜ state =ₜ some (Sum.inl (Parsing.Stage.rowEnd (Γ := Γ))) then
    (if skipFirst then checkFirstRow zero one (rowByte zero)
      else visitIncrement zero one (rowByte zero))
  else
    pure ()
  moveCells (Parsing.machine (Γ := Γ)) .Right 12

private noncomputable def countLoop (zero one : Γ) (skipFirst : Bool) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  whileₜ (notₜ tape =ₜ none) do
    countOne zero one skipFirst

private def nextBits (bits : List Bool) (skipFirst seen : Bool) (symbol : CodeSymbol) :
    List Bool :=
  if symbol = CodeSymbol.rowSeparator ∧ (skipFirst = false ∨ seen = true)
    then (incrementBits bits.reverse).reverse else bits

private theorem countOne_correct (zero one : Γ) (hne : zero ≠ one)
    (skipFirst seen : Bool) (bits : List Bool) (symbol : CodeSymbol)
    (crossed suffix : List Γ) (tail : StackTape Γ) (s : TMState (Parsing.machine (Γ := Γ)))
    (htape : s.config.BiTape = sourceView zero one bits
      (if skipFirst && seen then one else zero) crossed (code symbol ++ suffix) tail) :
    ∃ cost final, Completes (countOne zero one skipFirst) s cost final ∧
      final.config.BiTape = sourceView zero one (nextBits bits skipFirst seen symbol)
        (if skipFirst && (seen || decide (symbol = CodeSymbol.rowSeparator)) then one else zero)
        (crossed ++ code symbol) suffix tail ∧
      final.headPos = s.headPos + 12 ∧
      cost.steps ≤ 40 * (crossed.length + bits.length + 2) := by
  classical
  apply Spec.completes
  unfold countOne
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨some (if code CodeSymbol.rowSeparator <+: code symbol ++ suffix
      then .inl .rowEnd else .inl .rowStart), s.config.BiTape⟩ ∧
    current.headPos = s.headPos ∧ cost.steps ≤ 2 * (code (Γ := Γ) CodeSymbol.rowSeparator).length)
  · vcgen [checkPrefix_spec (tm := Parsing.machine (Γ := Γ)) (.inl .rowEnd) (.inl .rowStart)
      (code CodeSymbol.rowSeparator) (code symbol ++ suffix)
      (StackTape.prepend crossed.reverse
        (StackTape.cons (some (if skipFirst && seen then one else zero))
          (StackTape.cons none
            (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))))
      tail s.config.state s.headPos 0]
    all_goals cases hcfg : s.config
    all_goals simp_all [sourceView]
  · intro _
    apply Std.WP.Triple.intro
    rintro cost middle ⟨hmiddle, hmpos, hb⟩
    have hp : code CodeSymbol.rowSeparator <+: code symbol ++ suffix ↔
        symbol = CodeSymbol.rowSeparator := by
      simpa only [code, eq_comm] using
        finiteWordsOver_symbol_prefix_iff CodeSymbol.rowSeparator symbol suffix
    have hbody : ∃ moves, Runs
        (branch (tm := Parsing.machine (Γ := Γ)) (.stateIs (some (.inl .rowEnd)))
          (if skipFirst then checkFirstRow zero one (rowByte zero)
            else visitIncrement zero one (rowByte zero)) (pure ())) middle
        (sourceView zero one (nextBits bits skipFirst seen symbol)
          (if skipFirst && (seen || decide (symbol = CodeSymbol.rowSeparator)) then one else zero)
          crossed (code symbol ++ suffix) tail) middle.headPos moves ∧
        moves ≤ 16 * (crossed.length + bits.length + 2) := by
      by_cases heq : symbol = CodeSymbol.rowSeparator
      · subst symbol
        obtain ⟨first, rest, hcode⟩ : ∃ first rest, code (Γ := Γ) CodeSymbol.rowSeparator =
            first :: rest := List.exists_cons_of_ne_nil (by
          intro hempty
          have := code_length (Γ := Γ) CodeSymbol.rowSeparator
          rw [hempty] at this
          contradiction)
        have hfirst : rowByte (Γ := Γ) zero = first := by simp [rowByte, hcode]
        cases skipFirst with
        | false =>
          obtain ⟨moves, hr, hm⟩ := visitIncrement_correct zero one hne first zero bits crossed
            (rest ++ suffix) tail middle (by simpa [hmiddle, hcode] using htape)
          refine ⟨moves, Runs.branch ?_, by lia⟩
          simpa [hmiddle, hp, hfirst, nextBits, hcode] using hr
        | true =>
          obtain ⟨moves, hr, hm⟩ := checkFirstRow_correct zero one hne first bits seen crossed
            (rest ++ suffix) tail middle (by simpa [hmiddle, hcode] using htape)
          refine ⟨moves, Runs.branch ?_, hm⟩
          simpa [hmiddle, hp, hfirst, nextBits, hcode] using hr
      · refine ⟨0, Runs.branch ?_, by simp⟩
        have hcfg : middle.config = {middle.config with
            BiTape := sourceView zero one bits (if skipFirst && seen then one else zero)
              crossed (code symbol ++ suffix) tail} := by
          cases hm : middle.config
          simpa [hm] using (congrArg SingleTapeTM.Cfg.BiTape hmiddle).trans htape
        exact ⟨0, middle, by simp [hmiddle, hp, heq],
          by simpa [nextBits, heq] using hcfg, rfl, rfl⟩
    obtain ⟨moves, hr, hbound⟩ := hbody
    obtain ⟨currentCost, current, hbranch, hcurrent, hcurrentPos, hsteps⟩ := hr
    have hmove (newBits : List Bool) (marker : Γ) :
        BiTape.moveRight^[12] (sourceView zero one newBits marker crossed
          (code symbol ++ suffix) tail) =
        sourceView zero one newBits marker (crossed ++ code symbol) suffix tail := by
      rw [← code_length (Γ := Γ) symbol]
      simp [sourceView, BiTape.segment_moveRight_iterate, List.reverse_append,
        StackTape.prepend_append]
    vcgen [Spec.steps hbranch cost.steps,
      moveCells_spec (tm := Parsing.machine (Γ := Γ)) .Right 12
        (sourceView zero one (nextBits bits skipFirst seen symbol)
          (if skipFirst && (seen || decide (symbol = CodeSymbol.rowSeparator)) then one else zero)
          crossed (code symbol ++ suffix) tail)
        current.config.state current.headPos (cost.steps + currentCost.steps)]
    all_goals simp_all [code_length]
    all_goals lia

private def countResult (bits : List Bool) (skipFirst seen : Bool) :
    List CodeSymbol → List Bool × Bool
  | [] => (bits, seen)
  | symbol :: rest => countResult (nextBits bits skipFirst seen symbol) skipFirst
      (seen || decide (symbol = CodeSymbol.rowSeparator)) rest

private theorem nextBits_length (bits : List Bool) (skipFirst seen : Bool)
    (symbol : CodeSymbol) : (nextBits bits skipFirst seen symbol).length ≤ bits.length + 1 := by
  unfold nextBits
  split
  · simpa using length_incrementBits_le bits.reverse
  · lia

private theorem countResult_length (bits : List Bool) (skipFirst seen : Bool)
    (word : List CodeSymbol) :
    (countResult bits skipFirst seen word).1.length ≤ bits.length + word.length := by
  induction word generalizing bits seen with
  | nil => simp [countResult]
  | cons symbol rest ih =>
    have := ih (nextBits bits skipFirst seen symbol)
      (seen || decide (symbol = CodeSymbol.rowSeparator))
    have := nextBits_length bits skipFirst seen symbol
    simpa only [countResult, List.length_cons] using (by lia :
      (countResult (nextBits bits skipFirst seen symbol) skipFirst
        (seen || decide (symbol = CodeSymbol.rowSeparator)) rest).1.length ≤
          bits.length + (rest.length + 1))

private theorem countResult_seen (bits : List Bool) (skipFirst seen : Bool)
    (word : List CodeSymbol) :
    (countResult bits skipFirst seen word).2 =
      (seen || decide (CodeSymbol.rowSeparator ∈ word)) := by
  induction word generalizing bits seen with
  | nil => simp [countResult]
  | cons symbol rest ih =>
    simp only [countResult, ih, List.mem_cons]
    simp [eq_comm, Bool.or_assoc]

private theorem countResult_value (bits : List Bool) (skipFirst seen : Bool)
    (word : List CodeSymbol) :
    binaryValue (countResult bits skipFirst seen word).1.reverse +
        (if skipFirst && (countResult bits skipFirst seen word).2 then 1 else 0) =
      binaryValue bits.reverse + word.count CodeSymbol.rowSeparator +
        (if skipFirst && seen then 1 else 0) := by
  induction word generalizing bits seen with
  | nil => simp [countResult]
  | cons symbol rest ih =>
    have h := ih (nextBits bits skipFirst seen symbol)
      (seen || decide (symbol = CodeSymbol.rowSeparator))
    simp only [countResult]
    by_cases heq : symbol = CodeSymbol.rowSeparator <;>
      cases skipFirst <;> cases seen <;>
      simp [nextBits, heq, binaryValue_incrementBits] at h ⊢ <;> lia

private theorem countLoop_correct (zero one : Γ) (hne : zero ≠ one)
    (skipFirst seen : Bool) (bits : List Bool) (word : List CodeSymbol)
    (crossed : List Γ) (tail : StackTape Γ) (s : TMState (Parsing.machine (Γ := Γ)))
    (htape : s.config.BiTape = sourceView zero one bits
      (if skipFirst && seen then one else zero) crossed (word.flatMap code) tail) :
    let result := countResult bits skipFirst seen word
    ∃ cost final, Completes (countLoop zero one skipFirst) s cost final ∧
      final.config.BiTape = sourceView zero one result.1
        (if skipFirst && result.2 then one else zero)
        (crossed ++ word.flatMap code) [] tail ∧
      final.headPos = s.headPos + 12 * word.length ∧
      cost.steps ≤ 40 * word.length *
        (crossed.length + bits.length + 13 * word.length + 2) := by
  induction word generalizing bits seen crossed s with
  | nil =>
    refine ⟨0, s, completes_while_false _ _ s (by simp [htape, sourceView]), ?_,
      by simp, by simp⟩
    simpa [countResult] using htape
  | cons symbol rest ih =>
    obtain ⟨cost, middle, hc, hm, hmpos, hb⟩ := countOne_correct zero one hne skipFirst seen bits
      symbol crossed (rest.flatMap code) tail s htape
    obtain ⟨more, final, hr, hf, hfpos, hbound⟩ :=
      ih (seen || decide (symbol = CodeSymbol.rowSeparator))
        (nextBits bits skipFirst seen symbol) (crossed ++ code symbol) middle hm
    have hnonnil : code (Γ := Γ) symbol ≠ [] := by
      intro h
      have := code_length (Γ := Γ) symbol
      simp [h] at this
    have htest : (TMCondition.not (.tapeIs none)).eval s.config = true := by
      cases hcode : code (Γ := Γ) symbol with
      | nil => exact False.elim (hnonnil hcode)
      | cons first rest => simp [htape, sourceView, hcode]
    refine ⟨cost + more, final, Completes.while_step htest hc hr, ?_, ?_, ?_⟩
    · simpa [countResult, List.append_assoc] using hf
    · rw [hfpos, hmpos]
      simp only [List.length_cons]
      push_cast
      ring
    · have hlen := nextBits_length bits skipFirst seen symbol
      have hcodelen := code_length (Γ := Γ) symbol
      simp only [List.length_append, hcodelen] at hbound
      simp only [TMCost.add_steps, List.length_cons]
      calc
        cost.steps + more.steps ≤
            40 * (crossed.length + bits.length + 13 * (rest.length + 1) + 2) +
            40 * rest.length *
              (crossed.length + bits.length + 13 * (rest.length + 1) + 2) := by
          apply Nat.add_le_add
          · exact hb.trans (Nat.mul_le_mul_left 40 (by lia))
          · exact hbound.trans (Nat.mul_le_mul_left (40 * rest.length) (by lia))
        _ = _ := by ring

/--
This machine template counts row separators using the binary counter before the input region.
It starts on the counter's first digit and returns there after restoring the input marker.
The containing machine fixes the two digits and whether the first row is skipped once.
-/
noncomputable def collect (zero one : Γ) (skipFirst : Bool) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  nextRegion (Parsing.machine (Γ := Γ))
  moveₜ .Right
  countLoop zero one skipFirst
  seekLeftEnd (Parsing.machine (Γ := Γ))
  tape ←ₜ some zero
  previousRegion (Parsing.machine (Γ := Γ))
  state ←ₜ .inl .header

/--
The row counter preserves the encoded input and the tape beyond it. Starting with the single
zero digit, it records the number of row separators, or one less when the first row is skipped.
It returns to the first counter digit and takes at most `640 * (input.length + 1) ^ 2` head moves.
The input must consist of complete symbol encodings; the structure check establishes this fact.
-/
theorem collect_correct (zero one : Γ) (hne : zero ≠ one) (skipFirst : Bool)
    (word : List CodeSymbol) (tail : StackTape Γ) (s : TMState (Parsing.machine (Γ := Γ))) :
    let input := (finiteWordsOver CodeSymbol Γ).encode word
    s.config.BiTape = BiTape.segment StackTape.nil [zero]
      (StackTape.prepend (zero :: input) (StackTape.cons none tail)) →
    ∃ (bits : List Bool) (cost : TMCost) (final : TMState (Parsing.machine (Γ := Γ))),
      Completes (collect zero one skipFirst) s cost final ∧
      final.config = ⟨some (.inl .header),
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.prepend (zero :: input) (StackTape.cons none tail))⟩ ∧
      final.headPos = s.headPos + 1 - bits.length ∧
      binaryValue bits.reverse = word.count CodeSymbol.rowSeparator -
        (if skipFirst then 1 else 0) ∧
      bits.length ≤ word.length + 1 ∧
      cost.steps ≤ 640 * (input.length + 1) ^ 2 := by
  classical
  let input := (finiteWordsOver CodeSymbol Γ).encode word
  dsimp only
  intro htape
  have hencode : input = word.flatMap code := encode_finiteWordsOver word
  have hlen : input.length = 12 * word.length := by
    rw [hencode, List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  let result := countResult [false] skipFirst false word
  let digits := result.1.map (fun bit => if bit then one else zero)
  let marker := if skipFirst && result.2 then one else zero
  have hv : binaryValue result.1.reverse = word.count CodeSymbol.rowSeparator -
      (if skipFirst then 1 else 0) := by
    have hv := countResult_value [false] skipFirst false word
    have hs := countResult_seen [false] skipFirst false word
    have hcount : word.count CodeSymbol.rowSeparator = 0 ↔ CodeSymbol.rowSeparator ∉ word :=
      List.count_eq_zero
    cases skipFirst <;> by_cases hm : CodeSymbol.rowSeparator ∈ word <;>
      simp [result, hs, hm] at hv ⊢ <;> lia
  have hbits : result.1.length ≤ word.length + 1 := by
    simpa [result, Nat.add_comm] using countResult_length [false] skipFirst false word
  refine ⟨result.1, ?_⟩
  apply Spec.completes
  unfold collect
  rw [← bind_assoc]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨s.config.state, sourceView zero one [false] zero [] input tail⟩ ∧
    current.headPos = s.headPos + 3 ∧ cost.steps = 3)
  · vcgen [nextRegion_spec (tm := Parsing.machine (Γ := Γ)) StackTape.nil
      [zero] (zero :: input) tail s.config.state s.headPos 0]
    all_goals cases hcfg : s.config
    all_goals simp_all [sourceView, TMState.move, TMState.moveCost, add_assoc, input]
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hsteps⟩
    obtain ⟨cost, middle, hc, hmiddle, hmiddlepos, hb⟩ :=
      countLoop_correct zero one hne skipFirst false [false] word [] tail current
        (by simpa [← hencode] using congrArg SingleTapeTM.Cfg.BiTape hcfg)
    have hbound : 3 + cost.steps + (input.length + 3) + (digits.length + 3) ≤
        640 * (input.length + 1) ^ 2 := by
      simp only [List.length_singleton, List.length_nil, zero_add] at hb
      dsimp only [digits]
      simp only [List.length_map]
      nlinarith
    vcgen [Spec.steps hc initial.steps,
      seekLeftEnd_segment_spec (tm := Parsing.machine (Γ := Γ))
        (StackTape.mapSome digits.reverse) tail (input.reverse ++ [marker]) []
        middle.config.state (s.headPos + 3 + 12 * word.length) (initial.steps + cost.steps),
      previousRegion_spec (tm := Parsing.machine (Γ := Γ)) StackTape.nil
        digits (zero :: input) tail middle.config.state (s.headPos + 2)
        (initial.steps + cost.steps + input.length + 3)]
    all_goals cases hm : middle.config
    all_goals simp_all [sourceView, marker, digits, ← hencode,
      StackTape.prepend_append, TMState.write, List.reverse_append]
    all_goals lia

end Algolean.Algorithms.TMSATToSAT.Rows
