/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.StateFields

/-!
# Checking all state references in an encoded verifier

* `checkStates` checks the largest state number, the initial state, and every next-state
  number against the number of rows actually present in the transition table.
* `check` first checks the arrangement of all fields, then checks the state references.
  Both passes preserve the input. The head returns to its first cell, and the final control
  state records acceptance or rejection.

The same finite Query program reads every input. State numbers and the transition table
remain on the tape; they are not parameters used to construct the program.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Validation

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet Problems.TMSAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ]

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

private abbrev tm : SingleTapeTM Γ := Parsing.machine

private noncomputable def encode (word : List CodeSymbol) : List Γ :=
  word.flatMap (code (Γ := Γ))

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
    SingleTapeTM.Description.MovementSymbol, Extended]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_eq (word : List CodeSymbol) :
    encode (Γ := Γ) word = (finiteWordsOver CodeSymbol Γ).encode word := by
  exact (encode_finiteWordsOver word).symm

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_length (word : List CodeSymbol) :
    (encode (Γ := Γ) word).length = 12 * word.length := by
  simp [encode, List.length_flatMap, code_length, List.sum_replicate, Nat.mul_comm]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_nil : encode (Γ := Γ) [] = [] := rfl

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_cons (symbol : CodeSymbol) (word : List CodeSymbol) :
    encode (Γ := Γ) (symbol :: word) = code symbol ++ encode word := rfl

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_append (first second : List CodeSymbol) :
    encode (Γ := Γ) (first ++ second) = encode first ++ encode second := List.flatMap_append ..

attribute [local simp] encode_nil encode_cons encode_append encode_length code_length

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem encode_eq_nil_iff (word : List CodeSymbol) :
    encode (Γ := Γ) word = [] ↔ word = [] := by
  constructor
  · intro h
    have := encode_length (Γ := Γ) word
    rw [h] at this
    simpa using this.symm
  · rintro rfl
    rfl

attribute [local simp] encode_eq_nil_iff

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_ne_nil (symbol : CodeSymbol) : code (Γ := Γ) symbol ≠ [] := by
  intro h
  have := code_length (Γ := Γ) symbol
  rw [h] at this
  contradiction

attribute [local simp] code_ne_nil

private theorem digit_rows (number : List Bool) :
    (number.map CodeSymbol.digit).count CodeSymbol.rowSeparator = 0 := by
  induction number with
  | nil => rfl
  | cons bit bits ih =>
    cases bit <;>
      simpa [CodeSymbol.digit, CodeSymbol.rowSeparator, SingleTapeTM.Description.bitSymbol] using ih

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem movement_prefix (symbol : CodeSymbol) (rest : List CodeSymbol) :
    code (Γ := Γ) .movementEnd <+: encode (symbol :: rest) ↔ symbol = .movementEnd := by
  change code .movementEnd <+: code symbol ++ encode rest ↔ _
  rw [List.prefix_iff_eq_take, code_length, ← code_length (Γ := Γ) symbol, List.take_left]
  constructor
  · intro h
    simpa [code, eq_comm] using (finiteWordsOver CodeSymbol Γ).encode_injective h
  · rintro rfl
    rfl

private noncomputable def view (before after : List CodeSymbol) (tail : StackTape Γ) : BiTape Γ :=
  BiTape.segment (StackTape.prepend (encode before).reverse StackTape.nil) (encode after) tail

open scoped Classical in
private theorem stateField_spec (zero one : Γ) (hne : zero ≠ one)
    (field : StateFields.Field)
    (before after : List CodeSymbol) (number : List Bool)
    (hafter : CodeSymbol.headerEnd ∉ after) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        view before (number.map CodeSymbol.digit ++ field.ending :: after) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      StateFields.check zero one field
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if field.Valid (Computability.decodeNat number)
          ((before ++ after).count CodeSymbol.rowSeparator) then .header else .reject)),
          view (before ++ number.map CodeSymbol.digit) (field.ending :: after) tail⟩ ∧
        final.headPos = origin + (12 * number.length : Nat) ∧
        cost.steps ≤ elapsed + 4096 * (before.length + number.length + after.length + 2) ^ 2 ⦄ := by
  have hlength : ((finiteWordsOver CodeSymbol Γ).encode
      (number.map CodeSymbol.digit)).length = 12 * number.length := by
    rw [← encode_eq, encode_length, List.length_map]
  vcgen [StateFields.check_spec zero one hne field before after number hafter tail
    label origin elapsed]
  all_goals
    simp_all [StateFields.FieldInput, StateFields.CheckResult, StateFields.fieldTape,
      view, encode_eq, encode_finiteWordsOver_append]

private theorem count_movement : [CodeSymbol.movementEnd].count CodeSymbol.rowSeparator = 0 := by
  decide

private theorem count_entry : [CodeSymbol.entryEnd].count CodeSymbol.rowSeparator = 0 := by
  decide

attribute [local simp] count_movement count_entry digit_rows

private theorem movement_beq_row :
    (CodeSymbol.movementEnd == CodeSymbol.rowSeparator) = false := by decide

private theorem entry_beq_row :
    (CodeSymbol.entryEnd == CodeSymbol.rowSeparator) = false := by decide

attribute [local simp] movement_beq_row entry_beq_row

private theorem advance_spec (before crossed after : List CodeSymbol) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view before (crossed ++ after) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      moveCells (tm (Γ := Γ)) .Right (12 * crossed.length)
    ⦃ fun _ cost final => final.config = ⟨label, view (before ++ crossed) after tail⟩ ∧
        final.headPos = origin + (12 * crossed.length : Nat) ∧
        cost.steps ≤ elapsed + 12 * crossed.length ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  have hmove := BiTape.segment_moveRight_iterate
    (StackTape.prepend (encode (Γ := Γ) before).reverse StackTape.nil)
    (encode (Γ := Γ) crossed) (encode (Γ := Γ) after) tail
  rw [encode_length] at hmove
  vcgen [moveCells_spec (tm := tm (Γ := Γ)) .Right (12 * crossed.length)
    (view before (crossed ++ after) tail)
    label origin initial.steps]
  all_goals
    simp_all [view, List.reverse_append]

private def skipEnd : Prog (TMQuery (tm (Γ := Γ))) Unit := moveCells tm .Right 12

private noncomputable def nextStates (zero one : Γ) : Prog (TMQuery (tm (Γ := Γ))) Unit :=
    do [TMQuery (tm (Γ := Γ))]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ state =ₜ some (.inl .reject) then
      seekRightBlank tm
    else
      checkPrefix tm (.inl .initial) (.inl .header) (code .movementEnd)
      ifₜ state =ₜ some (.inl .initial) then
        moveCells tm .Right 12
        StateFields.check zero one .next
      else
        pure ()
      skipEnd

private theorem nextStates_reject_spec (zero one : Γ) (before after : List CodeSymbol)
    (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some (.inl .reject), view before after tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      nextStates zero one
    ⦃ fun _ cost final => final.config = ⟨some (.inl .reject), view (before ++ after) [] tail⟩ ∧
        final.headPos = origin + (12 * after.length : Nat) ∧
        cost.steps ≤ elapsed + 12 * after.length ⦄ := by
  cases after with
  | nil =>
    unfold nextStates
    vcgen [Spec.while_false_spec]
    simp_all [view, BiTape.segment]
  | cons symbol after =>
    have hn : encode (Γ := Γ) (symbol :: after) ≠ [] := by
      intro h
      have := encode_length (Γ := Γ) (symbol :: after)
      rw [h] at this
      simp at this
    have hf (position : ℤ) (steps : Nat) :
        ⦃ fun cost current => current.config =
            ⟨some (.inl .reject), view (before ++ symbol :: after) [] tail⟩ ∧
            current.headPos = position ∧ cost.steps ≤ steps ⦄
          nextStates zero one
        ⦃ fun _ cost final => final.config =
            ⟨some (.inl .reject), view (before ++ symbol :: after) [] tail⟩ ∧
            final.headPos = position ∧ cost.steps ≤ steps ⦄ := by
      unfold nextStates
      vcgen [Spec.while_false_spec]
      simp_all [view, BiTape.segment]
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hcost⟩
    unfold nextStates
    vcgen [skipEnd, Spec.while_step_spec (loop := nextStates zero one) (hloop := rfl),
      seekRightBlank_segment_spec (tm := tm (Γ := Γ))
        (StackTape.prepend (encode (Γ := Γ) before).reverse StackTape.nil)
        tail (encode (Γ := Γ) (symbol :: after)) (some (.inl .reject)) origin initial.steps,
      hf (origin + (encode (Γ := Γ) (symbol :: after)).length)
        (initial.steps + (encode (Γ := Γ) (symbol :: after)).length)]
    all_goals
      simp_all [view, BiTape.segment, List.reverse_append,
        List.head?_eq_none_iff]
      all_goals lia

private def pieceWord : CodeSymbol ⊕ List Bool → List CodeSymbol
  | .inl symbol => [symbol]
  | .inr number => CodeSymbol.movementEnd :: number.map CodeSymbol.digit ++ [CodeSymbol.entryEnd]

private def piecesWord (pieces : List (CodeSymbol ⊕ List Bool)) : List CodeSymbol :=
  pieces.flatMap pieceWord

private theorem piecesWord_nil : piecesWord [] = [] := rfl

private theorem piecesWord_cons (piece : CodeSymbol ⊕ List Bool)
    (pieces : List (CodeSymbol ⊕ List Bool)) :
    piecesWord (piece :: pieces) = pieceWord piece ++ piecesWord pieces := rfl

attribute [local simp] piecesWord_nil piecesWord_cons

private def SafePieces (pieces : List (CodeSymbol ⊕ List Bool)) : Prop :=
  ∀ symbol, Sum.inl symbol ∈ pieces → symbol ≠ CodeSymbol.headerEnd ∧
    symbol ≠ CodeSymbol.movementEnd

private def NextValid (rows : Nat) (pieces : List (CodeSymbol ⊕ List Bool)) : Prop :=
  ∀ number, Sum.inr number ∈ pieces → Computability.decodeNat number ≤ rows

private theorem no_header (pieces : List (CodeSymbol ⊕ List Bool)) (hsafe : SafePieces pieces) :
    CodeSymbol.headerEnd ∉ piecesWord pieces := by
  classical
  simp only [piecesWord, List.mem_flatMap]
  rintro ⟨piece, hp, he⟩
  cases piece with
  | inl symbol =>
    have heq : CodeSymbol.headerEnd = symbol := by simpa [pieceWord] using he
    exact (hsafe symbol hp).1 heq.symm
  | inr number =>
    simp [pieceWord, CodeSymbol.headerEnd, CodeSymbol.movementEnd,
      CodeSymbol.entryEnd, CodeSymbol.digit, SingleTapeTM.Description.bitSymbol] at he

set_option maxHeartbeats 1600000 in
-- The induction combines the field comparisons and their bounds for the whole encoded word.
open Classical in
private theorem nextStates_spec (zero one : Γ) (hne : zero ≠ one)
    (pieces : List (CodeSymbol ⊕ List Bool)) (hsafe : SafePieces pieces)
    (before : List CodeSymbol) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    let word := piecesWord pieces
    let rows := (before ++ word).count CodeSymbol.rowSeparator
    ⦃ fun cost current => current.config = ⟨some (.inl .header), view before word tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      nextStates zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if NextValid rows pieces then .header else .reject)),
          view (before ++ word) [] tail⟩ ∧
        final.headPos = origin + (12 * word.length : Nat) ∧
        cost.steps ≤ elapsed + 8192 * (word.length + 1) *
          (before.length + word.length + 2) ^ 2 ⦄ := by
  classical
  dsimp only
  induction pieces generalizing before origin elapsed with
  | nil =>
    unfold nextStates
    vcgen [Spec.while_false_spec]
    simp_all [piecesWord, NextValid, view, BiTape.segment]
    all_goals lia
  | cons piece pieces ih =>
    have hs : SafePieces pieces := fun symbol h => hsafe symbol (by simp [h])
    have hn := no_header pieces hs
    have hr := ih hs
    cases piece with
    | inl symbol =>
      have hsym := hsafe symbol (by simp)
      have hp := movement_prefix (Γ := Γ) symbol (piecesWord pieces)
      have hmBase := advance_spec (Γ := Γ) before [symbol] (piecesWord pieces) tail
        (some (.inl .header)) origin (elapsed + 24)
      norm_num only [List.length_singleton, Nat.mul_one] at hmBase
      have hm := hmBase
      change Std.WP.Triple (skipEnd (Γ := Γ)) _ _ _ at hm
      unfold nextStates
      vcgen [Spec.while_step_spec (loop := nextStates zero one) (hloop := rfl),
        checkPrefix_spec (tm := tm (Γ := Γ)) (.inl .initial) (.inl .header) (code .movementEnd)
          (encode (Γ := Γ) (symbol :: piecesWord pieces))
          (StackTape.prepend (encode (Γ := Γ) before).reverse StackTape.nil) tail
          (some (.inl .header)) origin elapsed,
        hm, hr (before ++ [symbol]) (origin + 12) (elapsed + 36)]
      all_goals
        simp_all [piecesWord, pieceWord, NextValid, view, code_length,
          BiTape.segment, List.append_assoc, List.reverse_append]
        all_goals try ring_nf
        all_goals lia
    | inr number =>
      let word := piecesWord pieces
      let crossed := before ++ [CodeSymbol.movementEnd]
      let rows := (before ++ word).count CodeSymbol.rowSeparator
      have hfield := stateField_spec zero one hne .next crossed word number hn tail
        (some (.inl .initial)) (origin + 12) (elapsed + 36)
      have hstart := advance_spec (Γ := Γ) before [CodeSymbol.movementEnd]
        (number.map CodeSymbol.digit ++ CodeSymbol.entryEnd :: word) tail
        (some (.inl .initial)) origin (elapsed + 24)
      have hend (label : Option (Parsing.State Γ)) :
          ⦃ fun cost current => current.config = ⟨label,
              view (crossed ++ number.map CodeSymbol.digit) (CodeSymbol.entryEnd :: word) tail⟩ ∧
              current.headPos = origin + 12 + (12 * number.length : Nat) ∧
              cost.steps ≤ elapsed + 36 +
                4096 * (crossed.length + number.length + word.length + 2) ^ 2 ⦄
            skipEnd (Γ := Γ)
          ⦃ fun _ cost final => final.config = ⟨label,
              view (crossed ++ number.map CodeSymbol.digit ++ [CodeSymbol.entryEnd]) word tail⟩ ∧
              final.headPos = origin + 12 + (12 * number.length : Nat) + 12 ∧
              cost.steps ≤ elapsed + 48 +
                4096 * (crossed.length + number.length + word.length + 2) ^ 2 ⦄ := by
        have h := advance_spec (Γ := Γ)
          (crossed ++ number.map CodeSymbol.digit) [CodeSymbol.entryEnd] word tail label
          (origin + 12 + (12 * number.length : Nat))
          (elapsed + 36 + 4096 * (crossed.length + number.length + word.length + 2) ^ 2)
        norm_num only [List.length_singleton, Nat.mul_one, List.singleton_append] at h
        have heq : elapsed + 36 +
            4096 * (crossed.length + number.length + word.length + 2) ^ 2 + 12 =
            elapsed + 48 + 4096 * (crossed.length + number.length + word.length + 2) ^ 2 := by
          lia
        rw [heq] at h
        exact h
      norm_num only [List.length_singleton, Nat.mul_one] at hstart
      have hrows : (crossed ++ word).count CodeSymbol.rowSeparator = rows := by
        simp only [crossed, rows, List.count_append, count_movement, Nat.add_zero]
      simp only [StateFields.Field.ending, StateFields.Field.Valid, hrows] at hfield
      let nextBefore := crossed ++ number.map CodeSymbol.digit ++ [CodeSymbol.entryEnd]
      let available := elapsed + 48 +
        4096 * (crossed.length + number.length + word.length + 2) ^ 2
      have hrestRows : (nextBefore ++ word).count CodeSymbol.rowSeparator = rows := by
        simp [nextBefore, rows, crossed, List.count_append, List.count_cons]
      have hcontinue :
          ⦃ fun cost current => current.config =
              ⟨some (.inl (if Computability.decodeNat number ≤ rows then .header else .reject)),
                view nextBefore word tail⟩ ∧
              current.headPos = origin + 12 + (12 * number.length : Nat) + 12 ∧
              cost.steps ≤ available ⦄
            nextStates zero one
          ⦃ fun _ cost final => final.config =
              ⟨some (.inl (if Computability.decodeNat number ≤ rows ∧ NextValid rows pieces
                then .header else .reject)), view (nextBefore ++ word) [] tail⟩ ∧
              final.headPos = origin + 12 + (12 * number.length : Nat) + 12 +
                (12 * word.length : Nat) ∧
              cost.steps ≤ available + 8192 * (word.length + 1) *
                (nextBefore.length + word.length + 2) ^ 2 ⦄ := by
        have hrestRows' : (nextBefore ++ piecesWord pieces).count CodeSymbol.rowSeparator =
            rows := hrestRows
        by_cases hv : Computability.decodeNat number ≤ rows
        · simpa only [word, hv, ite_true, true_and, hrestRows'] using
            hr nextBefore (origin + 12 + (12 * number.length : Nat) + 12) available
        · vcgen [nextStates_reject_spec zero one nextBefore word tail
            (origin + 12 + (12 * number.length : Nat) + 12) available]
          all_goals
            simp_all
            all_goals ring_nf
            all_goals lia
      have hbudget : available + 8192 * (word.length + 1) *
          (nextBefore.length + word.length + 2) ^ 2 ≤
          elapsed + 8192 * ((pieceWord (.inr number) ++ word).length + 1) *
            (before.length + (pieceWord (.inr number) ++ word).length + 2) ^ 2 := by
        dsimp [available, nextBefore, crossed, pieceWord]
        simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
        ring_nf
        lia
      all_goals unfold nextStates
      all_goals vcgen [Spec.while_step_spec (loop := nextStates zero one) (hloop := rfl),
        checkPrefix_spec (tm := tm (Γ := Γ)) (.inl .initial) (.inl .header) (code .movementEnd)
          (encode (Γ := Γ)
            (CodeSymbol.movementEnd :: number.map CodeSymbol.digit ++ CodeSymbol.entryEnd :: word))
          (StackTape.prepend (encode (Γ := Γ) before).reverse StackTape.nil) tail
          (some (.inl .header)) origin elapsed,
        hstart, hfield,
        hend (some (.inl (if Computability.decodeNat number ≤ rows then .header else .reject))),
        hcontinue]
      all_goals
        simp_all [piecesWord_cons, pieceWord, NextValid, view,
          List.append_assoc, nextBefore, available, crossed, word, rows, List.count_append,
          List.count_cons, digit_rows,
          List.reverse_append]
        all_goals lia


private noncomputable def afterLargest (zero one : Γ) : Prog (TMQuery (tm (Γ := Γ))) Unit :=
    do [TMQuery (tm (Γ := Γ))]
  ifₜ (notₜ state =ₜ some (.inl .reject)) then
    moveCells tm .Right 12
    StateFields.check zero one .initial
    ifₜ (notₜ state =ₜ some (.inl .reject)) then
      moveCells tm .Right 12
      nextStates zero one
    else
      pure ()
  else
    pure ()

/--
This program checks every state reference in a structurally valid description. It compares
the largest state number and initial state with the table's row count, then reads the table
to find and check each next-state number. It preserves the description and restores the head.
State `header` means that all comparisons succeeded; state `reject` means that one failed.
The two counter digits are fixed once when constructing the program.
-/
noncomputable def checkStates (zero one : Γ) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
    do [TMQuery (Parsing.machine (Γ := Γ))]
  StateFields.check zero one .largest
  afterLargest zero one
  seekLeftEnd tm
  ifₜ (notₜ state =ₜ some (.inl .reject)) then
    state ←ₜ Sum.inl Parsing.Stage.header
  else
    pure ()

private def addMarker (marker : Γ) : Prog (TMQuery (tm (Γ := Γ))) Unit :=
    do [TMQuery (tm (Γ := Γ))]
  moveₜ .Left
  tape ←ₜ some marker
  moveₜ .Right

private def removeMarker : Prog (TMQuery (tm (Γ := Γ))) Unit :=
    do [TMQuery (tm (Γ := Γ))]
  moveₜ .Left
  tape ←ₜ none
  moveₜ .Right

/--
This program checks the field arrangement and then every state reference. It starts with the
input on an otherwise blank tape and leaves that input unchanged. It uses `time` to report
success and `reject` to report failure. Its digit choices are fixed independently of the input.
-/
noncomputable def check (zero one : Γ) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
    do [TMQuery (Parsing.machine (Γ := Γ))]
  addMarker zero
  Parsing.checkStructure
  removeMarker
  ifₜ state =ₜ some (.inl .time) then
    checkStates zero one
    ifₜ (notₜ state =ₜ some (.inl .reject)) then
      state ←ₜ Sum.inl Parsing.Stage.time
    else
      pure ()
  else
    state ←ₜ Sum.inl Parsing.Stage.reject

end Algolean.Algorithms.TMSATToSAT.Validation
