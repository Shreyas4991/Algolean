/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Tape
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading
public import Algolean.Problems.Encodings.TMSAT

/-!
# Reading the fields of an encoded TMSAT instance

The input describes a verifier, its input word, a certificate length, and a time bound.
Each symbol of this description is represented by a fixed-length word over `Γ`.
The reader compares those words using tape tests and records the symbol it found in its
finite control state. It preserves the input and the neighboring regions on the single tape.

The format states distinguish binary numbers, transition entries, rows of the transition
table, input symbols, and the two unary bounds. Reading a symbol in the wrong place enters
the rejection state. The control states count entries within a row because their number is
fixed by `Γ`. They also check input-symbol numbers against the fixed numbering of `Γ` used
by `encodingOver`.

The alphabet, symbol representations, and all comparison words are fixed before execution.
The number of states depends on `Γ`, independently of the verifier and input length.
The verifier description and the values of its fields are read from the tape.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Parsing

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet Problems.TMSAT
open Problems.TMSAT.CodeSymbol
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Fintype Γ]

/-- These states identify the part of the TMSAT description currently being read. -/
inductive Stage (Γ : Type) [Fintype Γ] where
  /-- Binary digits describe the verifier's largest state number. -/
  | header
  /-- Binary digits describe the verifier's initial state. -/
  | initial
  /-- The written cell value or movement begins at this fixed position within its row. -/
  | transitionStart (column : Fin (Fintype.card (Option (TapeSymbol Γ)))) (movement : Bool)
  /-- Binary digits record a written cell value or movement within the fixed alphabet bounds. -/
  | transitionDigits (column : Fin (Fintype.card (Option (TapeSymbol Γ)))) (movement : Bool)
      (value weight : Fin (Fintype.card (Option (TapeSymbol Γ)) + 1)) (last : Bool)
  /-- Binary digits describe the next state at this fixed position within its row. -/
  | entry (column : Fin (Fintype.card (Option (TapeSymbol Γ))))
  /-- All transitions in the row have been read, so its ending must appear. -/
  | rowClose
  /-- A separator must follow the completed row. -/
  | rowEnd
  /-- Another row may begin, or the table may end. -/
  | rowStart
  /-- A separator must follow the completed verifier description. -/
  | machineEnd
  /-- The next input symbol may begin, or the input word may end. -/
  | inputStart
  /--
  The input-symbol number is read from its least significant digit. `value` sums the one bits
  read so far, and `weight` is the next bit's place value, capped at the alphabet size.
  `last` records the last digit, which distinguishes the decoder's alternative number spellings.
  -/
  | inputDigits (value weight : Fin (Fintype.card Γ + 1)) (last : Bool)
  /-- The separator before the two bounds must appear. -/
  | boundsStart
  /-- One true digit is read for each permitted certificate symbol. -/
  | certificate
  /-- One true digit is read for each permitted transition. -/
  | time
  /-- An unexpected symbol or unrecognized symbol encoding has been read. -/
  | reject

instance : DecidableEq (Stage Γ) := by
  intro first second
  cases first <;> cases second <;>
    try first
      | exact isTrue rfl
      | (refine isFalse ?_; intro h; cases h; done)
  · rename_i firstColumn firstMovement secondColumn secondMovement
    exact decidable_of_iff
      (firstColumn = secondColumn ∧ firstMovement = secondMovement) (by simp)
  · rename_i firstColumn firstMovement firstValue firstWeight firstLast
      secondColumn secondMovement secondValue secondWeight secondLast
    exact decidable_of_iff
      (firstColumn = secondColumn ∧ firstMovement = secondMovement ∧ firstValue = secondValue ∧
        firstWeight = secondWeight ∧ firstLast = secondLast) (by simp)
  · rename_i first second
    exact decidable_of_iff (first = second) (by simp)
  · rename_i firstValue firstWeight firstLast secondValue secondWeight secondLast
    exact decidable_of_iff
      (firstValue = secondValue ∧ firstWeight = secondWeight ∧ firstLast = secondLast) (by simp)

/-- These are all the stages used to check the arrangement of fields. -/
def stages : List (Stage Γ) :=
  [.header, .initial, .rowClose, .rowEnd, .rowStart, .machineEnd,
    .inputStart, .boundsStart, .certificate, .time, .reject] ++
    (List.finRange (Fintype.card (Option (TapeSymbol Γ)))).flatMap (fun column =>
      [Stage.entry column, Stage.transitionStart column false, Stage.transitionStart column true] ++
      (List.finRange (Fintype.card (Option (TapeSymbol Γ)) + 1)).flatMap (fun value =>
        (List.finRange (Fintype.card (Option (TapeSymbol Γ)) + 1)).flatMap fun weight =>
          [Stage.transitionDigits column false value weight false,
           Stage.transitionDigits column false value weight true,
           Stage.transitionDigits column true value weight false,
           Stage.transitionDigits column true value weight true])) ++
    (List.finRange (Fintype.card Γ + 1)).flatMap (fun value =>
      (List.finRange (Fintype.card Γ + 1)).flatMap fun weight =>
        [Stage.inputDigits value weight false, Stage.inputDigits value weight true])

/-- Every field-reading state occurs in the fixed comparison list. -/
theorem mem_stages (label : Stage Γ) : label ∈ stages := by
  cases label with
  | inputDigits value weight last => cases last <;> simp [stages]
  | transitionStart column movement => cases movement <;> simp [stages]
  | transitionDigits column movement value weight last =>
    cases movement <;> cases last <;> simp [stages]
  | _ => simp [stages]

instance : Fintype (Stage Γ) := .ofList stages mem_stages

/-- The extra states remember which fixed symbol comparison just succeeded. -/
abbrev State (Γ : Type) [Fintype Γ] := Stage Γ ⊕ (Stage Γ × CodeSymbol)

variable [Inhabited Γ] [Nontrivial Γ]
variable [DecidableEq Γ]

/-- The finite control states accompany the Query program that reads the encoded description. -/
abbrev machine : SingleTapeTM Γ where
  State := State Γ
  q₀ := .inl .header
  tr _ symbol := (⟨symbol, none⟩, none)

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

private noncomputable def symbols : List CodeSymbol :=
  (Finset.univ : Finset CodeSymbol).toList

private def firstColumn : Fin (Fintype.card (Option (TapeSymbol Γ))) :=
  ⟨0, Fintype.card_pos⟩

private def afterEntry (column : Fin (Fintype.card (Option (TapeSymbol Γ)))) : Stage Γ :=
  if h : column.val + 1 < Fintype.card (Option (TapeSymbol Γ)) then
    .transitionStart ⟨column.val + 1, h⟩ false
  else .rowClose

private def transitionDigit (column : Fin (Fintype.card (Option (TapeSymbol Γ))))
    (movement : Bool) (value weight : Fin (Fintype.card (Option (TapeSymbol Γ)) + 1))
    (bit : Bool) : Stage Γ :=
  let next := value.val + if bit then weight.val else 0
  if h : next < Fintype.card (Option (TapeSymbol Γ)) then
    .transitionDigits column movement ⟨next, by lia⟩
      ⟨min (2 * weight.val) (Fintype.card (Option (TapeSymbol Γ))), by lia⟩ bit
  else .reject

private def startTransitionDigit (column : Fin (Fintype.card (Option (TapeSymbol Γ))))
    (movement bit : Bool) : Stage Γ :=
  transitionDigit column movement ⟨0, by lia⟩
    ⟨min 1 (Fintype.card (Option (TapeSymbol Γ))), by lia⟩ bit

private def afterTransitionField (column : Fin (Fintype.card (Option (TapeSymbol Γ))))
    (movement : Bool) : Stage Γ :=
  if movement then .entry column else .transitionStart column true

private def transitionEnding (movement : Bool) : CodeSymbol :=
  if movement then movementEnd else writeEnd

private def transitionBound (movement : Bool) : Nat :=
  if movement then 3 else Fintype.card (Option (TapeSymbol Γ))

private def inputDigit (value weight : Fin (Fintype.card Γ + 1)) (bit : Bool) : Stage Γ :=
  let next := value.val + if bit then weight.val else 0
  if h : next < Fintype.card Γ then
    .inputDigits ⟨next, by lia⟩
      ⟨min (2 * weight.val) (Fintype.card Γ), by lia⟩ bit
  else .reject

private def startInputDigit (bit : Bool) : Stage Γ :=
  inputDigit ⟨0, by lia⟩ ⟨min 1 (Fintype.card Γ), by lia⟩ bit

private def afterSymbol (label : Stage Γ) (symbol : CodeSymbol) : Stage Γ :=
  match label with
  | .header => if symbol = digit false ∨ symbol = digit true then .header
      else if symbol = headerEnd then .initial else .reject
  | .initial => if symbol = digit false ∨ symbol = digit true then .initial
      else if symbol = initialEnd then .transitionStart firstColumn false else .reject
  | .transitionStart column movement =>
      if symbol = digit false then startTransitionDigit column movement false
      else if symbol = digit true then startTransitionDigit column movement true
      else if symbol = transitionEnding movement then afterTransitionField column movement
      else .reject
  | .transitionDigits column movement value weight last =>
      if symbol = digit false then transitionDigit column movement value weight false
      else if symbol = digit true then transitionDigit column movement value weight true
      else if symbol = transitionEnding movement ∧
          (if last then value.val else value.val + weight.val) < transitionBound (Γ := Γ) movement
        then afterTransitionField column movement
      else .reject
  | .entry column =>
      if symbol = digit false ∨ symbol = digit true then .entry column
      else if symbol = entryEnd then afterEntry column else .reject
  | .rowClose => if symbol = listEnd then .rowEnd else .reject
  | .rowStart =>
      if symbol = digit false then startTransitionDigit firstColumn false false
      else if symbol = digit true then startTransitionDigit firstColumn false true
      else if symbol = writeEnd then .transitionStart firstColumn true
      else if symbol = tableEnd then .machineEnd else .reject
  | .rowEnd => if symbol = rowSeparator then .rowStart else .reject
  | .machineEnd => if symbol = fieldSeparator then .inputStart else .reject
  | .inputStart => if symbol = digit false then startInputDigit false
      else if symbol = digit true then startInputDigit true
      else if symbol = entryEnd ∧ 0 < Fintype.card Γ then .inputStart
      else if symbol = listEnd then .boundsStart else .reject
  | .inputDigits value weight last =>
      if symbol = digit false then inputDigit value weight false
      else if symbol = digit true then inputDigit value weight true
      else if symbol = entryEnd ∧
          (if last then value.val else value.val + weight.val) < Fintype.card Γ then .inputStart
      else .reject
  | .boundsStart => if symbol = boundsSeparator then .certificate else .reject
  | .certificate => if symbol = digit true then .certificate
      else if symbol = fieldSeparator then .time else .reject
  | .time => if symbol = digit true then .time else .reject
  | .reject => .reject

private noncomputable def chooseSymbol (label : Stage Γ) :
    List CodeSymbol → Prog (TMQuery (machine (Γ := Γ))) Unit
  | [] => do [TMQuery (machine (Γ := Γ))]
    state ←ₜ Sum.inl Stage.reject
    moveₜ .Right
  | symbol :: rest => do [TMQuery (machine (Γ := Γ))]
    checkPrefix (machine (Γ := Γ)) (.inr (label, symbol)) (.inl label) (code symbol)
    ifₜ state =ₜ some (Sum.inr (label, symbol)) then
      moveCells (machine (Γ := Γ)) .Right (code (Γ := Γ) symbol).length
      state ←ₜ Sum.inl (afterSymbol label symbol)
    else
      chooseSymbol label rest

private noncomputable def readOne : Prog (TMQuery (machine (Γ := Γ))) Unit :=
  select stages (fun label => .stateIs (some (.inl label)))
    (fun label => chooseSymbol label symbols)

private noncomputable def scanDescription : Prog (TMQuery (machine (Γ := Γ))) Unit :=
    do [TMQuery (machine (Γ := Γ))]
  whileₜ (notₜ tape =ₜ none) do
    readOne

/--
This fixed Query program reads the description's symbol encodings and field separators.
It preserves the tape and returns to the first input cell after its marker. The alphabet and
all comparison words are fixed once; tape tests select the comparisons during execution.
-/
noncomputable def checkStructure : Prog (TMQuery (machine (Γ := Γ))) Unit :=
    do [TMQuery (machine (Γ := Γ))]
  state ←ₜ Sum.inl Stage.header
  scanDescription
  seekLeftEnd (machine (Γ := Γ))
  moveₜ .Right

private noncomputable def firstSymbol
    (candidates : List CodeSymbol) (word : List Γ) : Option CodeSymbol :=
  candidates.find? (fun symbol => decide (code symbol <+: word))

private noncomputable def consumed (candidates : List CodeSymbol) (word : List Γ) : Nat :=
  ((firstSymbol candidates word).map fun symbol => (code (Γ := Γ) symbol).length).getD 1

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
        SingleTapeTM.Description.MovementSymbol, Extended]

omit [Inhabited Γ] [Fintype Γ] in
private theorem consumed_pos (candidates : List CodeSymbol) (word : List Γ) :
    0 < consumed candidates word := by
  unfold consumed
  cases firstSymbol candidates word <;> simp [code_length]

omit [Inhabited Γ] [Fintype Γ] in
private theorem consumed_le (candidates : List CodeSymbol) (word : List Γ) (hword : word ≠ []) :
    consumed candidates word ≤ word.length := by
  unfold consumed
  cases h : firstSymbol candidates word with
  | none =>
    have hpos := List.length_pos_iff.mpr hword
    simpa using (show 1 ≤ word.length by lia)
  | some symbol =>
    change candidates.find? (fun entry => decide (code entry <+: word)) = some symbol at h
    have hd : decide (code symbol <+: word) = true :=
      List.find?_some (p := fun entry => decide (code entry <+: word)) h
    have hp : code symbol <+: word := of_decide_eq_true hd
    simpa using hp.length_le

omit [Inhabited Γ] [Fintype Γ] in
private theorem firstSymbol_code (symbol : CodeSymbol) (suffix : List Γ) :
    firstSymbol symbols (code symbol ++ suffix) = some symbol := by
  have hprefix (candidate : CodeSymbol) :
      code candidate <+: code symbol ++ suffix ↔ candidate = symbol :=
    finiteWordsOver_symbol_prefix_iff candidate symbol suffix
  cases h : firstSymbol symbols (code symbol ++ suffix) with
  | none =>
    change symbols.find? (fun entry => decide (code entry <+: code symbol ++ suffix)) = none at h
    have hn := List.find?_eq_none.mp h symbol (by simp [symbols])
    simp at hn
  | some found =>
    change symbols.find? (fun entry => decide (code entry <+: code symbol ++ suffix)) =
      some found at h
    have hp : decide (code found <+: code symbol ++ suffix) = true :=
      List.find?_some (p := fun entry => decide (code entry <+: code symbol ++ suffix)) h
    have heq := (hprefix found).mp (of_decide_eq_true hp)
    simp [heq]

/-- Testing the fixed symbol list preserves the input and advances past the first match. -/
private theorem chooseSymbol_spec (label : Stage Γ) (candidates : List CodeSymbol)
    (left tail : StackTape Γ) (word : List Γ) (hword : word ≠ [])
    (previous : Option (State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨previous, BiTape.segment left word tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      chooseSymbol label candidates
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl ((firstSymbol candidates word).map (afterSymbol label) |>.getD .reject)),
          BiTape.segment
            (StackTape.prepend (word.take (consumed candidates word)).reverse left)
            (word.drop (consumed candidates word)) tail⟩ ∧
        final.headPos = origin + consumed candidates word ∧
        cost.steps ≤ elapsed +
          2 * (candidates.map fun symbol => (code (Γ := Γ) symbol).length).sum +
          consumed candidates word ⦄ := by
  induction candidates generalizing previous origin elapsed with
  | nil =>
    obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil hword
    vcgen [chooseSymbol]
    simp_all [firstSymbol, consumed, TMState.move, TMState.moveCost]
  | cons symbol rest ih =>
    rw [chooseSymbol]
    apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
      ⟨some (if code symbol <+: word then .inr (label, symbol) else .inl label),
        BiTape.segment left word tail⟩ ∧
      current.headPos = origin ∧ cost.steps ≤ elapsed + 2 * (code (Γ := Γ) symbol).length)
    · vcgen [checkPrefix_spec (tm := machine (Γ := Γ)) (.inr (label, symbol)) (.inl label)
        (code symbol) word left tail previous origin elapsed]
    · intro _
      apply Std.WP.Triple.intro
      rintro initial current ⟨hcfg, hpos, hbound⟩
      by_cases hp : code symbol <+: word
      · obtain ⟨suffix, rfl⟩ := hp
        have hfound : firstSymbol (symbol :: rest) (code symbol ++ suffix) = some symbol := by
          simp [firstSymbol]
        vcgen [Spec.branch_true_spec]
        refine ⟨by simp [hcfg], ?_⟩
        dsimp only [binderNameHint]
        vcgen [moveCells_spec (tm := machine (Γ := Γ)) .Right (code (Γ := Γ) symbol).length
            (BiTape.segment left (code symbol ++ suffix) tail) (some (.inr (label, symbol)))
            origin initial.steps]
        all_goals simp_all [consumed, BiTape.segment_moveRight_iterate]
        all_goals lia
      · vcgen [Spec.branch_false_spec]
        refine ⟨by simp [hcfg, hp], ?_⟩
        dsimp only [binderNameHint]
        vcgen [ih (some (.inl label)) origin
          (elapsed + 2 * (code (Γ := Γ) symbol).length)]
        all_goals simp_all [firstSymbol, consumed]
        all_goals lia

private theorem chooseSymbol_correct (label : Stage Γ) (candidates : List CodeSymbol)
    (left tail : StackTape Γ) (word : List Γ) (hword : word ≠ []) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment left word tail) :
    ∃ cost final, Completes (chooseSymbol label candidates) s cost final ∧
      final.config = ⟨some (.inl ((firstSymbol candidates word).map
          (afterSymbol label) |>.getD .reject)),
        BiTape.segment (StackTape.prepend (word.take (consumed candidates word)).reverse left)
          (word.drop (consumed candidates word)) tail⟩ ∧
      final.headPos = s.headPos + consumed candidates word ∧
      cost.steps ≤ 2 * (candidates.map fun symbol => (code (Γ := Γ) symbol).length).sum +
        consumed candidates word := by
  apply Spec.completes
  vcgen [chooseSymbol_spec label candidates left tail word hword s.config.state s.headPos 0]
  all_goals cases hcfg : s.config
  all_goals simp_all

private noncomputable def nextStage (label : Stage Γ) (word : List Γ) : Stage Γ :=
  ((firstSymbol symbols word).map (afterSymbol label)).getD .reject

private theorem readOne_correct (label : Stage Γ) (left tail : StackTape Γ)
    (word : List Γ) (hword : word ≠ []) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment left word tail)
    (hstate : s.config.state = some (.inl label)) :
    ∃ cost final, Completes readOne s cost final ∧
      final.config = ⟨some (.inl (nextStage label word)),
        BiTape.segment (StackTape.prepend (word.take (consumed symbols word)).reverse left)
          (word.drop (consumed symbols word)) tail⟩ ∧
      final.headPos = s.headPos + consumed symbols word ∧ cost.steps ≤ 300 := by
  obtain ⟨cost, final, hc, hcfg, hpos, hb⟩ :=
    chooseSymbol_correct label symbols left tail word hword s htape
  refine ⟨cost, final, ?_, hcfg, hpos, ?_⟩
  · exact select_correct stages _ _ label s final cost (mem_stages label)
      (by intro candidate; simp [hstate, eq_comm]) hc
  · have hsum : (symbols.map fun symbol => (code (Γ := Γ) symbol).length).sum = 144 := by
      simp [code_length, symbols, CodeSymbol, PayloadSymbol,
        SingleTapeTM.Description.CodeSymbol, SingleTapeTM.Description.BodySymbol,
        SingleTapeTM.Description.TableSymbol, SingleTapeTM.Description.RowSymbol,
        SingleTapeTM.Description.TransitionSymbol,
        SingleTapeTM.Description.MovementSymbol, Extended]
    have hcount : consumed symbols word ≤ 12 := by
      unfold consumed
      cases firstSymbol symbols word <;> simp [code_length]
    rw [hsum] at hb
    lia

private noncomputable def readStages (label : Stage Γ) (word : List Γ) : Stage Γ :=
  match word with
  | [] => label
  | first :: rest => readStages (nextStage label (first :: rest))
      ((first :: rest).drop (consumed symbols (first :: rest)))
termination_by word.length
decreasing_by
  have hp := consumed_pos symbols (first :: rest)
  simp only [List.length_drop]
  exact Nat.sub_lt (by simp) hp

omit [Inhabited Γ] in
private theorem readStages_encode (label : Stage Γ) (word : List CodeSymbol) :
    readStages label ((finiteWordsOver CodeSymbol Γ).encode word) =
      word.foldl afterSymbol label := by
  induction word generalizing label with
  | nil =>
    rw [encode_finiteWordsOver]
    simp [readStages]
  | cons symbol rest ih =>
    have hne : code (Γ := Γ) symbol ++ (finiteWordsOver CodeSymbol Γ).encode rest ≠ [] := by
      have hlen := code_length (Γ := Γ) symbol
      intro heq
      have h := congrArg List.length heq
      simp only [List.length_append, hlen, List.length_nil] at h
      lia
    rw [show (finiteWordsOver CodeSymbol Γ).encode (symbol :: rest) =
      code symbol ++ (finiteWordsOver CodeSymbol Γ).encode rest by
        simpa [code] using encode_finiteWordsOver_append (Γ := Γ) [symbol] rest]
    rw [readStages.eq_def]
    split
    · contradiction
    · rename_i first remaining heq
      rw [← heq]
      simp only [nextStage, firstSymbol_code, Option.map_some, Option.getD_some,
        consumed, List.drop_left, List.foldl_cons]
      exact ih _

omit [Inhabited Γ] in
private theorem readStages_reject (word : List Γ) :
    readStages (.reject : Stage Γ) word = .reject := by
  induction hn : word.length using Nat.strong_induction_on generalizing word with
  | h size ih =>
    cases word with
    | nil => rw [readStages]
    | cons first rest =>
      subst size
      rw [readStages]
      have hn : nextStage (.reject : Stage Γ) (first :: rest) = .reject := by
        unfold nextStage
        cases firstSymbol symbols (first :: rest) <;> rfl
      rw [hn]
      apply ih _ _ _ rfl
      simp only [List.length_drop]
      exact Nat.sub_lt (by simp) (consumed_pos symbols (first :: rest))

omit [Inhabited Γ] in
private theorem encode_of_readStages_ne_reject (label : Stage Γ) (word : List Γ)
    (hresult : readStages label word ≠ .reject) :
    ∃ original, word = (finiteWordsOver CodeSymbol Γ).encode original := by
  induction hn : word.length using Nat.strong_induction_on generalizing label word with
  | h size ih =>
    cases word with
    | nil =>
      refine ⟨[], ?_⟩
      rw [encode_finiteWordsOver]
      rfl
    | cons first rest =>
      subst size
      let word := first :: rest
      have hlen : 0 < consumed symbols word := consumed_pos symbols word
      cases hfound : firstSymbol symbols word with
      | none =>
        have hn : nextStage label word = .reject := by simp [nextStage, hfound]
        have hreject : readStages label word = .reject := by
          rw [readStages]
          simpa only [word, hn] using readStages_reject (word.drop (consumed symbols word))
        exact False.elim (hresult hreject)
      | some symbol =>
        have hp : code symbol <+: word := by
          change symbols.find? (fun entry => decide (code entry <+: word)) = some symbol at hfound
          have ht : decide (code symbol <+: word) = true :=
            List.find?_some (p := fun entry => decide (code entry <+: word)) hfound
          exact of_decide_eq_true ht
        obtain ⟨suffix, heq⟩ := hp
        have hcount : consumed symbols word = (code (Γ := Γ) symbol).length := by
          simp [consumed, hfound]
        have hsuffix : word.drop (consumed symbols word) = suffix := by
          rw [hcount, ← heq, List.drop_left]
        have hshort : suffix.length < word.length := by
          rw [← heq]
          simp only [List.length_append, code_length]
          lia
        have hnext : readStages (nextStage label word) suffix ≠ .reject := by
          have hstep : readStages label word =
              readStages (nextStage label word) (word.drop (consumed symbols word)) := by
            rw [readStages]
          change readStages label word ≠ .reject at hresult
          rw [hstep, hsuffix] at hresult
          exact hresult
        obtain ⟨original, horiginal⟩ := ih suffix.length hshort
          (nextStage label word) suffix hnext rfl
        refine ⟨symbol :: original, ?_⟩
        change word = _
        rw [← heq, horiginal]
        simpa [code] using
          (encode_finiteWordsOver_append (Γ := Γ) [symbol] original).symm

/--
This is the field-reading state reached after reading the description symbols in order.
The `time` state means the separators and unary bounds are correctly arranged and every table
row has the number of entries fixed by `Γ`. Input-symbol numbers must belong to `Γ`'s fixed
numbering. The header and transition entries are read as binary fields.
-/
def formatResult (word : List CodeSymbol) : Stage Γ := word.foldl afterSymbol .header

omit [Inhabited Γ] in
private theorem readStages_decode (word : List Γ) :
    readStages (.header : Stage Γ) word =
      match (finiteWordsOver CodeSymbol Γ).decode word with
      | none => .reject
      | some original => formatResult original := by
  cases hd : (finiteWordsOver CodeSymbol Γ).decode word with
  | none =>
    by_contra hne
    obtain ⟨original, rfl⟩ := encode_of_readStages_ne_reject .header word hne
    simp at hd
  | some original =>
    rw [(decode_finiteWordsOver_eq_some_iff.mp hd), readStages_encode]
    rfl

private theorem scanDescription_correct (label : Stage Γ) (left tail : StackTape Γ)
    (word : List Γ) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment left word tail)
    (hstate : s.config.state = some (.inl label)) :
    ∃ cost final, Completes scanDescription s cost final ∧
      final.config = ⟨some (.inl (readStages label word)),
        BiTape.segment (StackTape.prepend word.reverse left) [] tail⟩ ∧
      final.headPos = s.headPos + word.length ∧ cost.steps ≤ 300 * word.length := by
  induction hn : word.length using Nat.strong_induction_on generalizing label left word s with
  | h size ih =>
    cases word with
    | nil =>
      subst size
      refine ⟨0, s, completes_while_false _ _ s (by simp [htape]), ?_, by simp, by simp⟩
      rw [readStages]
      cases hs : s.config
      simp_all
    | cons first rest =>
      subst size
      let word := first :: rest
      let count := consumed symbols word
      have hp : 0 < count := consumed_pos symbols word
      have hle : count ≤ word.length := consumed_le symbols word (by simp [word])
      obtain ⟨cost, middle, hc, hmiddle, hmpos, hb⟩ :=
        readOne_correct label left tail word (by simp [word]) s htape hstate
      obtain ⟨more, final, hr, hfinal, hfpos, hbound⟩ :=
        ih (word.drop count).length (by simp only [List.length_drop]; dsimp [word] at *; lia)
          (nextStage label word) (StackTape.prepend (word.take count).reverse left)
          (word.drop count) middle
          (by simpa only [count] using congrArg SingleTapeTM.Cfg.BiTape hmiddle)
          (by simp [hmiddle]) rfl
      refine ⟨cost + more, final, Completes.while_step (by simp [htape]) hc hr, ?_, ?_, ?_⟩
      · rw [readStages]
        simpa [word, count, ← StackTape.prepend_append,
          ← List.reverse_append] using hfinal
      · simp only [List.length_drop] at hfpos
        rw [hfpos, hmpos]
        simp only [word, count, List.length_cons] at hle ⊢
        lia
      · have hfirst : cost.steps ≤ 300 * count :=
          hb.trans (Nat.le_mul_of_pos_right 300 hp)
        simp only [TMCost.add_steps]
        have htotal := Nat.add_le_add hfirst hbound
        simp only [List.length_drop] at htotal
        have heq : count + (word.length - count) = word.length := Nat.add_sub_of_le hle
        rw [← Nat.mul_add, heq] at htotal
        exact htotal

private theorem checkStructure_result (marker : Γ) (left tail : StackTape Γ)
    (word : List Γ) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.cons (some marker) (StackTape.cons none left)) word tail) :
    ∃ cost final, Completes checkStructure s cost final ∧
      final.config = ⟨some (.inl (readStages .header word)), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 301 * word.length + 4 := by
  let initial : TMState (machine (Γ := Γ)) :=
    {s with config := ⟨some (.inl .header), s.config.BiTape⟩}
  obtain ⟨cost, middle, hc, hmiddle, hpos, hb⟩ := scanDescription_correct .header
    (StackTape.cons (some marker) (StackTape.cons none left)) tail word initial
    (by simpa [initial] using htape) rfl
  apply Spec.completes
  vcgen [checkStructure, Spec.steps hc 0,
    seekLeftEnd_segment_spec (tm := machine (Γ := Γ)) left tail (word.reverse ++ [marker]) []
      (some (.inl (readStages .header word))) (s.headPos + word.length) cost.steps]
  all_goals cases word
  all_goals cases hcfg : s.config
  all_goals simp_all [initial, StackTape.prepend_append, BiTape.segment, BiTape.moveRight,
    TMState.move, TMState.moveCost, List.reverse_append]
  all_goals lia

/--
The structure check preserves every tape cell and returns to the first input cell after its
marker. For every word, including malformed words, it uses at most `301 * word.length + 4`
head moves. The words on either side of the input region remain unchanged.
-/
theorem checkStructure_time_bound (marker : Γ) (left tail : StackTape Γ)
    (word : List Γ) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.cons (some marker) (StackTape.cons none left)) word tail) :
    ∃ cost final, Completes checkStructure s cost final ∧
      final.config.BiTape = s.config.BiTape ∧ final.headPos = s.headPos ∧
      cost.steps ≤ 301 * word.length + 4 := by
  obtain ⟨cost, final, hc, hcfg, hpos, hb⟩ := checkStructure_result marker left tail word s htape
  exact ⟨cost, final, hc, by simpa using congrArg SingleTapeTM.Cfg.BiTape hcfg, hpos, hb⟩

/--
The Query program has the same result as decoding the fixed-length symbol representations
and reading the resulting description symbols with `formatResult`. An unrecognized or
incomplete symbol representation gives the rejection state. Every tape cell is preserved.
-/
theorem checkStructure_correct (marker : Γ) (left tail : StackTape Γ)
    (word : List Γ) (s : TMState (machine (Γ := Γ)))
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.cons (some marker) (StackTape.cons none left)) word tail) :
    ∃ cost final, Completes checkStructure s cost final ∧
      final.config = ⟨some (.inl (match (finiteWordsOver CodeSymbol Γ).decode word with
        | none => .reject
        | some original => formatResult original)), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 301 * word.length + 4 := by
  obtain ⟨cost, final, hc, hcfg, hpos, hb⟩ := checkStructure_result marker left tail word s htape
  refine ⟨cost, final, hc, ?_, hpos, hb⟩
  rw [readStages_decode] at hcfg
  exact hcfg

end Algolean.Algorithms.TMSATToSAT.Parsing
