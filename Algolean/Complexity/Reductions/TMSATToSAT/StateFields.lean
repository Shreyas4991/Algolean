/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.StateBounds
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Writing
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Checking the numbers that refer to verifier states

The largest state number must be one less than the table's row count. The initial state must
be smaller than that count. A transition's next-state code may be zero for halting; otherwise
it is one more than the state number and must be at most the row count.

The machine copies each number into a binary counter and compares it with the actual rows.
It temporarily changes the field's ending to the header separator so it can find that position
after scanning the table. It chooses the last header separator, since the original one lies
earlier. It restores the original ending and erases the counter before returning.

* `FieldInput` records the starting tape and head position and requires an empty counter.
* `ReadCounterResult` records the copied number and the head at its ending.
* `ReadAndScanResult` records the counter after subtracting the row count.
* `CheckResult` records the restored description, cleared counter, and decision.

The specifications state these properties and give the time bounds separately.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.StateFields

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet Problems.TMSAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ]

/-- These three fields use different comparisons with the number of transition-table rows. -/
inductive Field where
  /-- This records the largest state number. There must be exactly one more row. -/
  | largest
  /-- This records the initial state number, which must have a row in the table. -/
  | initial
  /-- This records halting as zero or a next state as one more than its number. -/
  | next
  deriving DecidableEq

/-- This is the symbol that ends the selected kind of state field. -/
@[expose] def Field.ending : Field → CodeSymbol
  | .largest => .headerEnd
  | .initial => .initialEnd
  | .next => .entryEnd

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
    SingleTapeTM.Description.MovementSymbol, Extended]

private noncomputable def replaceCode (symbol : CodeSymbol) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  writeRight (Parsing.machine (Γ := Γ)) (code symbol)
  moveCells (Parsing.machine (Γ := Γ)) .Left 12

private theorem replaceCode_spec (replacement old : CodeSymbol)
    (left tail : StackTape Γ) (suffix : List Γ) (label : Option (Parsing.State Γ))
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment left (code old ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      replaceCode (Γ := Γ) replacement
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment left (code replacement ++ suffix) tail⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 24 ⦄ := by
  have hmove : BiTape.moveLeft^[12]
      (BiTape.segment (StackTape.prepend (code replacement).reverse left) suffix tail) =
      BiTape.segment left (code replacement ++ suffix) tail := by
    rw [← code_length (Γ := Γ) replacement, BiTape.segment_moveLeft_iterate]
  vcgen [replaceCode,
    writeRight_overwrite_spec (tm := Parsing.machine (Γ := Γ)) left tail
      (code replacement) (code old) suffix (by rw [code_length, code_length]) label origin elapsed,
    moveCells_spec (tm := Parsing.machine (Γ := Γ)) .Left 12
      (BiTape.segment (StackTape.prepend (code replacement).reverse left) suffix tail)
      label (origin + 12) (elapsed + 12)]
  all_goals simp_all [code_length]

private noncomputable def returnToField (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  findPreviousWord (Parsing.machine (Γ := Γ)) (.inl .initial) (.inl .header) (code .headerEnd)
  replaceCode (Field.ending field)

private theorem returnToField_spec (field : Field) (after : List CodeSymbol)
    (hafter : CodeSymbol.headerEnd ∉ after) (left tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend (code CodeSymbol.headerEnd ++ after.flatMap code).reverse left)
        [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      returnToField (Γ := Γ) field
    ⦃ fun _ cost final => final.config = ⟨some (.inl .initial),
        BiTape.segment left (code (Field.ending field) ++ after.flatMap code) tail⟩ ∧
        final.headPos = origin - 12 * (after.length + 1) ∧
        cost.steps ≤ elapsed + 36 * (after.length + 1) + 24 ⦄ := by
  have hblocks : ∀ block ∈ after.map (code (Γ := Γ)),
      block.length = (code (Γ := Γ) CodeSymbol.headerEnd).length ∧
        block ≠ code CodeSymbol.headerEnd := by
    intro block hblock
    obtain ⟨symbol, hmem, rfl⟩ := List.mem_map.mp hblock
    refine ⟨by rw [code_length, code_length], ?_⟩
    intro he
    have heq := (finiteWordsOver CodeSymbol Γ).encode_injective he
    have hs : symbol = CodeSymbol.headerEnd := by simpa using heq
    subst symbol
    exact hafter hmem
  unfold returnToField
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨some (.inl .initial),
      BiTape.segment left (code CodeSymbol.headerEnd ++ after.flatMap code) tail⟩ ∧
    current.headPos = origin - 12 * (after.length + 1) ∧
    cost.steps ≤ elapsed + 36 * (after.length + 1))
  · vcgen [findPreviousWord_spec (tm := Parsing.machine (Γ := Γ))
      (.inl .initial) (.inl .header) (by simp) (code CodeSymbol.headerEnd)
      (after.map code) hblocks left tail [] label origin elapsed]
    all_goals simp_all [code_length, List.flatMap_def]
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    vcgen [replaceCode_spec (Field.ending field) CodeSymbol.headerEnd left tail (after.flatMap code)
      (some (.inl .initial)) (origin - 12 * (after.length + 1)) initial.steps]
    all_goals simp_all

private noncomputable def incrementCounter (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  visitPreviousRegion (Parsing.machine (Γ := Γ)) ((code (Field.ending field)).headD zero)
    (incrementLeft (Parsing.machine (Γ := Γ)) zero one)

private noncomputable def clearCounter (zero : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  visitPreviousRegion (Parsing.machine (Γ := Γ)) ((code (Field.ending field)).headD zero)
    (eraseRight (Parsing.machine (Γ := Γ)))

private def counterView (counter crossed remaining : List Γ) (tail : StackTape Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome counter.reverse)))
    remaining tail

/--
This describes the counter and a number field on the same tape. The counter contains `bits`,
and `before` and `after` contain the surrounding description symbols. The head is on the first
binary digit of `number`, or on the field's ending when `number` is empty.
-/
@[expose] noncomputable def fieldTape (zero one : Γ) (bits : List Bool) (field : Field)
    (before after : List CodeSymbol) (number : List Bool) (tail : StackTape Γ) : BiTape Γ :=
  let encode := (finiteWordsOver CodeSymbol Γ).encode
  BiTape.segment (StackTape.prepend (encode before).reverse
    (StackTape.cons none
      (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse)))
    (encode (number.map CodeSymbol.digit ++ Field.ending field :: after)) tail

/-- This states whether a field's number is allowed for a table with `rows` rows. -/
@[expose] def Field.Valid (field : Field) (value rows : Nat) : Prop :=
  match field with
  | .largest => value + 1 = rows
  | .initial => value < rows
  | .next => value ≤ rows

/--
The counter is empty, the head is at the number field, and the control state and head coordinate
have the stated values. The words `before` and `after` describe the rest of the encoded instance.
-/
@[expose] def FieldInput (zero one : Γ) (field : Field) (before after : List CodeSymbol)
    (number : List Bool) (tail : StackTape Γ) (label : Option (Parsing.State Γ))
    (origin : ℤ) (current : TMState (Parsing.machine (Γ := Γ))) : Prop :=
  current.config = ⟨label, fieldTape zero one [] field before after number tail⟩ ∧
    current.headPos = origin

/--
The number has been copied to the counter, adding one for a largest-state or initial-state field.
The encoded description is preserved, the head is on the field's ending, and the counter has
at most two more digits than the original number. The control state records that reading finished.
-/
@[expose] def ReadCounterResult (zero one : Γ) (field : Field) (before after : List CodeSymbol)
    (number : List Bool) (tail : StackTape Γ) (origin : ℤ)
    (final : TMState (Parsing.machine (Γ := Γ))) : Prop :=
  ∃ bits, final.config = ⟨some (.inl .initial),
      fieldTape zero one bits field (before ++ number.map CodeSymbol.digit) after [] tail⟩ ∧
    final.headPos = origin + 12 * number.length ∧
    binaryValue bits.reverse = Computability.decodeNat number +
      (if field = .next then 0 else 1) ∧ bits.length ≤ number.length + 2

/--
The table's row count has been subtracted from the counter, stopping at zero. The state records
whether there were more rows than the starting counter value. The description is preserved with
the checked field's ending temporarily changed to `headerEnd`, and the head is on its final blank.
The counter still has at most two more digits than the original number.
-/
@[expose] def ReadAndScanResult (zero one : Γ) (field : Field) (before after : List CodeSymbol)
    (number : List Bool) (tail : StackTape Γ) (origin : ℤ)
    (final : TMState (Parsing.machine (Γ := Γ))) : Prop :=
  let rows := (before ++ after).count CodeSymbol.rowSeparator
  let value := Computability.decodeNat number + if field = .next then 0 else 1
  let encode := (finiteWordsOver CodeSymbol Γ).encode
  ∃ bits : List Bool,
    final.config = ⟨some (.inl (if value < rows then .reject else .header)),
      BiTape.segment (StackTape.prepend
        (encode (before ++ number.map CodeSymbol.digit ++ CodeSymbol.headerEnd :: after)).reverse
        (StackTape.cons none
          (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse))) [] tail⟩ ∧
    final.headPos = origin + 12 * (number.length + after.length + 1) ∧
    binaryValue bits.reverse = value - rows ∧ bits.length ≤ number.length + 2

open scoped Classical in
/--
The counter is empty, the description is restored, and the head is on the field's ending.
The state is `header` exactly when the number satisfies `Field.Valid`; otherwise it is `reject`.
-/
@[expose] def CheckResult (zero one : Γ) (field : Field) (before after : List CodeSymbol)
    (number : List Bool) (tail : StackTape Γ) (origin : ℤ)
    (final : TMState (Parsing.machine (Γ := Γ))) : Prop :=
  let rows := (before ++ after).count CodeSymbol.rowSeparator
  let value := Computability.decodeNat number
  final.config = ⟨some (.inl (if Field.Valid field value rows then .header else .reject)),
      fieldTape zero one [] field (before ++ number.map CodeSymbol.digit) after [] tail⟩ ∧
    final.headPos = origin + ((finiteWordsOver CodeSymbol Γ).encode
      (number.map CodeSymbol.digit)).length

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem fieldTape_eq (zero one : Γ) (bits : List Bool) (field : Field)
    (before after : List CodeSymbol) (number : List Bool) (tail : StackTape Γ) :
    fieldTape zero one bits field before after number tail =
      counterView (bits.map (fun bit => if bit then one else zero)) (before.flatMap code)
        ((number.map CodeSymbol.digit).flatMap code ++ code (Field.ending field) ++
          after.flatMap code) tail := by
  have hbytes (word : List CodeSymbol) :
      (finiteWordsOver CodeSymbol Γ).encode word = word.flatMap code := encode_finiteWordsOver word
  simp [fieldTape, counterView, hbytes, List.append_assoc]

omit [Nontrivial Γ] in
private theorem eraseRight_bound_spec (counter : List Γ) (right : StackTape Γ)
    (label : Option (Parsing.State Γ)) (position : ℤ) (spent : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil counter right⟩ ∧
        current.headPos = position ∧ cost.steps ≤ spent ⦄
      eraseRight (Parsing.machine (Γ := Γ))
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil [] right⟩ ∧
        final.headPos = position + counter.length ∧ cost.steps ≤ spent + counter.length ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  vcgen [eraseRight_spec (tm := Parsing.machine (Γ := Γ)) counter right label
    position initial.steps]
  all_goals simp_all

private theorem clearCounter_spec (zero : Γ) (field : Field)
    (counter crossed suffix : List Γ) (tail : StackTape Γ) (label : Option (Parsing.State Γ))
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, counterView counter crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      clearCounter zero field
    ⦃ fun _ cost final => final.config =
        ⟨label, counterView [] crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 6 ⦄ := by
  obtain ⟨restore, rest, hcode⟩ : ∃ restore rest,
      code (Γ := Γ) (Field.ending field) = restore :: rest :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by rw [code_length]; decide))
  unfold clearCounter
  simp only [hcode, List.headD_cons]
  vcgen [visitPreviousRegion_spec (tm := Parsing.machine (Γ := Γ)) restore
    (eraseRight (Parsing.machine (Γ := Γ))) counter [] crossed (rest ++ suffix) tail
    counter.length label label origin elapsed (by
      intro right position spent
      simpa using eraseRight_bound_spec counter right label position spent)]
  all_goals simp_all [counterView]
  all_goals lia

omit [Nontrivial Γ] in
private theorem incrementLeft_bound_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (right : StackTape Γ) (label : Option (Parsing.State Γ)) (position : ℤ) (spent : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) right⟩ ∧
        current.headPos = position ∧ cost.steps ≤ spent ⦄
      incrementLeft (Parsing.machine (Γ := Γ)) zero one
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil
        ((incrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)) right⟩ ∧
        final.headPos = position + bits.length - (incrementBits bits.reverse).length ∧
        cost.steps ≤ spent + (4 * bits.length + 5) ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  have hcount := carryCount_le_length bits.reverse
  have hlength := length_incrementBits_le bits.reverse
  vcgen [incrementLeft_spec (counter := Parsing.machine (Γ := Γ)) zero one hne bits right
    label position initial.steps]
  all_goals simp_all
  all_goals lia

private theorem incrementCounter_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (bits : List Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, counterView (bits.map (fun bit => if bit then one else zero))
          crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      incrementCounter zero one field
    ⦃ fun _ cost final => final.config =
        ⟨label, counterView ((incrementBits bits.reverse).reverse.map
          (fun bit => if bit then one else zero))
          crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 6 * bits.length + 12 ⦄ := by
  let output := (incrementBits bits.reverse).reverse.map (fun bit => if bit then one else zero)
  obtain ⟨restore, rest, hcode⟩ : ∃ restore rest,
      code (Γ := Γ) (Field.ending field) = restore :: rest :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by rw [code_length]; decide))
  have hlength := length_incrementBits_le bits.reverse
  unfold incrementCounter
  simp only [hcode, List.headD_cons]
  vcgen [visitPreviousRegion_spec (tm := Parsing.machine (Γ := Γ)) restore
    (incrementLeft (Parsing.machine (Γ := Γ)) zero one)
    (bits.map (fun bit => if bit then one else zero)) output crossed (rest ++ suffix) tail
    (4 * bits.length + 5) label label origin elapsed (by
      intro right position spent
      simpa only [List.length_map, List.length_reverse, output] using
        incrementLeft_bound_spec zero one hne bits right label position spent)]
  all_goals simp_all [counterView, output]
  all_goals lia

private noncomputable def finishKnown (zero : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  returnToField field
  clearCounter zero field
  state ←ₜ .inl (if field = .largest then .reject else .header)

private noncomputable def finishEqual (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  returnToField field
  visitPreviousRegion (Parsing.machine (Γ := Γ)) ((code (Field.ending field)).headD zero)
    (testZero (Parsing.machine (Γ := Γ)) one (.inl .header) (.inl .reject))
  clearCounter zero field

private theorem finishKnown_spec (zero : Γ) (field : Field)
    (counter crossed : List Γ) (after : List CodeSymbol) (hafter : CodeSymbol.headerEnd ∉ after)
    (tail : StackTape Γ) (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, counterView counter
        (crossed ++ code CodeSymbol.headerEnd ++ after.flatMap code) [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finishKnown zero field
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if field = .largest then .reject else .header)),
          counterView [] crossed (code (Field.ending field) ++ after.flatMap code) tail⟩ ∧
        final.headPos = origin - 12 * (after.length + 1) ∧
        cost.steps ≤ elapsed + 36 * (after.length + 1) +
          2 * crossed.length + 2 * counter.length + 30 ⦄ := by
  vcgen [finishKnown, returnToField_spec field after hafter
      (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome counter.reverse)))
      tail label origin elapsed,
    clearCounter_spec zero field counter crossed (after.flatMap code) tail (some (.inl .initial))
      (origin - 12 * (after.length + 1)) (elapsed + 36 * (after.length + 1) + 24)]
  all_goals simp_all [counterView, List.reverse_append, StackTape.prepend_append]
  all_goals lia

omit [Nontrivial Γ] in
private theorem testZero_bound_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (right : StackTape Γ) (label : Option (Parsing.State Γ)) (position : ℤ) (spent : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) right⟩ ∧
        current.headPos = position ∧ cost.steps ≤ spent ⦄
      testZero (Parsing.machine (Γ := Γ)) one (.inl .header) (.inl .reject)
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then .inl .header else .inl .reject),
          BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero)) right⟩ ∧
        final.headPos = position ∧ cost.steps ≤ spent + (2 * bits.length + 2) ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  vcgen [testZero_spec (tm := Parsing.machine (Γ := Γ)) zero one hne
    (.inl .header) (.inl .reject) (by simp) bits right label position initial.steps]
  all_goals simp_all
  all_goals lia

private theorem finishEqual_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (bits : List Bool) (crossed : List Γ) (after : List CodeSymbol)
    (hafter : CodeSymbol.headerEnd ∉ after) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, counterView (bits.map (fun bit => if bit then one else zero))
          (crossed ++ code CodeSymbol.headerEnd ++ after.flatMap code) [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finishEqual zero one field
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then .inl .header else .inl .reject),
          counterView [] crossed (code (Field.ending field) ++ after.flatMap code) tail⟩ ∧
        final.headPos = origin - 12 * (after.length + 1) ∧
        cost.steps ≤ elapsed + 36 * (after.length + 1) +
          4 * crossed.length + 6 * bits.length + 38 ⦄ := by
  let counter := bits.map (fun bit => if bit then one else zero)
  let answer : Option (Parsing.State Γ) :=
    some (if binaryValue bits.reverse = 0 then .inl .header else .inl .reject)
  obtain ⟨restore, rest, hcode⟩ : ∃ restore rest,
      code (Γ := Γ) (Field.ending field) = restore :: rest :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by rw [code_length]; decide))
  unfold finishEqual
  simp only [hcode, List.headD_cons]
  vcgen [returnToField_spec field after hafter
      (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome counter.reverse)))
      tail label origin elapsed,
    visitPreviousRegion_spec (tm := Parsing.machine (Γ := Γ)) restore
      (testZero (Parsing.machine (Γ := Γ)) one (.inl .header) (.inl .reject))
      counter counter crossed (rest ++ after.flatMap code) tail (2 * bits.length + 2)
      (some (.inl .initial)) answer (origin - 12 * (after.length + 1))
      (elapsed + 36 * (after.length + 1) + 24) (by
        intro right position spent
        simpa [counter, answer] using
          testZero_bound_spec zero one hne bits right (some (.inl .initial)) position spent),
    clearCounter_spec zero field counter crossed (after.flatMap code) tail answer
      (origin - 12 * (after.length + 1))
      (elapsed + 36 * (after.length + 1) + 24 + (2 * bits.length + 2) +
        2 * crossed.length + 2 * bits.length + 6)]
  all_goals simp_all [counterView, counter, answer, List.reverse_append,
    StackTape.prepend_append]
  all_goals lia
private noncomputable def adjustCounter (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  if field ≠ .next then incrementCounter zero one field else pure ()

private noncomputable def readCounter (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  Fields.readNumber zero one (Field.ending field)
  adjustCounter zero one field

private def adjustedBits (field : Field) (bits : List Bool) : List Bool :=
  if field = .next then bits else (incrementBits bits.reverse).reverse

private theorem adjustCounter_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (bits : List Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, counterView (bits.map (fun bit => if bit then one else zero))
          crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      adjustCounter zero one field
    ⦃ fun _ cost final => final.config =
        ⟨label, counterView ((adjustedBits field bits).map (fun bit => if bit then one else zero))
          crossed (code (Field.ending field) ++ suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 6 * bits.length + 12 ⦄ := by
  unfold adjustCounter
  by_cases hfield : field = .next
  · simp only [hfield, ne_eq, not_true_eq_false, ↓reduceIte]
    vcgen
    simp_all [adjustedBits]
    lia
  · simp only [hfield, ne_eq, not_false_eq_true, ↓reduceIte]
    vcgen [incrementCounter_spec zero one hne field bits crossed suffix tail label origin elapsed]
    all_goals simp_all [adjustedBits]

private theorem readCounter_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (before after : List CodeSymbol) (number : List Bool) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => FieldInput zero one field before after number tail label origin current ∧
        cost.steps ≤ elapsed ⦄
      readCounter zero one field
    ⦃ fun _ cost final => ReadCounterResult zero one field before after number tail origin final ∧
        cost.steps ≤ elapsed + 128 * (before.length + number.length + 1) ^ 2 ⦄ := by
  simp only [FieldInput, ReadCounterResult, ← exists_and_right, and_assoc, fieldTape_eq,
    List.flatMap_append, List.map_nil, List.flatMap_nil, List.nil_append]
  have hending : ∀ bit, Field.ending field ≠ CodeSymbol.digit bit := by
    intro bit
    cases field <;> cases bit <;> decide
  have hbytes (word : List CodeSymbol) :
      (finiteWordsOver CodeSymbol Γ).encode word = word.flatMap code := encode_finiteWordsOver word
  have hlength (word : List CodeSymbol) :
      (word.flatMap (code (Γ := Γ))).length = 12 * word.length := by
    rw [List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  let crossed : List Γ := before.flatMap code ++ (number.map CodeSymbol.digit).flatMap code
  let readBound := (number.length + 1) * (2 * ((before.flatMap (code (Γ := Γ))).length +
    13 * number.length) + 80)
  have hbudget : readBound + 2 * crossed.length + 6 * (number.length + 1) + 12 ≤
      128 * (before.length + number.length + 1) ^ 2 := by
    dsimp only [readBound, crossed]
    simp only [hlength, List.length_append, List.length_map]
    nlinarith
  unfold readCounter
  apply Std.WP.Triple.bind (mid := fun _ cost current => ∃ readBits : List Bool,
    current.config = ⟨some (.inl .initial), counterView
      (readBits.map (fun bit => if bit then one else zero)) crossed
      (code (Field.ending field) ++ after.flatMap code) tail⟩ ∧
    current.headPos = origin + 12 * number.length ∧
    binaryValue readBits.reverse = Computability.decodeNat number ∧
    readBits.length ≤ number.length + 1 ∧ cost.steps ≤ elapsed + readBound)
  · vcgen [Fields.readNumber_spec zero one (Field.ending field) hending number
      (before.flatMap code) (after.flatMap code) tail label origin elapsed]
    case vc1 => simp_all [counterView]
    case vc2 =>
      rename_i hpost
      obtain ⟨bits, hcfg, hpos, hvalue, hbits, htime⟩ := hpost
      refine ⟨bits, ?_⟩
      simp_all [counterView, crossed, readBound, binaryValue_eq_ofDigits]
      simp [code_length, List.sum_replicate, Function.comp_def]
      ring
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨readBits, hcfg, hpos, hvalue, hbits, htime⟩
    have hresult : binaryValue (adjustedBits field readBits).reverse =
        Computability.decodeNat number + if field = .next then 0 else 1 := by
      by_cases hfield : field = .next <;>
        simp [adjustedBits, hfield, binaryValue_incrementBits, hvalue]
    have hresultLength : (adjustedBits field readBits).length ≤ number.length + 2 := by
      have hinc := length_incrementBits_le readBits.reverse
      simp only [List.length_reverse] at hinc
      by_cases hfield : field = .next <;>
        simp only [adjustedBits, hfield, ↓reduceIte, List.length_reverse] <;> lia
    vcgen [adjustCounter_spec zero one hne field readBits crossed (after.flatMap code) tail
      (some (.inl .initial)) (origin + 12 * number.length) (elapsed + readBound)]
    case vc1 => simp_all
    case vc2 =>
      refine ⟨adjustedBits field readBits, ?_⟩
      simp_all [counterView, readBound, crossed]
      lia

private noncomputable def readAndScan (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  readCounter zero one field
  replaceCode .headerEnd
  seekLeftEnd (Parsing.machine (Γ := Γ))
  state ←ₜ .inl .header
  StateBounds.scanRows zero one

private theorem readAndScan_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (before after : List CodeSymbol) (number : List Bool) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => FieldInput zero one field before after number tail label origin current ∧
        cost.steps ≤ elapsed ⦄
      readAndScan zero one field
    ⦃ fun _ cost final => ReadAndScanResult zero one field before after number tail origin final ∧
        cost.steps ≤ elapsed + 2048 * (before.length + number.length + after.length + 2) ^ 2 ⦄ := by
  simp only [FieldInput, ReadAndScanResult, ← exists_and_right, and_assoc, fieldTape_eq,
    List.map_nil]
  have hbytes (word : List CodeSymbol) :
      (finiteWordsOver CodeSymbol Γ).encode word = word.flatMap code := encode_finiteWordsOver word
  have hlength (word : List CodeSymbol) :
      (word.flatMap (code (Γ := Γ))).length = 12 * word.length := by
    rw [List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  simp only [hbytes, List.flatMap_append, List.flatMap_cons]
  let crossed : List Γ := before.flatMap code ++ (number.map CodeSymbol.digit).flatMap code
  let readBound := 128 * (before.length + number.length + 1) ^ 2
  unfold readAndScan
  apply Std.WP.Triple.bind (mid := fun _ cost current => ∃ initialBits : List Bool,
    current.config = ⟨some (.inl .initial), counterView
      (initialBits.map (fun bit => if bit then one else zero)) crossed
      (code (Field.ending field) ++ after.flatMap code) tail⟩ ∧
    current.headPos = origin + 12 * number.length ∧
    binaryValue initialBits.reverse = Computability.decodeNat number +
      (if field = .next then 0 else 1) ∧ initialBits.length ≤ number.length + 2 ∧
    cost.steps ≤ elapsed + readBound)
  · vcgen [readCounter_spec zero one hne field before after number tail label origin elapsed]
    all_goals simp_all [FieldInput, ReadCounterResult, fieldTape_eq, readBound, crossed, add_assoc]
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨initialBits, hcfg, hpos, hvalue, hbits, htime⟩
    let word := before ++ number.map CodeSymbol.digit ++ CodeSymbol.headerEnd :: after
    have hrows : word.count CodeSymbol.rowSeparator =
        (before ++ after).count CodeSymbol.rowSeparator := by
      have hnone : (number.map CodeSymbol.digit).count CodeSymbol.rowSeparator = 0 := by
        apply List.count_eq_zero.mpr
        simp only [List.mem_map]
        rintro ⟨bit, _, he⟩
        cases bit <;> cases he
      simp only [word, List.count_append, hnone,
        List.count_cons_of_ne (by decide : CodeSymbol.headerEnd ≠ CodeSymbol.rowSeparator),
        Nat.add_zero]
    have hscan : 64 * word.length * (initialBits.length + 13 * word.length + 1) ≤
        64 * word.length * (number.length + 2 + 13 * word.length + 1) := by gcongr
    have hbudget : readBound + 24 + crossed.length + 2 +
        64 * word.length * (initialBits.length + 13 * word.length + 1) ≤
        2048 * (before.length + number.length + after.length + 2) ^ 2 := by
      dsimp only [readBound, crossed, word]
      simp only [hlength, List.length_append, List.length_cons, List.length_map]
      dsimp only [word] at hscan
      simp only [List.length_append, List.length_cons, List.length_map] at hscan
      nlinarith only [hscan]
    vcgen [replaceCode_spec CodeSymbol.headerEnd (Field.ending field)
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome
          (initialBits.map (fun bit => if bit then one else zero)).reverse)))
        tail (after.flatMap code) (some (.inl .initial))
        (origin + 12 * number.length) initial.steps,
      seekLeftEnd_segment_spec (tm := Parsing.machine (Γ := Γ))
        (StackTape.mapSome (initialBits.map (fun bit => if bit then one else zero)).reverse)
        tail crossed.reverse (code CodeSymbol.headerEnd ++ after.flatMap code)
        (some (.inl .initial)) (origin + 12 * number.length) (initial.steps + 24),
      StateBounds.scanRows_spec zero one hne initialBits word tail
        (origin + 12 * number.length - crossed.length)
        (initial.steps + 24 + crossed.length + 2)]
    case vc1 => simp_all [counterView]
    case vc2 => simp_all [counterView]
    case vc3 =>
      simp_all [counterView, word, crossed, List.append_assoc]
      lia
    case vc4 =>
      rename_i hpost
      obtain ⟨bits, hfinal, hfinalPos, hfinalValue, hfinalLength, hfinalTime⟩ := hpost
      refine ⟨bits, ?_, ?_, ?_, by lia, ?_⟩
      · rw [hvalue, hrows] at hfinal
        simpa [counterView, hbytes, word, crossed, List.append_assoc] using hfinal
      · simp only [hbytes, hlength, word, crossed, List.length_append, List.length_cons,
          List.length_map] at hfinalPos
        push_cast at hfinalPos
        lia
      · simpa [hvalue, hrows] using hfinalValue
      · lia

/--
This machine template checks one binary state field against the transition-table rows.
It starts on the field's first digit and finishes on its ending symbol. It preserves the
encoded description and clears its temporary counter. State `header` means that the number
is valid, and state `reject` means that it is invalid.

The containing machine fixes the two counter digits and the kind of field once. The number
and transition table are read from the tape by the same finite program on every input length.
-/
noncomputable def check (zero one : Γ) (field : Field) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  readAndScan zero one field
  ifₜ state =ₜ some (.inl .reject) then
    finishKnown zero field
  else
    finishEqual zero one field

open scoped Classical in
/--
The checker reports exactly the comparison required by the selected state field. It preserves
all encoded symbols, clears the initially empty counter, and stops on the field's ending.
The symbols before and after the number describe the rest of the instance. There must be no
header separator after the checked field, so the temporary replacement can be found again.
The bound is quadratic in the number of encoded symbols and does not depend on the number's value.
-/
@[spec] theorem check_spec (zero one : Γ) (hne : zero ≠ one) (field : Field)
    (before after : List CodeSymbol) (number : List Bool)
    (hafter : CodeSymbol.headerEnd ∉ after) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => FieldInput zero one field before after number tail label origin current ∧
        cost.steps ≤ elapsed ⦄
      check zero one field
    ⦃ fun _ cost final => CheckResult zero one field before after number tail origin final ∧
        cost.steps ≤ elapsed + 4096 * (before.length + number.length + after.length + 2) ^ 2 ⦄ := by
  simp only [FieldInput, CheckResult, and_assoc, fieldTape_eq,
    List.flatMap_append, List.map_nil, List.flatMap_nil, List.nil_append]
  have hbytes (word : List CodeSymbol) :
      (finiteWordsOver CodeSymbol Γ).encode word = word.flatMap code := encode_finiteWordsOver word
  have hlength (word : List CodeSymbol) :
      (word.flatMap (code (Γ := Γ))).length = 12 * word.length := by
    rw [List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  let crossed : List Γ := before.flatMap code ++ (number.map CodeSymbol.digit).flatMap code
  let rows := (before ++ after).count CodeSymbol.rowSeparator
  let value := Computability.decodeNat number
  let adjusted := value + if field = .next then 0 else 1
  let valid := Field.Valid field value rows
  have hknown (hsmall : adjusted < rows) :
      (if field = .largest then (Parsing.Stage.reject : Parsing.Stage Γ) else .header) =
      (if valid then .header else .reject) := by
    cases field with
    | largest =>
      have hbad : ¬valid := by dsimp [valid, Field.Valid, adjusted] at *; lia
      simp [hbad]
    | initial =>
      have hgood : valid := by dsimp [valid, Field.Valid, adjusted] at *; lia
      simp [hgood]
    | next =>
      have hgood : valid := by dsimp [valid, Field.Valid, adjusted] at *; lia
      simp [hgood]
  have hequal (hnot : ¬adjusted < rows) : adjusted - rows = 0 ↔ valid := by
    cases field <;> dsimp [adjusted, valid, Field.Valid] at * <;> lia
  unfold check
  apply Std.WP.Triple.bind (mid := fun _ cost current => ∃ bits : List Bool,
    current.config = ⟨some (.inl (if adjusted < rows then .reject else .header)),
      counterView (bits.map (fun bit => if bit then one else zero))
        (crossed ++ code CodeSymbol.headerEnd ++ after.flatMap code) [] tail⟩ ∧
    current.headPos = origin + 12 * (number.length + after.length + 1) ∧
    binaryValue bits.reverse = adjusted - rows ∧ bits.length ≤ number.length + 2 ∧
    cost.steps ≤ elapsed + 2048 * (before.length + number.length + after.length + 2) ^ 2)
  · vcgen [readAndScan_spec zero one hne field before after number tail label origin elapsed]
    all_goals simp_all [FieldInput, ReadAndScanResult, fieldTape_eq,
      Field.ending, counterView, crossed, adjusted, value, rows, List.append_assoc]
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨bits, hcfg, hpos, hvalue, hbits, htime⟩
    by_cases hsmall : adjusted < rows
    · have hanswer := hknown hsmall
      have hbudget : 2048 * (before.length + number.length + after.length + 2) ^ 2 +
          36 * (after.length + 1) + 2 * crossed.length + 2 * bits.length + 30 ≤
          4096 * (before.length + number.length + after.length + 2) ^ 2 := by
        dsimp only [crossed]
        simp only [List.length_append, hlength, List.length_map]
        nlinarith only [hbits]
      vcgen [Spec.branch_true_spec]
      refine ⟨by simp [hcfg, hsmall], ?_⟩
      vcgen [finishKnown_spec zero field (bits.map (fun bit => if bit then one else zero))
        crossed after hafter tail (some (.inl .reject))
        (origin + 12 * (number.length + after.length + 1))
        (elapsed + 2048 * (before.length + number.length + after.length + 2) ^ 2)]
      all_goals simp_all [counterView, crossed, Field.ending, valid, Field.Valid,
        List.append_assoc, code_length, List.sum_replicate, Nat.mul_comm, Function.comp_def,
        rows, value, adjusted]
      all_goals lia
    · have hvalid : binaryValue bits.reverse = 0 ↔ valid := by
        rw [hvalue]
        exact hequal hsmall
      have hbudget : 2048 * (before.length + number.length + after.length + 2) ^ 2 +
          36 * (after.length + 1) + 4 * crossed.length + 6 * bits.length + 38 ≤
          4096 * (before.length + number.length + after.length + 2) ^ 2 := by
        dsimp only [crossed]
        simp only [List.length_append, hlength, List.length_map]
        nlinarith only [hbits]
      vcgen [Spec.branch_false_spec]
      refine ⟨by simp [hcfg, hsmall], ?_⟩
      vcgen [finishEqual_spec zero one hne field bits crossed after hafter tail
        (some (.inl .header))
        (origin + 12 * (number.length + after.length + 1))
        (elapsed + 2048 * (before.length + number.length + after.length + 2) ^ 2)]
      all_goals simp_all [counterView, crossed, Field.ending, valid, Field.Valid,
        List.append_assoc, code_length, List.sum_replicate, Nat.mul_comm, Function.comp_def,
        rows, value, adjusted]
      all_goals lia

end Algolean.Algorithms.TMSATToSAT.StateFields
