/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Fields
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement

/-!
# Comparing a state number with the rows of its transition table

The description stays on the tape while the machine subtracts one from a binary counter for
each row separator. The counter stops changing if it reaches zero before the last row. Its
remaining value and the recorded result distinguish equality, a smaller number, and a larger
number. The loops are bounded by the description's length, rather than the number in the field.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.StateBounds

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet Problems.TMSAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ]

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
    SingleTapeTM.Description.MovementSymbol, Extended]

private def digits (zero one : Γ) (bits : List Bool) : List Γ :=
  bits.map (fun bit => if bit then one else zero)

private def view (zero one : Γ) (bits : List Bool) (crossed remaining : List Γ)
    (tail : StackTape Γ) : BiTape Γ :=
  BiTape.segment (StackTape.prepend crossed.reverse
    (StackTape.cons none (StackTape.mapSome (digits zero one bits).reverse))) remaining tail

private def decrease (bits : List Bool) : List Bool :=
  if binaryValue bits.reverse = 0 then bits else (decrementBits bits.reverse).reverse

private theorem decrease_length (bits : List Bool) : (decrease bits).length = bits.length := by
  unfold decrease
  split_ifs <;> simp

private theorem decrease_value (bits : List Bool) :
    binaryValue (decrease bits).reverse = binaryValue bits.reverse - 1 := by
  unfold decrease
  split_ifs with hzero
  · simp [hzero]
  · have := binaryValue_decrementBits bits.reverse (by lia)
    simpa only [List.reverse_reverse] using (show binaryValue (decrementBits bits.reverse) =
      binaryValue bits.reverse - 1 by lia)

private noncomputable def subtractOne (zero one : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  testZero (Parsing.machine (Γ := Γ)) one (.inl .reject) (.inl .header)
  ifₜ state =ₜ some (.inl .header) then
    decrementLeft (Parsing.machine (Γ := Γ)) zero one
  else
    pure ()

omit [Nontrivial Γ] in
private theorem subtractOne_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (tail : StackTape Γ) (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (digits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      subtractOne zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if binaryValue bits.reverse = 0 then .reject else .header)),
          BiTape.segment StackTape.nil (digits zero one (decrease bits)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 6 * bits.length + 6 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  by_cases hzero : binaryValue bits.reverse = 0
  · vcgen [subtractOne, testZero_spec (tm := Parsing.machine (Γ := Γ)) zero one hne
      (.inl .reject) (.inl .header) (by simp) bits tail label origin initial.steps,
      Spec.branch_false_spec]
    case vc1 => simp_all [digits]
    case vc2 =>
      refine ⟨by simp_all, ?_⟩
      dsimp only [binderNameHint]
      vcgen
      simp_all [digits, decrease]
      lia
  · have hcount := carryCount_le_length (bits.reverse.map Bool.not)
    vcgen [subtractOne, testZero_spec (tm := Parsing.machine (Γ := Γ)) zero one hne
        (.inl .reject) (.inl .header) (by simp) bits tail label origin initial.steps,
      decrementLeft_spec (tm := Parsing.machine (Γ := Γ)) zero one hne bits (by lia) tail
        (some (.inl .header)) origin (initial.steps + 2 * bits.length + 2)]
    all_goals simp_all [digits, decrease]
    all_goals lia

private noncomputable def visitSubtract (zero one restore : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  visitPreviousRegion (Parsing.machine (Γ := Γ)) restore (subtractOne zero one)

omit [Nontrivial Γ] in
private theorem subtractOne_counter_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (right : StackTape Γ) (label : Option (Parsing.State Γ)) (position : ℤ) (spent : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (digits zero one bits) right⟩ ∧
        current.headPos = position ∧ cost.steps ≤ spent ⦄
      subtractOne zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if binaryValue bits.reverse = 0 then .reject else .header)),
          BiTape.segment StackTape.nil (digits zero one (decrease bits)) right⟩ ∧
        final.headPos = position + (digits zero one bits).length -
          (digits zero one (decrease bits)).length ∧
        cost.steps ≤ spent + (6 * bits.length + 6) ⦄ := by
  vcgen [subtractOne_spec zero one hne bits right label position spent]
  all_goals simp_all [digits, decrease_length, add_assoc]

omit [Nontrivial Γ] in
private theorem visitSubtract_spec (zero one : Γ) (hne : zero ≠ one) (restore : Γ)
    (bits : List Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view zero one bits crossed (restore :: suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitSubtract zero one restore
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if binaryValue bits.reverse = 0 then .reject else .header)),
          view zero one (decrease bits) crossed (restore :: suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 8 * bits.length + 12 ⦄ := by
  vcgen [visitSubtract, visitPreviousRegion_spec restore (subtractOne zero one)
    (digits zero one bits) (digits zero one (decrease bits)) crossed suffix tail
    (6 * bits.length + 6) label
    (some (.inl (if binaryValue bits.reverse = 0 then .reject else .header))) origin elapsed
    (subtractOne_counter_spec zero one hne bits · label · ·)]
  all_goals simp_all [view, digits, decrease_length]
  all_goals lia

private noncomputable def rowByte (zero : Γ) : Γ :=
  (code CodeSymbol.rowSeparator).headD zero

private noncomputable def compareRow (zero one : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  ifₜ state =ₜ some (.inl .reject) then
    pure ()
  else
    checkPrefix (Parsing.machine (Γ := Γ)) (.inl .rowEnd) (.inl .header)
      (code CodeSymbol.rowSeparator)
    ifₜ state =ₜ some (.inl .rowEnd) then
      visitSubtract zero one (rowByte zero)
    else
      pure ()

private def rowResult (bits : List Bool) (exhausted : Bool) (symbol : CodeSymbol) :
    List Bool × Bool :=
  if exhausted ∨ symbol ≠ CodeSymbol.rowSeparator then (bits, exhausted)
  else (decrease bits, decide (binaryValue bits.reverse = 0))

private theorem compareRow_spec (zero one : Γ) (hne : zero ≠ one)
    (bits : List Bool) (exhausted : Bool) (symbol : CodeSymbol)
    (crossed suffix : List Γ) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨some (.inl (if exhausted then .reject else .header)),
          view zero one bits crossed (code symbol ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      compareRow zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if (rowResult bits exhausted symbol).2 then .reject else .header)),
          view zero one (rowResult bits exhausted symbol).1 crossed (code symbol ++ suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 8 * bits.length + 36 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  cases exhausted with
  | true =>
    vcgen [compareRow, Spec.branch_true_spec]
    refine ⟨by simp [hcfg], ?_⟩
    dsimp only [binderNameHint]
    vcgen
    simp_all [rowResult]
    lia
  | false =>
    have hp : code CodeSymbol.rowSeparator <+: code symbol ++ suffix ↔
        symbol = CodeSymbol.rowSeparator := by
      simpa only [code, eq_comm] using
        finiteWordsOver_symbol_prefix_iff CodeSymbol.rowSeparator symbol suffix
    unfold compareRow
    vcgen [Spec.branch_false_spec]
    refine ⟨by simp [hcfg], ?_⟩
    dsimp only [binderNameHint]
    by_cases hrow : symbol = CodeSymbol.rowSeparator
    · subst symbol
      obtain ⟨restore, rest, hcode⟩ : ∃ restore rest,
          code (Γ := Γ) CodeSymbol.rowSeparator = restore :: rest :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by rw [code_length]; decide))
      have hwidth := code_length (Γ := Γ) CodeSymbol.rowSeparator
      rw [hcode] at hwidth
      have hbyte : rowByte (Γ := Γ) zero = restore := by simp [rowByte, hcode]
      rw [hbyte]
      vcgen [checkPrefix_spec (tm := Parsing.machine (Γ := Γ)) (.inl .rowEnd) (.inl .header)
          (code CodeSymbol.rowSeparator) (code CodeSymbol.rowSeparator ++ suffix)
          (StackTape.prepend crossed.reverse
            (StackTape.cons none (StackTape.mapSome (digits zero one bits).reverse))) tail
          (some (.inl .header)) origin elapsed,
        visitSubtract_spec zero one hne restore bits crossed (rest ++ suffix) tail
          (some (.inl .rowEnd)) origin (elapsed + 24)]
      all_goals simp_all [rowResult, view]
      all_goals lia
    · vcgen [checkPrefix_spec (tm := Parsing.machine (Γ := Γ)) (.inl .rowEnd) (.inl .header)
        (code CodeSymbol.rowSeparator) (code symbol ++ suffix)
        (StackTape.prepend crossed.reverse
          (StackTape.cons none (StackTape.mapSome (digits zero one bits).reverse))) tail
        (some (.inl .header)) origin elapsed, Spec.branch_false_spec]
      case vc1 => simp_all [view]
      case vc2 =>
        refine ⟨by simp_all, ?_⟩
        vcgen
        simp_all [rowResult, view, code_length]
        lia

private noncomputable def rowStep (zero one : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  compareRow zero one
  moveCells (Parsing.machine (Γ := Γ)) .Right 12

private theorem rowStep_spec (zero one : Γ) (hne : zero ≠ one)
    (bits : List Bool) (exhausted : Bool) (symbol : CodeSymbol)
    (crossed suffix : List Γ) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨some (.inl (if exhausted then .reject else .header)),
          view zero one bits crossed (code symbol ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      rowStep zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if (rowResult bits exhausted symbol).2 then .reject else .header)),
          view zero one (rowResult bits exhausted symbol).1
            (crossed ++ code symbol) suffix tail⟩ ∧
        final.headPos = origin + 12 ∧
        cost.steps ≤ elapsed + 64 * (crossed.length + bits.length + 1) ⦄ := by
  unfold rowStep
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨some (.inl (if (rowResult bits exhausted symbol).2 then .reject else .header)),
      view zero one (rowResult bits exhausted symbol).1 crossed (code symbol ++ suffix) tail⟩ ∧
    current.headPos = origin ∧
    cost.steps ≤ elapsed + 2 * crossed.length + 8 * bits.length + 36)
  · vcgen [compareRow_spec zero one hne bits exhausted symbol crossed suffix tail origin elapsed]
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    have hmove (newBits : List Bool) : BiTape.moveRight^[12]
        (view zero one newBits crossed (code symbol ++ suffix) tail) =
        view zero one newBits (crossed ++ code symbol) suffix tail := by
      rw [← code_length (Γ := Γ) symbol]
      simp [view, BiTape.segment_moveRight_iterate, List.reverse_append,
        StackTape.prepend_append]
    vcgen [moveCells_spec (tm := Parsing.machine (Γ := Γ)) .Right 12
      (view zero one (rowResult bits exhausted symbol).1 crossed (code symbol ++ suffix) tail)
      (some (.inl (if (rowResult bits exhausted symbol).2 then .reject else .header)))
      origin initial.steps]
    all_goals simp_all
    all_goals lia

private def rowsResult : List Bool → Bool → List CodeSymbol → List Bool × Bool
  | bits, exhausted, [] => (bits, exhausted)
  | bits, exhausted, symbol :: rest =>
      let next := rowResult bits exhausted symbol
      rowsResult next.1 next.2 rest

private theorem rowResult_length (bits : List Bool) (exhausted : Bool) (symbol : CodeSymbol) :
    (rowResult bits exhausted symbol).1.length = bits.length := by
  unfold rowResult
  split_ifs <;> simp [decrease_length]

private theorem rowsResult_values (bits : List Bool) (exhausted : Bool)
    (hzero : exhausted = true → binaryValue bits.reverse = 0) (word : List CodeSymbol) :
    let result := rowsResult bits exhausted word
    binaryValue result.1.reverse = binaryValue bits.reverse - word.count CodeSymbol.rowSeparator ∧
      result.2 =
        (exhausted || decide (binaryValue bits.reverse < word.count CodeSymbol.rowSeparator)) ∧
      result.1.length = bits.length := by
  induction word generalizing bits exhausted with
  | nil => simp [rowsResult]
  | cons symbol rest ih =>
    cases exhausted with
    | true =>
      have hz := hzero rfl
      simpa [rowsResult, rowResult, hz] using ih bits true hzero
    | false =>
      by_cases hrow : symbol = CodeSymbol.rowSeparator
      · subst symbol
        have hnext : decide (binaryValue bits.reverse = 0) = true →
            binaryValue (decrease bits).reverse = 0 := by
          intro he
          have := of_decide_eq_true he
          simp [decrease_value, this]
        obtain ⟨hv, hf, hl⟩ := ih (decrease bits) (decide (binaryValue bits.reverse = 0)) hnext
        dsimp only [rowsResult, rowResult]
        simp only [Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
        refine ⟨?_, ?_, by simpa [decrease_length] using hl⟩
        · simpa only [decrease_value, List.count_cons_self, Nat.sub_sub, Nat.add_comm] using hv
        · rw [hf, decrease_value]
          simp only [List.count_cons_self, Bool.false_or]
          by_cases hn : binaryValue bits.reverse = 0
          · simp [hn]
          · apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, decide_eq_true_eq]
            lia
      · simpa [rowsResult, rowResult, hrow, List.count_cons, eq_comm] using ih bits false hzero

/--
This scans the remaining description and subtracts one from the preceding counter for each
row separator. It records `.reject` if a subtraction is requested when the counter is already
zero. The containing machine fixes the two digit symbols once; the counter and description
are read from the tape.
-/
noncomputable def scanRows (zero one : Γ) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  whileₜ (notₜ tape =ₜ none) do
    rowStep zero one

private theorem scanRows_loop_spec (zero one : Γ) (hne : zero ≠ one)
    (bits : List Bool) (exhausted : Bool) (word : List CodeSymbol)
    (crossed : List Γ) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨some (.inl (if exhausted then .reject else .header)),
          view zero one bits crossed (word.flatMap code) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      scanRows zero one
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl (if (rowsResult bits exhausted word).2 then .reject else .header)),
          view zero one (rowsResult bits exhausted word).1
            (crossed ++ word.flatMap code) [] tail⟩ ∧
        final.headPos = origin + 12 * word.length ∧
        cost.steps ≤ elapsed + 64 * word.length *
          (crossed.length + bits.length + 13 * word.length + 1) ⦄ := by
  induction word generalizing bits exhausted crossed origin elapsed with
  | nil =>
    unfold scanRows
    vcgen [Spec.while_false_spec]
    simp_all [view, rowsResult]
    rfl
  | cons symbol rest ih =>
    have hcode : code (Γ := Γ) symbol ≠ [] :=
      List.ne_nil_of_length_pos (by rw [code_length]; decide)
    have hrest := ih (rowResult bits exhausted symbol).1 (rowResult bits exhausted symbol).2
      (crossed ++ code symbol) (origin + 12)
      (elapsed + 64 * (crossed.length + bits.length + 1))
    unfold scanRows
    vcgen [Spec.while_step_spec (loop := scanRows zero one) (hloop := rfl),
      rowStep_spec zero one hne bits exhausted symbol crossed (rest.flatMap code) tail
        origin elapsed, hrest]
    all_goals simp_all [view, rowsResult, List.append_assoc, rowResult_length, code_length]
    all_goals ring_nf at *
    all_goals lia

/--
The scan preserves the description and subtracts its row count from the counter, stopping at
zero. The final state records whether there were more rows than the original counter value.
The counter keeps its original length, and the bound counts head moves from the initial cost.
-/
@[spec] theorem scanRows_spec (zero one : Γ) (hne : zero ≠ one) (bits : List Bool)
    (word : List CodeSymbol) (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some (.inl .header), BiTape.segment
        (StackTape.cons none (StackTape.mapSome
          (bits.map (fun bit => if bit then one else zero)).reverse))
        ((finiteWordsOver CodeSymbol Γ).encode word) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      scanRows zero one
    ⦃ fun _ cost final => ∃ remaining : List Bool,
        final.config =
          ⟨some (.inl (if binaryValue bits.reverse < word.count CodeSymbol.rowSeparator
            then .reject else .header)),
            BiTape.segment (StackTape.prepend ((finiteWordsOver CodeSymbol Γ).encode word).reverse
              (StackTape.cons none (StackTape.mapSome
                (remaining.map (fun bit => if bit then one else zero)).reverse))) [] tail⟩ ∧
        final.headPos = origin + ((finiteWordsOver CodeSymbol Γ).encode word).length ∧
        binaryValue remaining.reverse =
          binaryValue bits.reverse - word.count CodeSymbol.rowSeparator ∧
        remaining.length = bits.length ∧
        cost.steps ≤ elapsed + 64 * word.length * (bits.length + 13 * word.length + 1) ⦄ := by
  have hinput : (finiteWordsOver CodeSymbol Γ).encode word = word.flatMap code :=
    encode_finiteWordsOver word
  have hlength : ((finiteWordsOver CodeSymbol Γ).encode word).length = 12 * word.length := by
    rw [hinput, List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  obtain ⟨hv, hflag, hl⟩ := rowsResult_values bits false (by simp) word
  vcgen [scanRows_loop_spec zero one hne bits false word [] tail origin elapsed]
  case vc1 => simp_all [view, digits]
  case vc2 =>
    refine ⟨(rowsResult bits false word).1, ?_⟩
    simp_all [view, digits]

end Algolean.Algorithms.TMSATToSAT.StateBounds
