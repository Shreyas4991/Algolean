/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockCounting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.ReverseCopying
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.VariableNames
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Variables

/-!
# Writing the symbol choices for every recorded tape cell

* `writeChoices` reads two unary words. The first gives the number of recorded times, and
  the second gives the number of tape positions. It writes exactly-one clauses for each pair.
* `writeTapeChoices` fixes the choices to all cell values, including blank and the preserved's
  separating symbol. The clauses use the existing binary computation-variable names.
* Both words, the original input, and earlier output are preserved. Each clause is ended,
  while the formula is left open so further clauses can follow.

These are machine templates. The alphabet choices and symbol representations are fixed once.
Every time and position is read from the tape by the same program on every preserved length.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Computation.TapeChoices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Computability Problems Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def symbolBits (symbol : Option (TapeSymbol Γ)) : List Bool :=
  encodingNatBool.encode (Encodable.encode symbol)

/-- These are the two unary words, preserved words, and earlier output on the same tape. -/
@[expose] def layout (tick : Γ) (times positions : Nat) (preserved : List (List Γ))
    (output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (List.replicate times tick)
    (StackTape.separateWords (List.replicate positions tick :: preserved)
      (StackTape.mapSome output))

/-- This is the encoded clause prefix for the given times, positions, and fixed cell choices. -/
@[expose] def word (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (times positions : Nat) : List Γ :=
  (List.range times).flatMap fun time =>
    (List.range positions).flatMap fun position =>
      (formulaPrefix ((CNF.exactlyOne symbols).rename fun symbol =>
        Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
          (encodingNatBool.encode (Encodable.encode symbol)))).flatMap code

private def writeTime (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (preservedCount : Nat) : Prog (TMQuery tm) Unit :=
  appendEarlierAtMark zero one tick (fun bit => code (.inl bit)) true 0 1 (preservedCount + 4)

private def writePosition (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (preservedCount : Nat) : Prog (TMQuery tm) Unit :=
  appendCurrentAtMark zero one tick (fun bit => code (.inl bit)) true 2 (preservedCount + 4)

private def marked (tick : Γ) (time timeRest position positionRest : Nat)
    (preserved : List (List Γ))
    (output : List Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend (List.replicate position tick).reverse
      (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])) []
    (StackTape.separateWords (List.replicate positionRest tick :: preserved)
      (StackTape.mapSome output))

private def positionMoves (tick : Γ) (width time timeRest position positionRest : Nat)
    (preserved : List (List Γ)) (output : List Γ) : Nat :=
  2 * position + 2 + unaryNumberMoves true width 1 position
    [List.replicate timeRest tick, List.replicate time tick]
    (List.replicate positionRest tick :: preserved) output.length

omit [Encodable Γ] in
private theorem writePosition_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (preserved : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest preserved output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writePosition (tm := tm) zero one tick code preserved.length
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest preserved
          (output ++ (unaryNumberBits true position).flatMap (fun bit => code (.inl bit)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positionMoves tick width time timeRest position positionRest preserved output ⦄ := by
  simpa [writePosition, marked, markedUnaryTape, positionMoves,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    appendCurrentAtMark_spec (tm := tm) zero one hne tick (fun bit => code (.inl bit))
      width (fun bit => hwidth (.inl bit)) true position
      [List.replicate timeRest tick, List.replicate time tick]
      (List.replicate positionRest tick :: preserved) output label origin elapsed

private def timeMoves (tick : Γ) (width time timeRest position positionRest : Nat)
    (preserved : List (List Γ)) (output : List Γ) : Nat :=
  unaryNumberMoves true width 1 time []
    ([List.replicate timeRest tick, List.replicate position tick,
      List.replicate positionRest tick] ++ preserved) output.length +
    2 * time + 2 * timeRest + 2 * position + 10

omit [Encodable Γ] in
private theorem writeTime_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (preserved : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest preserved output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeTime (tm := tm) zero one tick code preserved.length
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest preserved
          (output ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          timeMoves tick width time timeRest position positionRest preserved output ⦄ := by
  have h := appendEarlierAtMark_spec (tm := tm) zero one hne tick
    (fun bit => code (.inl bit)) width (fun bit => hwidth (.inl bit)) true time []
    [List.replicate timeRest tick] (List.replicate position tick)
    (List.replicate positionRest tick :: preserved) output label origin elapsed
  simp only [List.length_nil, List.length_cons, Nat.zero_add, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] at h
  vcgen [writeTime, h]
  all_goals
    simp_all [marked, markedUnaryTape, timeMoves, earlierUnaryMoves]
    all_goals lia

private def numberBudget (width size : Nat) : Nat :=
  256 * (width + 1) * 2 ^ 2 * (size + 7) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem timeMoves_le (tick : Γ) (width time timeRest position positionRest size : Nat)
    (preserved : List (List Γ)) (output : List Γ)
    (hsize : time + timeRest + position + positionRest +
      regionSpan preserved + output.length ≤ size) :
    timeMoves tick width time timeRest position positionRest preserved output ≤
      numberBudget width size + 2 * size + 10 := by
  simp only [regionSpan] at hsize
  have hu := unaryNumberMoves_le true width 1 time []
    ([List.replicate timeRest tick, List.replicate position tick,
      List.replicate positionRest tick] ++ preserved) output.length
  have hb : unaryNumberMoves true width 1 time []
      ([List.replicate timeRest tick, List.replicate position tick,
        List.replicate positionRest tick] ++ preserved) output.length ≤
        numberBudget width size := by
    apply hu.trans
    dsimp [numberBudget]
    simp only [regionSpan_cons, List.length_replicate]
    simp only [regionSpan] at *
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    lia
  simp only [List.cons_append, List.nil_append] at hb
  dsimp [timeMoves]
  lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem positionMoves_le (tick : Γ) (width time timeRest position positionRest size : Nat)
    (preserved : List (List Γ)) (output : List Γ)
    (hsize : time + timeRest + position + positionRest +
      regionSpan preserved + output.length ≤ size) :
    positionMoves tick width time timeRest position positionRest preserved output ≤
      numberBudget width size + 2 * size + 2 := by
  simp only [regionSpan] at hsize
  have hu := unaryNumberMoves_le true width 1 position
    [List.replicate timeRest tick, List.replicate time tick]
    (List.replicate positionRest tick :: preserved) output.length
  have hb : unaryNumberMoves true width 1 position
      [List.replicate timeRest tick, List.replicate time tick]
      (List.replicate positionRest tick :: preserved) output.length ≤ numberBudget width size := by
    apply hu.trans
    dsimp [numberBudget]
    simp only [regionSpan_cons, regionSpan_nil, List.length_replicate]
    simp only [regionSpan] at *
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    lia
  dsimp [positionMoves]
  lia

private def sign : Literal (Option (TapeSymbol Γ)) → CodeSymbol
  | .pos _ => .inr 0
  | .neg _ => .inr 1

private def itemWord (code : CodeSymbol → List Γ) (time position : Nat) :
    Option (Literal (Option (TapeSymbol Γ))) → List Γ
  | none => code (.inr 3) ++ code (.inr 4)
  | some literal => code (sign literal) ++
      (Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
        (symbolBits literal.name)).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)

private def writeLiteral (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (preservedCount : Nat) (literal : Literal (Option (TapeSymbol Γ))) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendAcross tm (code (sign literal) ++ code (.inl true) ++ code (.inl false))
    (preservedCount + 1)
  writeTime zero one tick code preservedCount
  writePosition zero one tick code preservedCount
  appendAcross tm ((symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++
    code (.inr 2)) (preservedCount + 1)

private def literalMoves (tick : Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (time timeRest position positionRest : Nat) (preserved : List (List Γ)) (output : List Γ)
    (literal : Literal (Option (TapeSymbol Γ))) : Nat :=
  let front := code (sign literal) ++ code (.inl true) ++ code (.inl false)
  let first := output ++ front
  let second := first ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit))
  let third := second ++ (unaryNumberBits true position).flatMap (fun bit => code (.inl bit))
  let back := (symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)
  2 * (positionRest + regionSpan preserved + 1 + output.length + front.length) + 8 +
    timeMoves tick width time timeRest position positionRest preserved first +
    positionMoves tick width time timeRest position positionRest preserved second +
    (2 * (positionRest + regionSpan preserved + 1 + third.length + back.length) + 8)

private theorem writeLiteral_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (preserved : List (List Γ)) (output : List Γ)
    (literal : Literal (Option (TapeSymbol Γ)))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest preserved output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeLiteral (tm := tm) zero one tick code preserved.length literal
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest preserved
          (output ++ itemWord code time position (some literal))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          literalMoves tick code width time timeRest position positionRest
            preserved output literal ⦄ := by
  let digits := fun bit => code (.inl bit)
  let front := code (sign literal) ++ code (.inl true) ++ code (.inl false)
  let first := output ++ front
  let second := first ++ (unaryNumberBits true time).flatMap digits
  let third := second ++ (unaryNumberBits true position).flatMap digits
  let back := (symbolBits literal.name).flatMap digits ++ code (.inr 2)
  let parts := (List.replicate positionRest tick :: preserved)
  let left := StackTape.prepend (List.replicate position tick).reverse
    (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])
  let start := 2 * (regionSpan parts + output.length + front.length) + 8
  let middle := timeMoves tick width time timeRest position positionRest preserved first
  let later := positionMoves tick width time timeRest position positionRest preserved second
  have hf := appendAcross_le_spec (tm := tm) front parts output left label origin elapsed
  have hb := appendAcross_le_spec (tm := tm) back parts third left label origin
    (elapsed + start + middle + later)
  norm_num only [parts, List.length_cons, List.length_nil] at hf hb
  dsimp only [front] at hf
  dsimp only [back, digits] at hb
  vcgen [writeLiteral, hf,
    writeTime_spec zero one hne tick code width hwidth time timeRest position positionRest
      preserved first label origin (elapsed + start),
    writePosition_spec zero one hne tick code width hwidth time timeRest position positionRest
      preserved second label origin (elapsed + start + middle),
    hb]
  all_goals
    simp_all [marked, literalMoves, itemWord, Naming.bits, unaryNumberBits,
      BooleanTapeEncoding.pair, digits, front, first, second, third, parts, left,
      start, middle, later, regionSpan, List.append_assoc, List.flatMap_append]
    all_goals lia

private def itemBudget (width size : Nat) : Nat := 4096 * (width + 1) * (size + 8) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem literalMoves_le (tick : Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (time timeRest position positionRest : Nat) (preserved : List (List Γ)) (output : List Γ)
    (literal : Literal (Option (TapeSymbol Γ))) (size : Nat)
    (hsize : time + timeRest + position + positionRest + regionSpan preserved +
      (output ++ itemWord code time position (some literal)).length ≤ size) :
    literalMoves tick code width time timeRest position positionRest preserved output literal ≤
      itemBudget width size := by
  let digits := fun bit => code (.inl bit)
  let front := code (sign literal) ++ code (.inl true) ++ code (.inl false)
  let first := output ++ front
  let second := first ++ (unaryNumberBits true time).flatMap digits
  let third := second ++ (unaryNumberBits true position).flatMap digits
  let back := (symbolBits literal.name).flatMap digits ++ code (.inr 2)
  have heq : itemWord code time position (some literal) = front ++
      (unaryNumberBits true time).flatMap digits ++
      (unaryNumberBits true position).flatMap digits ++ back := by
    simp [itemWord, front, back, digits, Naming.bits, unaryNumberBits,
      BooleanTapeEncoding.pair, List.flatMap_append, List.append_assoc]
  have hdata : time + timeRest + position + positionRest + regionSpan preserved +
      third.length + back.length ≤ size := by
    simpa only [heq, third, second, first, List.length_append, Nat.add_assoc] using hsize
  have ht := timeMoves_le tick width time timeRest position positionRest size preserved first (by
    simp only [third, second, List.length_append] at hdata
    lia)
  have hp := positionMoves_le tick width time timeRest position positionRest size
    preserved second (by
    simp only [third, List.length_append] at hdata
    lia)
  have hf : positionRest + regionSpan preserved + 1 + output.length + front.length ≤ size + 2 := by
    simp only [third, second, first, List.length_append] at hdata
    lia
  have hb : positionRest + regionSpan preserved + 1 + third.length + back.length ≤
      size + 2 := by lia
  have he : literalMoves tick code width time timeRest position positionRest
      preserved output literal =
      2 * (positionRest + regionSpan preserved + 1 + output.length + front.length) + 8 +
      timeMoves tick width time timeRest position positionRest preserved first +
      positionMoves tick width time timeRest position positionRest preserved second +
      (2 * (positionRest + regionSpan preserved + 1 + third.length + back.length) + 8) := rfl
  rw [he]
  dsimp [itemBudget, numberBudget] at *
  ring_nf at *
  lia

private def writeItems (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (preservedCount : Nat) :
    List (Option (Literal (Option (TapeSymbol Γ)))) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | none :: rest => do [TMQuery tm]
    appendAcross tm (code (.inr 3) ++ code (.inr 4)) (preservedCount + 1)
    writeItems zero one tick code preservedCount rest
  | some literal :: rest => do [TMQuery tm]
    writeLiteral zero one tick code preservedCount literal
    writeItems zero one tick code preservedCount rest

private theorem writeItems_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (items : List (Option (Literal (Option (TapeSymbol Γ)))))
    (time timeRest position positionRest : Nat) (preserved : List (List Γ))
    (output : List Γ) (size : Nat)
    (hsize : time + timeRest + position + positionRest + regionSpan preserved +
      (output ++ items.flatMap (itemWord code time position)).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest preserved output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeItems (tm := tm) zero one tick code preserved.length items
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest preserved
          (output ++ items.flatMap (itemWord code time position))⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + items.length * itemBudget width size ⦄ := by
  induction items generalizing output elapsed with
  | nil =>
    vcgen [writeItems]
    simp_all
  | cons item rest ih =>
    have hrest := ih (output ++ itemWord code time position item)
      (by simpa [List.append_assoc] using hsize) (elapsed + itemBudget width size)
    have hfirst : time + timeRest + position + positionRest + regionSpan preserved +
        (output ++ itemWord code time position item).length ≤ size := by
      simp only [List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    cases item with
    | none =>
      let parts := (List.replicate positionRest tick :: preserved)
      let left := StackTape.prepend (List.replicate position tick).reverse
        (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])
      have htime : 2 * (regionSpan parts + output.length +
          (code (.inr 3) ++ code (.inr 4)).length) + 8 ≤ itemBudget width size := by
        simp only [itemWord, List.length_append, regionSpan] at hfirst
        dsimp [parts, regionSpan, itemBudget]
        simp only [List.map_cons, List.sum_cons, List.length_replicate, List.length_append]
        ring_nf at *
        lia
      have ha := appendAcross_le_spec (tm := tm) (code (.inr 3) ++ code (.inr 4))
        parts output left label origin elapsed
      norm_num only [parts, List.length_cons, List.length_nil, List.length_append] at ha
      simp only [writeItems]
      vcgen [ha, hrest]
      all_goals
        simp_all [marked, parts, left, itemWord, List.append_assoc]
        all_goals ring_nf at *
        all_goals lia
    | some literal =>
      have htime := literalMoves_le tick code width time timeRest position positionRest
        preserved output literal size hfirst
      simp only [writeItems]
      vcgen [writeLiteral_spec zero one hne tick code width hwidth time timeRest position
        positionRest preserved output literal label origin elapsed, hrest]
      all_goals
        simp_all [List.append_assoc]
        all_goals ring_nf at *
        all_goals lia

private def items (formula : CNF (Option (TapeSymbol Γ))) :
    List (Option (Literal (Option (TapeSymbol Γ)))) :=
  formula.flatMap fun clause => clause.map some ++ [none]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem items_word (code : CodeSymbol → List Γ) (time position : Nat)
    (formula : CNF (Option (TapeSymbol Γ))) :
    (items formula).flatMap (itemWord code time position) =
      (formulaPrefix (formula.rename fun symbol =>
        Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
          (symbolBits symbol))).flatMap code := by
  let name : Option (TapeSymbol Γ) → SAT.Variable := fun symbol =>
    Naming.bits .tape (encodingNatBool.encode time)
    (encodingNatBool.encode position) (symbolBits symbol)
  have hc (clause : Clause (Option (TapeSymbol Γ))) :
      (clause.map some ++ [none]).flatMap (itemWord code time position) =
        (certificateEncoding.encode (clause.rename name) ++
          [(.inr 4 : CodeSymbol)]).flatMap code := by
    induction clause with
    | nil => simp [itemWord, Clause.rename, certificateEncoding_encode_nil]
    | cons literal rest ih =>
      cases literal <;>
        simp [itemWord, sign, Clause.rename, Literal.rename, certificateEncoding_encode_pos,
          certificateEncoding_encode_neg, name,
          List.flatMap_append, List.flatMap_map, List.append_assoc, ih]
  induction formula with
  | nil => simp [items, formulaPrefix, CNF.rename]
  | cons clause rest ih =>
    simpa [items, formulaPrefix, CNF.rename, List.flatMap_append] using
      congrArg₂ (· ++ ·) (hc clause) ih

private def rowWord (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (time positions : Nat) : List Γ :=
  (List.range positions).flatMap fun position =>
    (items (CNF.exactlyOne symbols)).flatMap (itemWord code time position)

omit [Inhabited Γ] [Fintype Γ] in
private theorem rowWord_succ (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (time positions : Nat) :
    rowWord code symbols time (positions + 1) = rowWord code symbols time positions ++
      (items (CNF.exactlyOne symbols)).flatMap (itemWord code time positions) := by
  simp [rowWord, List.range_succ]

omit [Inhabited Γ] [Fintype Γ] in
private theorem rowWord_length_mono (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (time : Nat) {first second : Nat}
    (h : first ≤ second) :
    (rowWord code symbols time first).length ≤ (rowWord code symbols time second).length :=
  ((List.range_sublist.mpr h).flatMap _).length_le

omit [Inhabited Γ] [Fintype Γ] in
private theorem word_eq_rows (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (times positions : Nat) :
    word code symbols times positions =
      (List.range times).flatMap fun time => rowWord code symbols time positions := by
  simp [word, rowWord, items_word, symbolBits]

omit [Inhabited Γ] [Fintype Γ] in
private theorem word_succ (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (times positions : Nat) :
    word code symbols (times + 1) positions = word code symbols times positions ++
      rowWord code symbols times positions := by
  simp [word_eq_rows, List.range_succ]

omit [Inhabited Γ] [Fintype Γ] in
private theorem word_length_mono (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (positions : Nat) {first second : Nat}
    (h : first ≤ second) :
    (word code symbols first positions).length ≤ (word code symbols second positions).length := by
  simp only [word_eq_rows]
  exact ((List.range_sublist.mpr h).flatMap _).length_le

private theorem positions_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (time timeRest positions : Nat)
    (preserved : List (List Γ)) (output : List Γ) (size : Nat)
    (hsize : time + timeRest + positions + regionSpan preserved +
      (output ++ rowWord code symbols time positions).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let left := counterLeft [] [List.replicate timeRest tick, List.replicate time tick]
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment left (List.replicate positions tick)
          (StackTape.separateWords preserved (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forBlocks tm tick []
        (writeItems zero one tick code preserved.length (items (CNF.exactlyOne symbols)))
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment left (List.replicate positions tick)
          (StackTape.separateWords preserved
            (StackTape.mapSome (output ++ rowWord code symbols time positions)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positions * ((items (CNF.exactlyOne symbols)).length *
            itemBudget width size + 2) + 2 ⦄ := by
  dsimp only
  let left := counterLeft [] [List.replicate timeRest tick, List.replicate time tick]
  let tails := fun index => StackTape.separateWords preserved
    (StackTape.mapSome (output ++ rowWord code symbols time index))
  let body := writeItems (tm := tm) zero one tick code preserved.length
    (items (CNF.exactlyOne symbols))
  let bound := (items (CNF.exactlyOne symbols)).length * itemBudget width size
  have ha : BlockAction tick [] positions (fun _ => left.tail) tails label body bound := by
    intro index rest hcount position steps
    have hp := rowWord_length_mono code symbols time (show index + 1 ≤ positions by lia)
    have hi : time + timeRest + index + rest + regionSpan preserved +
        (output ++ rowWord code symbols time index ++
          (items (CNF.exactlyOne symbols)).flatMap (itemWord code time index)).length ≤ size := by
      rw [List.append_assoc, ← rowWord_succ]
      simp only [List.length_append] at hp hsize ⊢
      lia
    vcgen [writeItems_spec zero one hne tick code width hwidth (items (CNF.exactlyOne symbols))
      time timeRest index rest preserved (output ++ rowWord code symbols time index) size
      (by simpa only [List.append_assoc] using hi) label position steps]
    all_goals
      simp_all [bound, left, tails, marked, counterLeft, unaryWord,
        rowWord_succ, List.append_assoc]
  have hrun := forBlocks_spec tick [] positions (fun _ => left.tail) tails label body bound ha
    origin elapsed
  dsimp only [body] at hrun
  vcgen [hrun]
  all_goals simp_all [left, tails, body, bound, counterLeft, unaryWord, rowWord]

private def visitPositions (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  seekRightBlank tm
  moveₜ .Right
  forBlocks tm tick [] action
  previousRegion tm
  moveₜ .Left

private def outerMarked (tick : Γ) (time timeRest positions : Nat)
    (preserved : List (List Γ))
    (output : List Γ) : BiTape Γ :=
  BiTape.segment (StackTape.mapSome (List.replicate time tick).reverse) []
    (StackTape.separateWords
      ([List.replicate timeRest tick, List.replicate positions tick] ++ preserved)
      (StackTape.mapSome output))

private theorem visitPositions_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (time timeRest positions : Nat)
    (preserved : List (List Γ)) (output : List Γ) (size : Nat)
    (hsize : time + timeRest + positions + regionSpan preserved +
      (output ++ rowWord code symbols time positions).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, outerMarked tick time timeRest positions preserved output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitPositions tick (writeItems (tm := tm) zero one tick code preserved.length
        (items (CNF.exactlyOne symbols)))
    ⦃ fun _ cost final => final.config = ⟨label,
        outerMarked tick time timeRest positions preserved
          (output ++ rowWord code symbols time positions)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 2 * timeRest + 8 +
          positions * ((items (CNF.exactlyOne symbols)).length * itemBudget width size + 2) ⦄ := by
  let before := List.replicate time tick
  let suffix := List.replicate timeRest tick
  let source := List.replicate positions tick
  let written := output ++ rowWord code symbols time positions
  let inner := positions * ((items (CNF.exactlyOne symbols)).length * itemBudget width size + 2) + 2
  have hp := positions_spec zero one hne tick code width hwidth symbols time timeRest positions
    preserved output size hsize label (origin + (timeRest + 2 : Nat)) (elapsed + timeRest + 2)
  vcgen [visitPositions,
    seekRightBlank_le_spec (tm := tm) (StackTape.cons none (StackTape.mapSome before.reverse))
      (StackTape.separateWords (source :: preserved) (StackTape.mapSome output)) suffix
      label (origin + 1) (elapsed + 1),
    hp,
    previousRegion_le_spec (tm := tm) (StackTape.mapSome before.reverse) suffix source
      (StackTape.separateWords preserved (StackTape.mapSome written)) label
      (origin + (timeRest + 2 : Nat)) (elapsed + timeRest + 2 + inner)]
  all_goals
    cases timeRest
    all_goals cases positions
    all_goals
      simp_all [outerMarked, before, suffix, source, written, inner, counterLeft,
        TMState.move, TMState.moveCost, BiTape.segment, BiTape.moveRight, BiTape.moveLeft,
        List.replicate_succ]
      all_goals lia

/--
This machine template writes the fixed symbol-choice clauses at every time and position
specified by its two unary words. It reads both indices from the tape and restores the
unary words, their separating blanks, and the starting head position.
-/
def writeChoices (tm : SingleTapeTM Γ) (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (symbols : List (Option (TapeSymbol Γ))) (preservedCount : Nat := 1) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  forBlocks tm tick []
    (visitPositions tick (writeItems zero one tick code preservedCount
      (items (CNF.exactlyOne symbols))))

/-- This states the source words, output, control state, and starting head position. -/
@[expose] def AtInput (tick : Γ) (times positions : Nat)
    (preserved : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, layout tick times positions preserved output⟩ ∧ current.headPos = origin

/-- This polynomial bounds execution in terms of source length and the total output length. -/
noncomputable def timeBound (width : Nat) (symbols : List (Option (TapeSymbol Γ))) :
    Polynomial Nat :=
  Polynomial.C ((items (CNF.exactlyOne symbols)).length * 4096 * (width + 1) + 16) *
    (Polynomial.X + 8) ^ 4

omit [Inhabited Γ] [Fintype Γ] [Encodable Γ] in
private theorem loopTime_le (width : Nat) (symbols : List (Option (TapeSymbol Γ)))
    (times positions size : Nat) (ht : times ≤ size) (hp : positions ≤ size) :
    times * (2 * times + 10 +
      positions * ((items (CNF.exactlyOne symbols)).length * itemBudget width size + 2)) + 2 ≤
        (timeBound width symbols).eval size := by
  calc
    _ ≤ size * (2 * size + 10 +
        size * ((items (CNF.exactlyOne symbols)).length * itemBudget width size + 2)) + 2 := by
      gcongr
    _ ≤ _ := by
      simp only [timeBound, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, itemBudget]
      ring_nf
      lia

/--
The program appends exactly the SAT clauses for the two unary bounds. It preserves both
bounds, the preserved words and earlier output, and the starting head position. A polynomial bounds
execution for every pair of bounds and every preserved and output word.
-/
@[spec] theorem writeChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TapeSymbol Γ))) (times positions : Nat)
    (preserved : List (List Γ)) (output : List Γ) (size : Nat)
    (hsize : times + positions + regionSpan preserved +
      (output ++ word code symbols times positions).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick times positions preserved output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeChoices tm zero one tick code symbols preserved.length
    ⦃ fun _ cost final => AtInput tick times positions preserved
        (output ++ word code symbols times positions) label origin final ∧
        cost.steps ≤ elapsed + (timeBound width symbols).eval size ⦄ := by
  let body := visitPositions tick
    (writeItems (tm := tm) zero one tick code preserved.length (items (CNF.exactlyOne symbols)))
  let inner := (items (CNF.exactlyOne symbols)).length * itemBudget width size
  let bound := 2 * times + 8 + positions * (inner + 2)
  let tails := fun index => StackTape.separateWords (List.replicate positions tick :: preserved)
    (StackTape.mapSome (output ++ word code symbols index positions))
  have ha : BlockAction tick [] times (fun _ => StackTape.nil) tails label body bound := by
    intro index rest hcount position steps
    have hp := word_length_mono code symbols positions (show index + 1 ≤ times by lia)
    have hi : index + rest + positions + regionSpan preserved +
        (output ++ word code symbols index positions ++
          rowWord code symbols index positions).length ≤
          size := by
      rw [List.append_assoc, ← word_succ]
      simp only [List.length_append] at hp hsize ⊢
      lia
    vcgen [visitPositions_spec zero one hne tick code width hwidth symbols index rest positions
      preserved (output ++ word code symbols index positions) size
      (by simpa only [List.append_assoc] using hi) label position steps]
    all_goals
      simp_all [bound, inner, tails, outerMarked, unaryWord,
        word_succ, List.append_assoc]
      all_goals lia
  have hz : word code symbols 0 positions = [] := rfl
  have ht := loopTime_le width symbols times positions size (by lia) (by lia)
  have hrun := forBlocks_spec tick [] times (fun _ => StackTape.nil) tails label body
    bound ha origin elapsed
  dsimp only [body] at hrun
  vcgen [writeChoices, hrun]
  all_goals
    simp_all [AtInput, layout, tails, body, bound, inner, unaryWord]
    all_goals lia

/-- This fixes all possible cell values once and writes their choices for every recorded cell. -/
noncomputable def writeTapeChoices (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (preservedCount : Nat := 1) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeChoices tm zero one tick code (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
    preservedCount

omit [Inhabited Γ] in
/-- The writer's output is precisely the existing tape-symbol clauses, with their existing names. -/
theorem word_eq_tapeClauses (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ) :
    word code (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
        (problem.time + 1) (NPToSAT.Computation.width problem) =
      (formulaPrefix ((tapeClauses problem).rename Variable.name)).flatMap code := by
  let symbols := (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
  have hindices (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
    ext i; simp
  have hmap (time : Fin (problem.time + 1)) (position : Fin (NPToSAT.Computation.width problem)) :
      (CNF.exactlyOne (symbols.map (Variable.tape time position))).rename Variable.name =
        (CNF.exactlyOne symbols).rename (fun symbol =>
          Naming.bits .tape (encodingNatBool.encode time.val)
              (encodingNatBool.encode position.val)
            (symbolBits symbol)) := by
    rw [← CNF.rename_exactlyOne (Variable.tape time position)
      (by intro first second h; cases h; rfl)]
    simp only [CNF.rename, Clause.rename, List.map_map, Function.comp_def]
    congr 1
    funext clause
    congr 1
    funext literal
    cases literal <;> simp [Literal.rename, Naming.bits, symbolBits, Variable.name]
  have hformula : (tapeClauses problem).rename Variable.name =
      (List.finRange (problem.time + 1)).flatMap fun time =>
        (List.finRange (NPToSAT.Computation.width problem)).flatMap fun position =>
          (CNF.exactlyOne symbols).rename (fun symbol =>
            Naming.bits .tape (encodingNatBool.encode time.val)
              (encodingNatBool.encode position.val)
              (symbolBits symbol)) := by
    simp only [tapeClauses, CNF.rename, List.map_flatMap]
    congr 1
    funext time
    congr 1
    funext position
    exact hmap time position
  rw [hformula]
  simp only [word, hindices, List.flatMap_map, formulaPrefix, List.flatMap_assoc, symbols,
    CNF.rename, symbolBits]

/--
The program writes the tape-symbol clauses for the specified bounded computation.
The bounds occur only in the specification. The running program reads them from the tape.
-/
@[spec] theorem writeTapeChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (problem : BoundedVerification Γ) (preserved : List (List Γ)) (output : List Γ) (size : Nat)
    (hsize : problem.time + 1 + NPToSAT.Computation.width problem + regionSpan preserved +
      (output ++ (formulaPrefix ((tapeClauses problem).rename Variable.name)).flatMap code).length ≤
        size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick (problem.time + 1) (NPToSAT.Computation.width problem)
        preserved output label origin current ∧ cost.steps ≤ elapsed ⦄
      writeTapeChoices tm zero one tick code preserved.length
    ⦃ fun _ cost final => AtInput tick (problem.time + 1)
    (NPToSAT.Computation.width problem) preserved
        (output ++ (formulaPrefix ((tapeClauses problem).rename Variable.name)).flatMap code)
        label origin final ∧ cost.steps ≤ elapsed +
          (timeBound width
            (Finset.univ : Finset (Option (TapeSymbol Γ))).toList).eval size ⦄ := by
  simpa only [writeTapeChoices, word_eq_tapeClauses] using
    writeChoices_spec (tm := tm) zero one hne tick code width hwidth
      (Finset.univ : Finset (Option (TapeSymbol Γ))).toList
      (problem.time + 1) (NPToSAT.Computation.width problem) preserved output size
      (by simpa only [word_eq_tapeClauses] using hsize) label origin elapsed

end Algolean.Algorithms.NPToSAT.Computation.TapeChoices
