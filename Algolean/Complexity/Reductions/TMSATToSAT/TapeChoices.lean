/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockCounting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.ReverseCopying
public import Algolean.Complexity.Reductions.TMSATToSAT.Naming
public import Algolean.Complexity.Reductions.TMSATToSAT.Variables

/-!
# Writing the symbol choices for every recorded tape cell

* `writeChoices` reads two unary words. The first gives the number of recorded times, and
  the second gives the number of tape positions. It writes exactly-one clauses for each pair.
* `writeTapeChoices` fixes the choices to all cell values, including blank and the input's
  separating symbol. The clauses use the existing binary computation-variable names.
* Both words, the original input, and earlier output are preserved. Each clause is ended,
  while the formula is left open so further clauses can follow.

These are machine templates. The alphabet choices and symbol representations are fixed once.
Every time and position is read from the tape by the same program on every input length.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.TapeChoices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Computability Problems Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def symbolBits (symbol : Option (TMSAT.TapeSymbol Γ)) : List Bool :=
  encodingNatBool.encode (Encodable.encode symbol)

/-- These are the two unary words, preserved input, and earlier output on the same tape. -/
@[expose] def layout (tick : Γ) (times positions : Nat) (input output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (List.replicate times tick)
    (StackTape.separateWords [List.replicate positions tick, input] (StackTape.mapSome output))

/-- This is the encoded clause prefix for the given times, positions, and fixed cell choices. -/
@[expose] def word (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (times positions : Nat) : List Γ :=
  (List.range times).flatMap fun time =>
    (List.range positions).flatMap fun position =>
      (formulaPrefix ((CNF.exactlyOne symbols).rename fun symbol =>
        Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
          (encodingNatBool.encode (Encodable.encode symbol)))).flatMap code

private def writeTime (zero one tick : Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  onCounter tm (appendUnaryNumber tm zero one tick [] (fun bit => code (.inl bit)) true 0 5) 1
  seekRightBlank tm

private def writePosition (zero one tick : Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  appendUnaryNumber tm zero one tick [] (fun bit => code (.inl bit)) true 2 5
  seekRightBlank tm

private def marked (tick : Γ) (time timeRest position positionRest : Nat)
    (input output : List Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend (List.replicate position tick).reverse
      (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])) []
    (StackTape.separateWords [List.replicate positionRest tick, input] (StackTape.mapSome output))

private def positionMoves (tick : Γ) (width time timeRest position positionRest : Nat)
    (input output : List Γ) : Nat :=
  2 * position + 2 + unaryNumberMoves true width 1 position
    [List.replicate timeRest tick, List.replicate time tick]
    [List.replicate positionRest tick, input] output.length

omit [Encodable Γ] in
private theorem writePosition_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writePosition (tm := tm) zero one tick code
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest input
          (output ++ (unaryNumberBits true position).flatMap (fun bit => code (.inl bit)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positionMoves tick width time timeRest position positionRest input output ⦄ := by
  let near := [List.replicate timeRest tick, List.replicate time tick]
  let parts := [List.replicate positionRest tick, input]
  let written := output ++ (unaryNumberBits true position).flatMap (fun bit => code (.inl bit))
  let moves := unaryNumberMoves true width 1 position near parts output.length
  have hw (bit : Bool) := hwidth (.inl bit)
  have ha := appendUnaryNumber_spec (tm := tm) zero one hne tick [] (fun bit => code (.inl bit))
    width hw true position near parts output label (origin - position) (elapsed + position + 2)
  norm_num only [near, parts, List.length_cons, List.length_nil, Nat.add_zero] at ha
  vcgen [writePosition,
    seekLeftEnd_le_spec (tm := tm) ((counterLeft [] near).tail)
      (StackTape.separateWords parts (StackTape.mapSome output))
      (List.replicate position tick).reverse [] label origin elapsed,
    ha,
    seekRightBlank_le_spec (tm := tm) (counterLeft [] near)
      (StackTape.separateWords parts (StackTape.mapSome written)) (List.replicate position tick)
      label (origin - position) (elapsed + position + 2 + moves)]
  all_goals
    simp_all [marked, positionMoves, near, parts, written, moves, counterLeft,
      unaryWord, StackTape.separateWords]
    all_goals lia

private def timeMoves (tick : Γ) (width time timeRest position positionRest : Nat)
    (input output : List Γ) : Nat :=
  unaryNumberMoves true width 1 time []
    [List.replicate timeRest tick, List.replicate position tick,
      List.replicate positionRest tick, input] output.length +
    2 * time + 2 * timeRest + 2 * position + 10

omit [Encodable Γ] in
private theorem writeTime_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeTime (tm := tm) zero one tick code
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest input
          (output ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          timeMoves tick width time timeRest position positionRest input output ⦄ := by
  let before := List.replicate time tick
  let near := [List.replicate timeRest tick]
  let current := List.replicate position tick
  let parts := [List.replicate positionRest tick, input]
  let sourceParts := [List.replicate timeRest tick, current] ++ parts
  let written := output ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit))
  let moves := unaryNumberMoves true width 1 time [] sourceParts output.length
  have hw (bit : Bool) := hwidth (.inl bit)
  have ha (position : ℤ) (steps : Nat) := appendUnaryNumber_spec (tm := tm) zero one hne tick []
    (fun bit => code (.inl bit)) width hw true time [] sourceParts output label position steps
  norm_num only [sourceParts, parts, List.length_cons, List.length_nil, List.length_append,
    Nat.add_zero] at ha
  have hv := onCounter_spec (tm := tm)
    (appendUnaryNumber tm zero one tick [] (fun bit => code (.inl bit)) true 0 5)
    before before near current (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts (StackTape.mapSome written)) label label moves
    (by simpa [counterRight, sourceParts, parts, before, current, near, written, moves,
      counterLeft, unaryWord] using ha)
    (origin - position) (elapsed + position + 2)
  norm_num only [near, List.length_cons, List.length_nil] at hv
  vcgen [writeTime,
    seekLeftEnd_le_spec (tm := tm)
      ((counterLeft [] [List.replicate timeRest tick, before]).tail)
      (StackTape.separateWords parts (StackTape.mapSome output)) current.reverse []
      label origin elapsed,
    hv,
    seekRightBlank_le_spec (tm := tm) (counterLeft before near)
      (StackTape.separateWords parts (StackTape.mapSome written)) current
      label (origin - position)
      (elapsed + position + 2 + moves + before.length + before.length +
        2 * (near.map List.length).sum + 4 * near.length + 4)]
  all_goals
    simp_all [marked, timeMoves, before, near, current, parts, sourceParts, written, moves,
      counterLeft, unaryWord, StackTape.separateWords]
    all_goals lia

private def numberBudget (width size : Nat) : Nat :=
  256 * (width + 1) * 2 ^ 2 * (size + 7) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem timeMoves_le (tick : Γ) (width time timeRest position positionRest size : Nat)
    (input output : List Γ)
    (hsize : time + timeRest + position + positionRest + input.length + output.length ≤ size) :
    timeMoves tick width time timeRest position positionRest input output ≤
      numberBudget width size + 2 * size + 10 := by
  have hu := unaryNumberMoves_le true width 1 time []
    [List.replicate timeRest tick, List.replicate position tick,
      List.replicate positionRest tick, input] output.length
  have hb : unaryNumberMoves true width 1 time []
      [List.replicate timeRest tick, List.replicate position tick,
        List.replicate positionRest tick, input] output.length ≤ numberBudget width size := by
    apply hu.trans
    dsimp [numberBudget]
    simp only [regionSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.length_replicate]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    lia
  dsimp [timeMoves]
  lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem positionMoves_le (tick : Γ) (width time timeRest position positionRest size : Nat)
    (input output : List Γ)
    (hsize : time + timeRest + position + positionRest + input.length + output.length ≤ size) :
    positionMoves tick width time timeRest position positionRest input output ≤
      numberBudget width size + 2 * size + 2 := by
  have hu := unaryNumberMoves_le true width 1 position
    [List.replicate timeRest tick, List.replicate time tick]
    [List.replicate positionRest tick, input] output.length
  have hb : unaryNumberMoves true width 1 position
      [List.replicate timeRest tick, List.replicate time tick]
      [List.replicate positionRest tick, input] output.length ≤ numberBudget width size := by
    apply hu.trans
    dsimp [numberBudget]
    simp only [regionSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.length_replicate]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    lia
  dsimp [positionMoves]
  lia

private def sign : Literal (Option (TMSAT.TapeSymbol Γ)) → CodeSymbol
  | .pos _ => .inr 0
  | .neg _ => .inr 1

private def itemWord (code : CodeSymbol → List Γ) (time position : Nat) :
    Option (Literal (Option (TMSAT.TapeSymbol Γ))) → List Γ
  | none => code (.inr 3) ++ code (.inr 4)
  | some literal => code (sign literal) ++
      (Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
        (symbolBits literal.name)).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)

private def writeLiteral (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (literal : Literal (Option (TMSAT.TapeSymbol Γ))) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendAcross tm (code (sign literal) ++ code (.inl true) ++ code (.inl false)) 2
  writeTime zero one tick code
  writePosition zero one tick code
  appendAcross tm ((symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++
    code (.inr 2)) 2

private def literalMoves (tick : Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (time timeRest position positionRest : Nat) (input output : List Γ)
    (literal : Literal (Option (TMSAT.TapeSymbol Γ))) : Nat :=
  let front := code (sign literal) ++ code (.inl true) ++ code (.inl false)
  let first := output ++ front
  let second := first ++ (unaryNumberBits true time).flatMap (fun bit => code (.inl bit))
  let third := second ++ (unaryNumberBits true position).flatMap (fun bit => code (.inl bit))
  let back := (symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)
  2 * (positionRest + input.length + 2 + output.length + front.length) + 8 +
    timeMoves tick width time timeRest position positionRest input first +
    positionMoves tick width time timeRest position positionRest input second +
    (2 * (positionRest + input.length + 2 + third.length + back.length) + 8)

private theorem writeLiteral_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (time timeRest position positionRest : Nat) (input output : List Γ)
    (literal : Literal (Option (TMSAT.TapeSymbol Γ)))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeLiteral (tm := tm) zero one tick code literal
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest input
          (output ++ itemWord code time position (some literal))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          literalMoves tick code width time timeRest position positionRest
            input output literal ⦄ := by
  let digits := fun bit => code (.inl bit)
  let front := code (sign literal) ++ code (.inl true) ++ code (.inl false)
  let first := output ++ front
  let second := first ++ (unaryNumberBits true time).flatMap digits
  let third := second ++ (unaryNumberBits true position).flatMap digits
  let back := (symbolBits literal.name).flatMap digits ++ code (.inr 2)
  let parts := [List.replicate positionRest tick, input]
  let left := StackTape.prepend (List.replicate position tick).reverse
    (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])
  let start := 2 * (regionSpan parts + output.length + front.length) + 8
  let middle := timeMoves tick width time timeRest position positionRest input first
  let later := positionMoves tick width time timeRest position positionRest input second
  have hf := appendAcross_le_spec (tm := tm) front parts output left label origin elapsed
  have hb := appendAcross_le_spec (tm := tm) back parts third left label origin
    (elapsed + start + middle + later)
  norm_num only [parts, List.length_cons, List.length_nil] at hf hb
  change Std.WP.Triple
    (appendAcross tm (code (sign literal) ++ code (.inl true) ++ code (.inl false)) 2) _ _ _ at hf
  change Std.WP.Triple
    (appendAcross tm ((symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++
      code (.inr 2)) 2) _ _ _ at hb
  vcgen [writeLiteral, hf,
    writeTime_spec zero one hne tick code width hwidth time timeRest position positionRest
      input first label origin (elapsed + start),
    writePosition_spec zero one hne tick code width hwidth time timeRest position positionRest
      input second label origin (elapsed + start + middle),
    hb]
  all_goals
    simp_all [marked, literalMoves, itemWord, Naming.bits, unaryNumberBits,
      BooleanTapeEncoding.pair, digits, front, first, second, third, back, parts, left,
      start, middle, later, regionSpan, List.append_assoc, List.flatMap_append]
    all_goals lia

private def itemBudget (width size : Nat) : Nat := 4096 * (width + 1) * (size + 8) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem literalMoves_le (tick : Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (time timeRest position positionRest : Nat) (input output : List Γ)
    (literal : Literal (Option (TMSAT.TapeSymbol Γ))) (size : Nat)
    (hsize : time + timeRest + position + positionRest + input.length +
      (output ++ itemWord code time position (some literal)).length ≤ size) :
    literalMoves tick code width time timeRest position positionRest input output literal ≤
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
  have hdata : time + timeRest + position + positionRest + input.length +
      third.length + back.length ≤ size := by
    simpa only [heq, third, second, first, List.length_append, Nat.add_assoc] using hsize
  have ht := timeMoves_le tick width time timeRest position positionRest size input first (by
    simp only [third, second, List.length_append] at hdata
    lia)
  have hp := positionMoves_le tick width time timeRest position positionRest size input second (by
    simp only [third, List.length_append] at hdata
    lia)
  have hf : positionRest + input.length + 2 + output.length + front.length ≤ size + 2 := by
    simp only [third, second, first, List.length_append] at hdata
    lia
  have hb : positionRest + input.length + 2 + third.length + back.length ≤ size + 2 := by lia
  have he : literalMoves tick code width time timeRest position positionRest input output literal =
      2 * (positionRest + input.length + 2 + output.length + front.length) + 8 +
      timeMoves tick width time timeRest position positionRest input first +
      positionMoves tick width time timeRest position positionRest input second +
      (2 * (positionRest + input.length + 2 + third.length + back.length) + 8) := rfl
  rw [he]
  dsimp [itemBudget, numberBudget] at *
  ring_nf at *
  lia

private def writeItems (zero one tick : Γ) (code : CodeSymbol → List Γ) :
    List (Option (Literal (Option (TMSAT.TapeSymbol Γ)))) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | none :: rest => do [TMQuery tm]
    appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2
    writeItems zero one tick code rest
  | some literal :: rest => do [TMQuery tm]
    writeLiteral zero one tick code literal
    writeItems zero one tick code rest

private theorem writeItems_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (items : List (Option (Literal (Option (TMSAT.TapeSymbol Γ)))))
    (time timeRest position positionRest : Nat) (input output : List Γ) (size : Nat)
    (hsize : time + timeRest + position + positionRest + input.length +
      (output ++ items.flatMap (itemWord code time position)).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, marked tick time timeRest position positionRest input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeItems (tm := tm) zero one tick code items
    ⦃ fun _ cost final => final.config = ⟨label,
        marked tick time timeRest position positionRest input
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
    have hfirst : time + timeRest + position + positionRest + input.length +
        (output ++ itemWord code time position item).length ≤ size := by
      simp only [List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    cases item with
    | none =>
      let parts := [List.replicate positionRest tick, input]
      let left := StackTape.prepend (List.replicate position tick).reverse
        (counterLeft [] [List.replicate timeRest tick, List.replicate time tick])
      have htime : 2 * (regionSpan parts + output.length +
          (code (.inr 3) ++ code (.inr 4)).length) + 8 ≤ itemBudget width size := by
        simp only [itemWord, List.length_append] at hfirst
        dsimp [parts, regionSpan, itemBudget]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.length_replicate, List.length_cons, List.length_nil, List.length_append]
        ring_nf at *
        lia
      have ha := appendAcross_le_spec (tm := tm) (code (.inr 3) ++ code (.inr 4))
        parts output left label origin elapsed
      norm_num only [parts, List.length_cons, List.length_nil] at ha
      simp only [writeItems]
      vcgen [ha, hrest]
      all_goals
        simp_all [marked, parts, left, itemWord, List.append_assoc]
        all_goals ring_nf at *
        all_goals lia
    | some literal =>
      have htime := literalMoves_le tick code width time timeRest position positionRest
        input output literal size hfirst
      simp only [writeItems]
      vcgen [writeLiteral_spec zero one hne tick code width hwidth time timeRest position
        positionRest input output literal label origin elapsed, hrest]
      all_goals
        simp_all [List.append_assoc]
        all_goals ring_nf at *
        all_goals lia

private def items (formula : CNF (Option (TMSAT.TapeSymbol Γ))) :
    List (Option (Literal (Option (TMSAT.TapeSymbol Γ)))) :=
  formula.flatMap fun clause => clause.map some ++ [none]

private theorem items_word (code : CodeSymbol → List Γ) (time position : Nat)
    (formula : CNF (Option (TMSAT.TapeSymbol Γ))) :
    (items formula).flatMap (itemWord code time position) =
      (formulaPrefix (formula.rename fun symbol =>
        Naming.bits .tape (encodingNatBool.encode time) (encodingNatBool.encode position)
          (symbolBits symbol))).flatMap code := by
  let name := fun symbol => Naming.bits .tape (encodingNatBool.encode time)
    (encodingNatBool.encode position) (symbolBits symbol)
  have hc (clause : Clause (Option (TMSAT.TapeSymbol Γ))) :
      (clause.map some ++ [none]).flatMap (itemWord code time position) =
        (certificateEncoding.encode (clause.rename name) ++ [(.inr 4 : CodeSymbol)]).flatMap code := by
    induction clause with
    | nil => simp [itemWord, Clause.rename, certificateEncoding_encode_nil]
    | cons literal rest ih =>
      cases literal <;>
        simp [itemWord, sign, Clause.rename, Literal.rename, certificateEncoding_encode_pos,
          certificateEncoding_encode_neg, certificateEncoding_encode_nil, name,
          List.flatMap_append, List.flatMap_map, List.append_assoc, ih]
  induction formula with
  | nil => simp [items, formulaPrefix, CNF.rename]
  | cons clause rest ih =>
    simpa [items, formulaPrefix, CNF.rename, List.flatMap_append] using
      congrArg₂ (· ++ ·) (hc clause) ih

private def rowWord (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (time positions : Nat) : List Γ :=
  (List.range positions).flatMap fun position =>
    (items (CNF.exactlyOne symbols)).flatMap (itemWord code time position)

private theorem rowWord_succ (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (time positions : Nat) :
    rowWord code symbols time (positions + 1) = rowWord code symbols time positions ++
      (items (CNF.exactlyOne symbols)).flatMap (itemWord code time positions) := by
  simp [rowWord, List.range_succ]

private theorem rowWord_length_mono (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (time : Nat) {first second : Nat}
    (h : first ≤ second) :
    (rowWord code symbols time first).length ≤ (rowWord code symbols time second).length :=
  ((List.range_sublist.mpr h).flatMap _).length_le

private theorem word_eq_rows (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (times positions : Nat) :
    word code symbols times positions =
      (List.range times).flatMap fun time => rowWord code symbols time positions := by
  simp [word, rowWord, items_word, symbolBits]

private theorem word_succ (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (times positions : Nat) :
    word code symbols (times + 1) positions = word code symbols times positions ++
      rowWord code symbols times positions := by
  simp [word_eq_rows, List.range_succ]

private theorem word_length_mono (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (positions : Nat) {first second : Nat}
    (h : first ≤ second) :
    (word code symbols first positions).length ≤ (word code symbols second positions).length := by
  simp only [word_eq_rows]
  exact ((List.range_sublist.mpr h).flatMap _).length_le

private theorem positions_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) (time timeRest positions : Nat)
    (input output : List Γ) (size : Nat)
    (hsize : time + timeRest + positions + input.length +
      (output ++ rowWord code symbols time positions).length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let left := counterLeft [] [List.replicate timeRest tick, List.replicate time tick]
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment left (List.replicate positions tick)
          (StackTape.separateWords [input] (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forBlocks tm tick [] (writeItems zero one tick code (items (CNF.exactlyOne symbols)))
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment left (List.replicate positions tick)
          (StackTape.separateWords [input]
            (StackTape.mapSome (output ++ rowWord code symbols time positions)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          positions * ((items (CNF.exactlyOne symbols)).length * itemBudget width size + 2) + 2 ⦄ := by
  dsimp only
  let left := counterLeft [] [List.replicate timeRest tick, List.replicate time tick]
  let tails := fun index => StackTape.separateWords [input]
    (StackTape.mapSome (output ++ rowWord code symbols time index))
  let body := writeItems (tm := tm) zero one tick code (items (CNF.exactlyOne symbols))
  let bound := (items (CNF.exactlyOne symbols)).length * itemBudget width size
  have ha : BlockAction tick [] positions (fun _ => left.tail) tails label body bound := by
    intro index rest hcount position steps
    have hp := rowWord_length_mono code symbols time (show index + 1 ≤ positions by lia)
    have hi : time + timeRest + index + rest + input.length +
        (output ++ rowWord code symbols time index ++
          (items (CNF.exactlyOne symbols)).flatMap (itemWord code time index)).length ≤ size := by
      rw [← List.append_assoc, ← rowWord_succ]
      simp only [List.length_append] at hp hsize ⊢
      lia
    vcgen [writeItems_spec zero one hne tick code width hwidth (items (CNF.exactlyOne symbols))
      time timeRest index rest input (output ++ rowWord code symbols time index) size
      (by simpa only [List.append_assoc] using hi) label position steps]
    all_goals
      simp_all [BlockAction, body, bound, left, tails, marked, counterLeft, unaryWord,
        rowWord_succ, List.append_assoc]
  vcgen [forBlocks_spec tick [] positions (fun _ => left.tail) tails label body bound ha
    origin elapsed]
  all_goals simp_all [left, tails, body, bound, counterLeft, unaryWord, rowWord]

private def visitPositions (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  seekRightBlank tm
  moveₜ .Right
  forBlocks tm tick [] action
  previousRegion tm
  moveₜ .Left

/--
This machine template writes the fixed symbol-choice clauses at every time and position
specified by its two unary words. It reads both indices from the tape and restores the
unary words, their separating blanks, and the starting head position.
-/
def writeChoices (tm : SingleTapeTM Γ) (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (symbols : List (Option (TMSAT.TapeSymbol Γ))) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  forBlocks tm tick []
    (visitPositions tick (writeItems zero one tick code (items (CNF.exactlyOne symbols))))

/-- This fixes all possible cell values once and writes their choices for every recorded cell. -/
noncomputable def writeTapeChoices (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeChoices tm zero one tick code (Finset.univ : Finset (Option (TMSAT.TapeSymbol Γ))).toList

end Algolean.Algorithms.TMSATToSAT.TapeChoices
