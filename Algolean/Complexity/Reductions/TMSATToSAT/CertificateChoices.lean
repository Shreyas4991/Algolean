/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.ReverseCopying
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryIteration
public import Algolean.Complexity.Reductions.TMSATToSAT.Naming
public import Algolean.Complexity.Reductions.TMSATToSAT.Variables
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.ComputeDegree

/-!
# Writing the choices for each certificate position

* `writeChoices` reads a unary count and writes exactly-one clauses for each position, using
  a symbol list fixed with the program. It uses the existing clauses and their existing order.
* `writeCertificateChoices` uses the whole alphabet and writes `certificateClauses` from the
  existing reduction. Each clause is ended and separated, but the formula is left open.
* Both writers preserve the bound, input, and earlier output. They erase the position counter
  and return the head to the bound's first cell. Their time bound is a polynomial of degree
  at most four, fixed for the chosen alphabet and encodings.

The bound is a repetition of one fixed, nonempty word, with one repetition per position.
A blank separates it from the preserved input, and another blank precedes the output.
All cells to the left are initially blank so the position counter can grow there.

These are machine templates. The alphabet enumeration, digit symbols, unary unit, and SAT
representations are fixed with the program. The count and position stay on the tape; neither
is a Lean parameter to the program.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.CertificateChoices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Computability Problems Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def symbolBits (symbol : Γ) : List Bool := encodingNatBool.encode (Encodable.encode symbol)

private def nameAt (bits : List Bool) (symbol : Γ) : SAT.Variable :=
  Naming.bits .certificate [] bits.reverse (symbolBits symbol)

private def sign : Literal Γ → CodeSymbol
  | .pos _ => .inr 0
  | .neg _ => .inr 1

private def itemWord (code : CodeSymbol → List Γ) (bits : List Bool) :
    Option (Literal Γ) → List Γ
  | none => code (.inr 3) ++ code (.inr 4)
  | some literal =>
    ((certificateEncoding.encode [literal.rename (nameAt bits)]).dropLast).flatMap code

private def literalMoves (width size distance output symbol : Nat) : Nat :=
  let start := 2 * (size + distance + output + 2 * width) + 12
  let header := lengthHeaderMoves width size distance (output + 2 * width)
  let copied := copyBitsMoves width size distance (output + width * (size + 3))
  start + header + copied +
    (2 * (size + distance + output + width * (2 * size + symbol + 4)) + 12)

private def writeLiteral (zero one : Γ) (code : CodeSymbol → List Γ) (count : Nat)
    (literal : Literal Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendFromRegion tm (code (sign literal) ++ code (.inl false)) count
  appendLengthHeader tm zero one (fun bit => code (.inl bit)) count
  copyBitsReverseAcross tm zero one (fun bit => code (.inl bit)) count
  appendFromRegion tm ((symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++
    code (.inr 2)) count

private def writeItem (zero one : Γ) (code : CodeSymbol → List Γ) (count : Nat) :
    Option (Literal Γ) → Prog (TMQuery tm) Unit
  | none => appendFromRegion tm (code (.inr 3) ++ code (.inr 4)) count
  | some literal => writeLiteral zero one code count literal

private def itemMoves (width size distance output : Nat) : Option (Literal Γ) → Nat
  | none => 2 * (size + distance + output + 2 * width) + 12
  | some literal => literalMoves width size distance output (symbolBits literal.name).length

private def itemWeight (width : Nat) : Option (Literal Γ) → Nat
  | none => 32 * (width + 1)
  | some literal => 32 * (width + 1) * ((symbolBits literal.name).length + 1)

private def weight (width : Nat) (items : List (Option (Literal Γ))) : Nat :=
  (items.map (itemWeight width)).sum

private def writeItems (zero one : Γ) (code : CodeSymbol → List Γ) (count : Nat) :
    List (Option (Literal Γ)) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | item :: items => do [TMQuery tm]
    writeItem zero one code count item
    writeItems zero one code count items

private theorem writeLiteral_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (literal : Literal Γ) (bits : List Bool) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeLiteral (tm := tm) zero one code parts.length literal
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ itemWord code bits (some literal))))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          literalMoves width bits.length (regionSpan parts) output.length
            (symbolBits literal.name).length ⦄ := by
  let digits := fun bit => code (.inl bit)
  let front := code (sign literal) ++ code (.inl false)
  let header := (List.replicate bits.length true ++ [false]).flatMap digits
  let copied := bits.reverse.flatMap digits
  have hf : front.length = 2 * width := by simp [front, hwidth]; lia
  have hh : header.length = width * (bits.length + 1) := by
    simp [header, digits, List.length_flatMap, hwidth, List.sum_replicate,
      Nat.mul_comm, Nat.mul_add]
  have hc : copied.length = width * bits.length := by
    simp [copied, digits, List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  have hs : ((symbolBits literal.name).flatMap digits).length =
      width * (symbolBits literal.name).length := by
    simp [digits, List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  vcgen [writeLiteral,
    appendFromRegion_spec (code (sign literal) ++ code (.inl false))
      (bits.map (fun bit => if bit then one else zero))
      parts output StackTape.nil label origin elapsed,
    appendLengthHeader_spec zero one hne (fun bit => code (.inl bit)) width
      (fun bit => hwidth (.inl bit))
      bits parts (output ++ front) StackTape.nil label origin
      (elapsed + 2 * (bits.length + regionSpan parts + output.length + 2 * width) + 12),
    copyBitsReverseAcross_spec zero one hne (fun bit => code (.inl bit)) width
      (fun bit => hwidth (.inl bit))
      bits parts (output ++ front ++ header) StackTape.nil label origin
      (elapsed + 2 * (bits.length + regionSpan parts + output.length + 2 * width) + 12 +
        lengthHeaderMoves width bits.length (regionSpan parts) (output.length + 2 * width)),
    appendFromRegion_spec ((symbolBits literal.name).flatMap (fun bit => code (.inl bit)) ++
      code (.inr 2))
      (bits.map (fun bit => if bit then one else zero)) parts (output ++ front ++ header ++ copied)
      StackTape.nil label origin
      (elapsed + 2 * (bits.length + regionSpan parts + output.length + 2 * width) + 12 +
        lengthHeaderMoves width bits.length (regionSpan parts) (output.length + 2 * width) +
        copyBitsMoves width bits.length (regionSpan parts)
          (output.length + width * (bits.length + 3)))]
  all_goals
    cases literal <;>
    simp_all [literalMoves, itemWord, nameAt, Naming.bits, sign, front, header,
      copied, digits, Literal.rename, BooleanTapeEncoding.pair, certificateEncoding_encode_pos,
      certificateEncoding_encode_neg, certificateEncoding_encode_nil, List.append_assoc,
      List.dropLast_cons_of_ne_nil, List.flatMap_map, -List.map_reverse, List.flatMap_replicate] <;>
    ring_nf at *

private theorem writeItem_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (item : Option (Literal Γ)) (bits : List Bool) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeItem (tm := tm) zero one code parts.length item
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome (output ++ itemWord code bits item)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          itemMoves width bits.length (regionSpan parts) output.length item ⦄ := by
  cases item with
  | none =>
    vcgen [writeItem,
      appendFromRegion_spec (code (.inr 3) ++ code (.inr 4))
        (bits.map (fun bit => if bit then one else zero)) parts output StackTape.nil
        label origin elapsed]
    all_goals
      simp_all [itemWord, itemMoves, two_mul, Nat.add_assoc]
  | some literal =>
    exact writeLiteral_spec zero one hne code width hwidth literal bits parts output
      label origin elapsed

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem itemWord_length_le (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (bits : List Bool) (item : Option (Literal Γ)) :
    (itemWord code bits item).length ≤ itemWeight width item * (bits.length + 1) := by
  cases item with
  | none =>
    simp only [itemWord, itemWeight, List.length_append, hwidth]
    ring_nf
    lia
  | some literal =>
    cases literal <;>
      simp [itemWord, itemWeight, Literal.rename, nameAt, Naming.bits, BooleanTapeEncoding.pair,
        certificateEncoding_encode_pos, certificateEncoding_encode_neg,
        certificateEncoding_encode_nil,
        List.dropLast_cons_of_ne_nil, List.length_flatMap, hwidth, List.sum_replicate,
        Function.comp_def]
    all_goals
      ring_nf; lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem itemMoves_le (width size distance output : Nat) (item : Option (Literal Γ)) :
    itemMoves width size distance output item ≤ itemWeight width item * (size + 1) *
      (size + distance + output + itemWeight width item * (size + 1) + 1) := by
  cases item <;> simp only [itemMoves, itemWeight, literalMoves, lengthHeaderMoves, copyBitsMoves]
  all_goals
    ring_nf; lia

private theorem writeItem_bound_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (item : Option (Literal Γ)) (bits : List Bool) (parts : List (List Γ)) (output : List Γ)
    (limit : Nat)
    (hlimit : bits.length + regionSpan parts + output.length +
      itemWeight width item * (bits.length + 1) + 1 ≤ limit)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeItem (tm := tm) zero one code parts.length item
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome (output ++ itemWord code bits item)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          itemWeight width item * (bits.length + 1) * limit ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  have htime := (itemMoves_le width bits.length (regionSpan parts) output.length item).trans
    (Nat.mul_le_mul_left _ hlimit)
  vcgen [writeItem_spec zero one hne code width hwidth item bits parts output
    label origin initial.steps]
  all_goals
    grind

private theorem writeItems_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (items : List (Option (Literal Γ))) (bits : List Bool) (parts : List (List Γ))
    (output : List Γ) (limit : Nat)
    (hlimit : bits.length + regionSpan parts + output.length +
      weight width items * (bits.length + 1) + 1 ≤ limit)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeItems (tm := tm) zero one code parts.length items
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ items.flatMap (itemWord code bits))))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          weight width items * (bits.length + 1) * limit ⦄ := by
  induction items generalizing output elapsed with
  | nil =>
    vcgen [writeItems]
    simp_all [weight]
  | cons item items ih =>
    have hl := itemWord_length_le code width hwidth bits item
    have hfirst : bits.length + regionSpan parts + output.length +
        itemWeight width item * (bits.length + 1) + 1 ≤ limit := by
      simp only [weight, List.map_cons, List.sum_cons, Nat.add_mul] at hlimit
      lia
    have hrest : bits.length + regionSpan parts + (output ++ itemWord code bits item).length +
        weight width items * (bits.length + 1) + 1 ≤ limit := by
      simp only [weight, List.map_cons, List.sum_cons, Nat.add_mul] at hlimit
      simp only [List.length_append, weight]
      lia
    vcgen [writeItems,
      writeItem_bound_spec zero one hne code width hwidth item bits parts output limit hfirst
        label origin elapsed,
      ih (output ++ itemWord code bits item) hrest
        (elapsed + itemWeight width item * (bits.length + 1) * limit)]
    all_goals
      simp_all [weight, List.append_assoc]; ring_nf at *; lia

private def items (formula : CNF Γ) : List (Option (Literal Γ)) :=
  formula.flatMap fun clause => clause.map some ++ [none]

private def schema (symbols : List Γ) : List (Option (Literal Γ)) :=
  items (CNF.exactlyOne symbols)

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem items_word (code : CodeSymbol → List Γ) (bits : List Bool) (formula : CNF Γ) :
    (items formula).flatMap (itemWord code bits) =
      (formulaPrefix (formula.rename (nameAt bits))).flatMap code := by
  have hclause (clause : Clause Γ) :
      (clause.map some ++ [none]).flatMap (itemWord code bits) =
        (certificateEncoding.encode (clause.rename (nameAt bits)) ++
          [(.inr 4 : CodeSymbol)]).flatMap code := by
    induction clause with
    | nil => simp [itemWord, Clause.rename, certificateEncoding_encode_nil]
    | cons literal rest ih =>
      cases literal <;>
        simp [itemWord, Clause.rename, Literal.rename, certificateEncoding_encode_pos,
          certificateEncoding_encode_neg, certificateEncoding_encode_nil, List.append_assoc,
          List.dropLast_cons_of_ne_nil, ih]
  induction formula with
  | nil => simp [items, formulaPrefix, CNF.rename]
  | cons clause rest ih =>
    simpa [items, formulaPrefix, CNF.rename, List.flatMap_append] using
      congrArg₂ (· ++ ·) (hclause clause) ih

/--
This is the encoded clause prefix written for the given symbol choices at every certificate
position. It uses the existing exactly-one clauses and omits the final formula-ending symbol.
-/
def word (code : CodeSymbol → List Γ) (symbols : List Γ) (count : Nat) : List Γ :=
  (List.finRange count).flatMap fun position =>
    (schema symbols).flatMap (itemWord code (encodingNatBool.encode position.val).reverse)

omit [Inhabited Γ] [Fintype Γ] in
private theorem word_succ (code : CodeSymbol → List Γ) (symbols : List Γ) (count : Nat) :
    word code symbols (count + 1) = word code symbols count ++
      (schema symbols).flatMap (itemWord code (encodingNatBool.encode count).reverse) := by
  simp [word, List.finRange_succ_last, List.flatMap_map]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem items_length_le (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (bits : List Bool) (items : List (Option (Literal Γ))) :
    (items.flatMap (itemWord code bits)).length ≤ weight width items * (bits.length + 1) := by
  induction items with
  | nil => simp [weight]
  | cons item items ih =>
    simpa only [List.flatMap_cons, List.length_append, weight, List.map_cons, List.sum_cons,
      Nat.add_mul] using Nat.add_le_add (itemWord_length_le code width hwidth bits item) ih

omit [Inhabited Γ] [Fintype Γ] in
private theorem word_length_le (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (symbols : List Γ) (count : Nat) :
    (word code symbols count).length ≤ weight width (schema symbols) * count * (count + 1) := by
  have hposition (position : Fin count) :
      ((schema symbols).flatMap
        (itemWord code (encodingNatBool.encode position.val).reverse)).length ≤
          weight width (schema symbols) * (count + 1) := by
    apply (items_length_le code width hwidth _ _).trans
    apply Nat.mul_le_mul_left
    have hs : position.val.size ≤ position.val := Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [List.length_reverse, length_encodingNatBool]
    have := position.isLt
    lia
  have h := List.sum_le_length_nsmul
    ((List.finRange count).map fun position =>
      ((schema symbols).flatMap
        (itemWord code (encodingNatBool.encode position.val).reverse)).length)
    (weight width (schema symbols) * (count + 1)) (by
      intro size hsize
      obtain ⟨position, _, rfl⟩ := List.mem_map.mp hsize
      exact hposition position)
  simpa [word, List.length_flatMap, nsmul_eq_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
    List.map_map, Function.comp_def] using h

private def workSize (width : Nat) (symbols : List Γ) (unit count input output : Nat) : Nat :=
  (unit + 1) * count + input + output + weight width (schema symbols) * (count + 1) ^ 2 + 4

/--
This machine template writes exactly-one clauses for the fixed list `symbols` at every position
specified by the unary word. The unary unit, symbol list, digit symbols, and SAT representations
are fixed with the program. The position and number of positions are read from the tape.
-/
def writeChoices (tm : SingleTapeTM Γ) (zero one tick : Γ) (unitTail : List Γ)
    (code : CodeSymbol → List Γ) (symbols : List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  forUnary tm zero one tick unitTail (writeItems zero one code 3 (schema symbols))

/-- This describes the unary bound, preserved input, and existing formula output on one tape. -/
@[expose] def layout (tick : Γ) (unitTail : List Γ) (count : Nat)
    (input output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (unaryWord (tick :: unitTail) count)
    (StackTape.separateWords [input] (StackTape.mapSome output))

/-- This states the tape contents, control state, and head position of the clause writer. -/
@[expose] def AtInput (tick : Γ) (unitTail : List Γ) (count : Nat) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, layout tick unitTail count input output⟩ ∧ current.headPos = origin

open Polynomial in
/-- This fixed polynomial bounds the moves in terms of the input and earlier output lengths. -/
noncomputable def timeBound (width unit : Nat) (symbols : List Γ) : Polynomial Nat :=
  let a := weight width (schema symbols)
  let b : Polynomial Nat := X + 1
  let size := C (unit + 3) * b + C a * b ^ 2 + 4
  b * (C a * b * size + 8 * C (unit + 1) * b) + 4 * C (unit + 1) * b

omit [Inhabited Γ] [Fintype Γ] in
/-- The time-bound polynomial has degree at most four. -/
theorem timeBound_natDegree_le (width unit : Nat) (symbols : List Γ) :
    (timeBound width unit symbols).natDegree ≤ 4 := by
  dsimp [timeBound]
  compute_degree

private theorem action_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (unitTail : List Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List Γ) (count : Nat) (input output : List Γ) (label : Option tm.State) :
    UnaryAction zero one tick unitTail count [input]
      (fun index => output ++ word code symbols index) label
      (writeItems (tm := tm) zero one code 3 (schema symbols))
      (weight width (schema symbols) * (count + 1) *
        workSize width symbols (unitTail.length + 1) count input.length output.length) := by
  intro index rest hcount origin elapsed
  let bits := (encodingNatBool.encode index).reverse
  let parts := [unaryWord (tick :: unitTail) index,
    unitTail ++ unaryWord (tick :: unitTail) rest, input]
  let a := weight width (schema symbols)
  have hi : index ≤ count := by lia
  have hb : bits.length ≤ count := by
    have hs : index.size ≤ index := Nat.size_le.mpr Nat.lt_two_pow_self
    simpa only [bits, List.length_reverse, length_encodingNatBool] using hs.trans hi
  have hspan : regionSpan parts ≤ (unitTail.length + 1) * count + input.length + 2 := by
    rw [← hcount]
    simp [parts, regionSpan, unaryWord, List.length_flatten]
    ring_nf
    lia
  have hout : (output ++ word code symbols index).length ≤
      output.length + a * count * (count + 1) := by
    have h := word_length_le code width hwidth symbols index
    have hm : a * index * (index + 1) ≤ a * count * (count + 1) := by gcongr
    simp only [List.length_append]
    exact Nat.add_le_add_left (h.trans hm) _
  have hweight : a * (bits.length + 1) ≤ a * (count + 1) := by gcongr
  have hlimit : bits.length + regionSpan parts + (output ++ word code symbols index).length +
      weight width (schema symbols) * (bits.length + 1) + 1 ≤
        workSize width symbols (unitTail.length + 1) count input.length output.length := by
    dsimp [workSize]
    dsimp [a] at hweight hout
    ring_nf at *
    lia
  have htime := Nat.mul_le_mul_right
    (workSize width symbols (unitTail.length + 1) count input.length output.length) hweight
  have hbody := writeItems_spec (tm := tm) zero one hne code width hwidth (schema symbols)
    bits parts (output ++ word code symbols index)
    (workSize width symbols (unitTail.length + 1) count input.length output.length) hlimit
    label origin elapsed
  norm_num only [parts, List.length_cons, List.length_nil] at hbody
  have hw := word_succ code symbols index
  vcgen [hbody]
  all_goals
    grind only [counterTape, counterWord, List.append_assoc]

omit [Inhabited Γ] [Fintype Γ] in
private theorem forUnaryMoves_le (width : Nat) (symbols : List Γ) (unit count input output : Nat)
    (size : Nat) (hcount : count ≤ size) (hinput : input ≤ size) (houtput : output ≤ size) :
    forUnaryMoves unit count (weight width (schema symbols) * (count + 1) *
      workSize width symbols unit count input output) ≤
        (timeBound width unit symbols).eval size := by
  have hw : workSize width symbols unit count input output ≤
      (unit + 3) * (size + 1) + weight width (schema symbols) * (size + 1) ^ 2 + 4 := by
    dsimp [workSize]
    calc
      _ ≤ (unit + 1) * size + size + size +
          weight width (schema symbols) * (size + 1) ^ 2 + 4 := by gcongr
      _ ≤ _ := by ring_nf; lia
  simp only [forUnaryMoves, timeBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_ofNat]
  gcongr; lia

/--
The writer appends the encoded exactly-one clauses for every position in the unary bound.
It preserves the bound, input, earlier output, and control state, erases its counter, and
restores the head. The same fixed polynomial bounds every run of this program.
-/
@[spec] theorem writeChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (unitTail : List Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (symbols : List Γ) (count : Nat) (input output : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtInput tick unitTail count input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeChoices tm zero one tick unitTail code symbols
    ⦃ fun _ cost final =>
        AtInput tick unitTail count input (output ++ word code symbols count) label origin final ∧
        cost.steps ≤ elapsed + (timeBound width (unitTail.length + 1) symbols).eval
          ((unaryWord (tick :: unitTail) count).length + input.length + output.length + 1) ⦄ := by
  let size := (unaryWord (tick :: unitTail) count).length + input.length + output.length + 1
  have hn : count ≤ size := by
    simp [size, unaryWord, List.length_flatten]
    have h := Nat.mul_le_mul_right count (show 1 ≤ unitTail.length + 1 by lia)
    lia
  have ht := forUnaryMoves_le width symbols (unitTail.length + 1) count input.length
    output.length size hn (by dsimp [size]; lia) (by dsimp [size]; lia)
  have hz : word code symbols 0 = [] := rfl
  vcgen [writeChoices, forUnary_spec zero one hne tick unitTail count [input]
    (fun index => output ++ word code symbols index) label
    (writeItems (tm := tm) zero one code 3 (schema symbols))
    (weight width (schema symbols) * (count + 1) *
      workSize width symbols (unitTail.length + 1) count input.length output.length)
    (action_spec zero one hne tick unitTail code width hwidth symbols count input output label)
    origin elapsed]
  all_goals
    grind only [AtInput, layout, List.append_nil]

omit [Inhabited Γ] in
/-- The generated word is exactly the existing certificate clauses in SAT's encoding. -/
theorem word_eq_certificateClauses (code : CodeSymbol → List Γ) (problem : TMSAT.Instance Γ) :
    word code (Finset.univ : Finset Γ).toList problem.certificateLength =
      (formulaPrefix ((certificateClauses problem).rename Variable.name)).flatMap code := by
  have hmap (position : Fin problem.certificateLength) :
      (CNF.exactlyOne ((Finset.univ : Finset Γ).toList.map (Variable.certificate position))).rename
          Variable.name =
        (CNF.exactlyOne (Finset.univ : Finset Γ).toList).rename
          (nameAt (encodingNatBool.encode position.val).reverse) := by
    rw [← CNF.rename_exactlyOne (Variable.certificate position)
      (by intro first second h; cases h; rfl)]
    simp only [CNF.rename, Clause.rename, List.map_map, Function.comp_def]
    congr 1
    funext clause
    congr 1
    funext literal
    cases literal <;> simp [Literal.rename, nameAt, Naming.bits, symbolBits, Variable.name]
  have hblock (position : Fin problem.certificateLength) :
      (schema (Finset.univ : Finset Γ).toList).flatMap
          (itemWord code (encodingNatBool.encode position.val).reverse) =
        (formulaPrefix ((CNF.exactlyOne
          ((Finset.univ : Finset Γ).toList.map (Variable.certificate position))).rename
            Variable.name)).flatMap code := by
    rw [schema, items_word, ← hmap position]
  simp only [word, certificateClauses, CNF.rename, formulaPrefix, List.map_flatMap,
    List.flatMap_assoc, List.flatMap_map]
  congr 1
  funext position
  simpa only [CNF.rename, formulaPrefix, List.flatMap_map, List.flatMap_assoc] using hblock position

/--
This machine template chooses from the whole fixed alphabet at every certificate position.
It fixes that alphabet's enumeration once and reads the number of positions from the unary
bound on the tape. It writes the certificate part of the existing TMSAT-to-SAT formula.
-/
noncomputable def writeCertificateChoices (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (unitTail : List Γ) (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeChoices tm zero one tick unitTail code (Finset.univ : Finset Γ).toList

/--
The program appends precisely the certificate clauses already defined for the given instance.
It preserves the unary bound and input, clears its position counter, and restores the head.
The instance occurs only in the specification; the running program reads its bound from the tape.
-/
@[spec] theorem writeCertificateChoices_spec (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (unitTail : List Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (problem : TMSAT.Instance Γ)
    (input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current =>
        AtInput tick unitTail problem.certificateLength input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeCertificateChoices tm zero one tick unitTail code
    ⦃ fun _ cost final =>
        AtInput tick unitTail problem.certificateLength input
          (output ++
            (formulaPrefix ((certificateClauses problem).rename Variable.name)).flatMap code)
          label origin final ∧ cost.steps ≤ elapsed +
          (timeBound width (unitTail.length + 1) (Finset.univ : Finset Γ).toList).eval
            ((unaryWord (tick :: unitTail) problem.certificateLength).length +
              input.length + output.length + 1) ⦄ := by
  simpa only [writeCertificateChoices, word_eq_certificateClauses] using
    writeChoices_spec (tm := tm) zero one hne tick unitTail code width hwidth
      (Finset.univ : Finset Γ).toList problem.certificateLength input output label origin elapsed

/-- The completed run appends the certificate clauses and preserves the input and starting head. -/
theorem writeCertificateChoices_correct (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (unitTail : List Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (problem : TMSAT.Instance Γ)
    (input output : List Γ) (s : TMState tm)
    (hs : s.config.BiTape = layout tick unitTail problem.certificateLength input output) :
    let result := output ++
      (formulaPrefix ((certificateClauses problem).rename Variable.name)).flatMap code
    let size := (unaryWord (tick :: unitTail) problem.certificateLength).length +
      input.length + output.length + 1
    ∃ steps, Runs (writeCertificateChoices tm zero one tick unitTail code) s
      (layout tick unitTail problem.certificateLength input result) s.headPos steps ∧
      steps ≤
        (timeBound width (unitTail.length + 1) (Finset.univ : Finset Γ).toList).eval size := by
  apply Spec.runs_le
  vcgen [writeCertificateChoices_spec zero one hne tick unitTail code width hwidth problem
    input output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all [AtInput]

/-- The same polynomial bounds the head moves for every unary bound and preserved input word. -/
theorem writeCertificateChoices_time_bound (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (unitTail : List Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (problem : TMSAT.Instance Γ)
    (input output : List Γ) (s : TMState tm)
    (hs : s.config.BiTape = layout tick unitTail problem.certificateLength input output) :
    let size := (unaryWord (tick :: unitTail) problem.certificateLength).length +
      input.length + output.length + 1
    ∃ cost final, Completes (writeCertificateChoices tm zero one tick unitTail code) s cost final ∧
      cost.steps ≤
        (timeBound width (unitTail.length + 1) (Finset.univ : Finset Γ).toList).eval size := by
  obtain ⟨steps, ⟨cost, final, hc, _, _, ht⟩, hb⟩ :=
    writeCertificateChoices_correct zero one hne tick unitTail code width hwidth problem
      input output s hs
  exact ⟨cost, final, hc, ht ▸ hb⟩

end Algolean.Algorithms.TMSATToSAT.CertificateChoices
