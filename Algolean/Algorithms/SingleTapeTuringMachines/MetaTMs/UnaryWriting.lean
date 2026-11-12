/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockCounting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.ReverseCopying

/-!
# Writing a unary count in binary

* `appendUnaryNumber` counts repetitions of a fixed word and appends the count in binary to
  the output. It can first write the number of binary digits, allowing a decoder to distinguish
  consecutive numbers.
* The source word and intervening words are preserved. A temporary counter grows left into
  blank cells and is erased before the head returns to the source's first cell.

This is a machine template. Its symbols, output representations, and numbers of intervening
words are fixed once. The number to write is read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Computability Problems
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the existing binary encoding of a number, optionally preceded by its digit count. -/
@[expose] def unaryNumberBits (header : Bool) (number : Nat) : List Bool :=
  if header then BooleanTapeEncoding.pair (encodingNatBool.encode number) []
  else encodingNatBool.encode number

/-- This machine template appends the counter's binary number and erases the counter. -/
@[expose] def appendCounterNumber (zero one : Γ) (code : Bool → List Γ)
    (header : Bool) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  if header then
    appendLengthHeader tm zero one code count
  else
    pure ()
  copyBitsReverseAcross tm zero one code count
  eraseRight tm

/-- This counts writing the optional length header, copying the digits, and erasing the counter. -/
@[expose] def counterNumberMoves (header : Bool) (width size distance output : Nat) : Nat :=
  (if header then lengthHeaderMoves width size distance output else 0) +
    copyBitsMoves width size distance (output + if header then width * (size + 1) else 0) + size

/-- Writing a canonical counter appends the chosen number word and clears its cells exactly. -/
@[spec] theorem appendCounterNumber_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (number : Nat) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (counterWord zero one number)
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendCounterNumber (tm := tm) zero one code header parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil []
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header number).flatMap code)))⟩ ∧
        final.headPos = origin + number.size ∧ cost.steps = elapsed +
          counterNumberMoves header width number.size (regionSpan parts) output.length ⦄ := by
  let digits := (encodingNatBool.encode number).reverse
  let head := (List.replicate number.size true ++ [false]).flatMap code
  have hlen : head.length = width * (number.size + 1) := by
    simp [head, List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm, Nat.mul_add]
  have hcopy (out : List Γ) (steps : Nat) := copyBitsReverseAcross_spec (tm := tm)
    zero one hne code width hwidth digits parts out StackTape.nil label origin steps
  have herase (out : List Γ) (steps : Nat) := eraseRight_segment_spec (tm := tm)
    StackTape.nil (StackTape.separateWords parts (StackTape.mapSome out))
    (counterWord zero one number) label origin steps
  cases header
  · vcgen [appendCounterNumber, hcopy output elapsed,
      herase (output ++ (encodingNatBool.encode number).flatMap code)
        (elapsed + copyBitsMoves width number.size (regionSpan parts) output.length)]
    all_goals simp_all [counterWord, digits, unaryNumberBits, counterNumberMoves, Nat.add_assoc]
  · vcgen [appendCounterNumber,
      appendLengthHeader_spec (tm := tm) zero one hne code width hwidth digits parts output
        StackTape.nil label origin elapsed,
      hcopy (output ++ head)
        (elapsed + lengthHeaderMoves width number.size (regionSpan parts) output.length),
      herase (output ++ head ++ (encodingNatBool.encode number).flatMap code)
        (elapsed + lengthHeaderMoves width number.size (regionSpan parts) output.length +
          copyBitsMoves width number.size (regionSpan parts) (output.length + head.length))]
    all_goals
      simp_all [counterWord, digits, head, unaryNumberBits, counterNumberMoves,
        BooleanTapeEncoding.pair, List.flatMap_append, List.append_assoc]
      all_goals lia

/-- The same counter writer preserves an upper time bound with its exact additional move count. -/
theorem appendCounterNumber_le_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (number : Nat) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (counterWord zero one number)
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendCounterNumber (tm := tm) zero one code header parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil []
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header number).flatMap code)))⟩ ∧
        final.headPos = origin + number.size ∧ cost.steps ≤ elapsed +
          counterNumberMoves header width number.size (regionSpan parts) output.length ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [appendCounterNumber_spec zero one hne code width hwidth header number parts output
    label origin initial.steps]
  all_goals simp_all

/--
This machine template appends the unary source's number using the chosen binary symbol words.
`near` is the number of words between its temporary counter and the source. `distance` is
the number of words between that counter and the output. Both numbers are fixed with the program.
-/
def appendUnaryNumber (tm : SingleTapeTM Γ) (zero one tick : Γ) (unitTail : List Γ)
    (code : Bool → List Γ) (header : Bool) (near distance : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  countBlocks tm zero one tick unitTail near
  onCounter tm (appendCounterNumber zero one code header distance) near

/-- This bounds counting the source, writing its number, erasing the counter, and both visits. -/
def unaryNumberMoves (header : Bool) (width unit count : Nat)
    (near parts : List (List Γ)) (output : Nat) : Nat :=
  countBlocksMoves unit 0 count (regionSpan near) +
    counterNumberMoves header width count.size
      (regionSpan near + count * unit + 1 + regionSpan parts) output +
    count.size + 2 * (near.map List.length).sum + 4 * near.length + 4

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- The number writer's move bound is quadratic in the lengths of the words it reads and crosses. -/
theorem unaryNumberMoves_le (header : Bool) (width unit count : Nat)
    (near parts : List (List Γ)) (output : Nat) :
    unaryNumberMoves header width unit count near parts output ≤
      256 * (width + 1) * (unit + 1) ^ 2 *
        (count + regionSpan near + regionSpan parts + output + 3) ^ 2 := by
  let total := count + regionSpan near + regionSpan parts + output + 2
  have hc : count ≤ total := by dsimp [total]; lia
  have hn : regionSpan near ≤ total := by dsimp [total]; lia
  have hp : regionSpan parts ≤ total := by dsimp [total]; lia
  have ho : output ≤ total := by dsimp [total]; lia
  have hs : count.size ≤ total := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hc
  have hd : regionSpan near + count * unit + 1 + regionSpan parts ≤ (unit + 3) * total := by
    have hm := Nat.mul_le_mul_right unit hc
    dsimp [total] at *
    ring_nf at *
    lia
  have hl : (near.map List.length).sum ≤ total := by dsimp [total, regionSpan]; lia
  have hh : near.length ≤ total := by dsimp [total, regionSpan]; lia
  have hcount : countBlocksMoves unit 0 count (regionSpan near) ≤
      countBlocksMoves unit 0 total total := by
    dsimp [countBlocksMoves]
    gcongr
  have hcounter : counterNumberMoves header width count.size
      (regionSpan near + count * unit + 1 + regionSpan parts) output ≤
      counterNumberMoves header width total ((unit + 3) * total) total := by
    cases header <;> simp only [counterNumberMoves, Bool.false_eq_true,
      ite_false, ite_true, lengthHeaderMoves, copyBitsMoves]
    all_goals gcongr
  have hmain : unaryNumberMoves header width unit count near parts output ≤
      countBlocksMoves unit 0 total total +
        counterNumberMoves header width total ((unit + 3) * total) total + 7 * total + 4 := by
    dsimp only [unaryNumberMoves]
    calc
      _ ≤ countBlocksMoves unit 0 total total +
          counterNumberMoves header width total ((unit + 3) * total) total +
            total + 2 * total + 4 * total + 4 := by gcongr
      _ = _ := by ring
  calc
    _ ≤ _ := hmain
    _ ≤ 256 * (width + 1) * (unit + 1) ^ 2 * (total + 1) ^ 2 := by
      cases header <;> simp only [counterNumberMoves, Bool.false_eq_true,
        ite_false, ite_true, countBlocksMoves, lengthHeaderMoves, copyBitsMoves]
      all_goals
        ring_nf
        lia
    _ = _ := by rfl

/--
The appended word is the existing binary encoding of the source count, with the chosen header.
The source and neighboring words are preserved, the counter is erased, and the head is restored.
-/
@[spec] theorem appendUnaryNumber_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (unitTail : List Γ) (code : Bool → List Γ) (width : Nat)
    (hwidth : ∀ bit, (code bit).length = width) (header : Bool) (count : Nat)
    (near parts : List (List Γ)) (output : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft [] near) (unaryWord (tick :: unitTail) count)
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendUnaryNumber tm zero one tick unitTail code header near.length
        (near.length + 1 + parts.length)
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (counterLeft [] near) (unaryWord (tick :: unitTail) count)
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header count).flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          unaryNumberMoves header width (unitTail.length + 1) count near parts output.length ⦄ := by
  let source := unaryWord (tick :: unitTail) count
  let allParts := near.reverse ++ [source] ++ parts
  let written := output ++ (unaryNumberBits header count).flatMap code
  let budget := counterNumberMoves header width count.size (regionSpan allParts) output.length
  have hz : encodingNatBool.encode 0 = [] := rfl
  have hspan : regionSpan allParts =
      regionSpan near + count * (unitTail.length + 1) + 1 + regionSpan parts := by
    simp [allParts, source, regionSpan, unaryWord, List.length_flatten,
      List.map_append, List.sum_append]
    ring
  have ha (position : ℤ) (steps : Nat) :
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment StackTape.nil (counterWord zero one count)
            (counterRight near source (StackTape.separateWords parts (StackTape.mapSome output)))⟩ ∧
          current.headPos = position ∧ cost.steps ≤ steps ⦄
        appendCounterNumber (tm := tm) zero one code header (near.length + 1 + parts.length)
      ⦃ fun _ cost final => final.config = ⟨label,
          BiTape.segment StackTape.nil []
            (counterRight near source
              (StackTape.separateWords parts (StackTape.mapSome written)))⟩ ∧
          final.headPos = position + (counterWord zero one count).length ∧
          cost.steps ≤ steps + budget ⦄ := by
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hcost⟩
    have hc := appendCounterNumber_spec (tm := tm) zero one hne code width hwidth header count
      allParts output label position initial.steps
    simp only [allParts, List.length_append, List.length_reverse, List.length_singleton] at hc
    vcgen [hc]
    all_goals
      simp_all [counterRight, allParts, StackTape.separateWords_append, written, budget,
        counterWord]
  vcgen [appendUnaryNumber,
    countBlocks_spec (tm := tm) zero one hne tick unitTail 0 count near
      (StackTape.separateWords parts (StackTape.mapSome output)) label origin elapsed,
    onCounter_spec (tm := tm)
      (appendCounterNumber zero one code header (near.length + 1 + parts.length))
      (counterWord zero one count) [] near source
      (StackTape.separateWords parts (StackTape.mapSome output))
      (StackTape.separateWords parts (StackTape.mapSome written)) label label budget
      (by simpa only [List.length_nil, Nat.cast_zero, sub_zero] using ha) origin
      (elapsed + countBlocksMoves (unitTail.length + 1) 0 count (regionSpan near))]
  all_goals
    simp_all [source, written, unaryNumberMoves, budget, counterWord, Nat.add_assoc]

end Algolean.Algorithms.SingleTapeTuringMachines
