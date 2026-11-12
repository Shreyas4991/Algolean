/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.PolynomialFields
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.WordCopying
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.RegionNavigation
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Preparing polynomial bounds for a fixed verifier

The program writes each bound as repeated copies of one symbol. The number of copies is a
fixed polynomial of the original input length. It places these words before a preserved copy
of the input, with a blank between neighboring words. A temporary symbol begins both the
input and output, so neither word is empty. The final cleanup removes these symbols.

The polynomials and alphabet symbols are fixed when constructing the containing machine.
The machine reads the input and its length from its tape.
-/

public section

namespace Algolean.Algorithms.NPToSAT.Preparation

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Polynomial PolynomialWriter
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def joined (tick separator : Γ) (counts : List Nat) : List Γ :=
  List.intercalate [separator] (counts.map fun count => List.replicate count tick)

private theorem seekSeparator_spec (tick separator : Γ) (hne : tick ≠ separator)
    (count : Nat) (suffix : List Γ) (left tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment left (List.replicate count tick ++ separator :: suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      seekRightSymbol tm separator
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.prepend (List.replicate count tick).reverse left)
          (separator :: suffix) tail⟩ ∧ final.headPos = origin + count ∧
        cost.steps ≤ elapsed + count ⦄ := by
  induction count generalizing left origin elapsed with
  | zero =>
    unfold seekRightSymbol
    vcgen [Spec.while_false_spec]
    simp_all
  | succ count ih =>
    unfold seekRightSymbol
    vcgen [Spec.while_step_spec (loop := seekRightSymbol tm separator) (hloop := rfl),
      ih (StackTape.cons (some tick) left) (origin + 1) (elapsed + 1)]
    all_goals
      simp_all [List.replicate_succ, TMState.move, TMState.moveCost,
        List.reverse_cons, StackTape.prepend_append]
      all_goals lia

private def splitFields (tm : SingleTapeTM Γ) (separator : Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    seekRightSymbol tm separator
    tape ←ₜ none
    moveₜ .Right
    splitFields tm separator count
    previousRegion tm

private def splitMoves (first : Nat) : List Nat → Nat
  | [] => 0
  | next :: rest => 2 * first + 4 + splitMoves next rest

private theorem splitFields_spec (tick separator : Γ) (hne : tick ≠ separator)
    (first : Nat) (rest : List Nat) (left tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none left) (joined tick separator (first :: rest)) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      splitFields tm separator rest.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left) (List.replicate first tick)
          (StackTape.separateWords (rest.map fun count => List.replicate count tick) tail)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + splitMoves first rest ⦄ := by
  induction rest generalizing first left origin elapsed with
  | nil =>
    simp only [List.length_nil, splitFields]
    vcgen
    simp_all [joined, splitMoves]
  | cons next rest ih =>
    let firstWord := List.replicate first tick
    let later := StackTape.separateWords (rest.map fun count => List.replicate count tick) tail
    have hj : joined tick separator (first :: next :: rest) =
        firstWord ++ separator :: joined tick separator (next :: rest) := by
      simp [joined, firstWord, List.intercalate_cons_cons]
    have hi := ih next (StackTape.prepend firstWord.reverse (StackTape.cons none left))
      (origin + first + 1) (elapsed + first + 1)
    simp only [List.length_cons, splitFields, hj]
    vcgen [seekSeparator_spec (tm := tm) tick separator hne first
        (joined tick separator (next :: rest)) (StackTape.cons none left) tail
        label origin elapsed,
      hi,
      previousRegion_le_spec (tm := tm) left firstWord (List.replicate next tick) later label
        (origin + first + 1) (elapsed + first + 1 + splitMoves next rest)]
    all_goals
      simp_all [firstWord, later, splitMoves, TMState.write, TMState.move, TMState.moveCost]
      all_goals lia

private noncomputable def fieldParts (tick separator : Γ) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) : List (List Γ × Polynomial Nat) :=
  ([tick], first) :: rest.flatMap fun p => [([separator], 1), ([tick], p)]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem fieldParts_word (tick separator : Γ) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) (n : Nat) :
    fieldsWord (fieldParts tick separator first rest) n =
      joined tick separator ((first :: rest).map fun p => p.eval n) := by
  induction rest generalizing first with
  | nil => simp [fieldParts, fieldsWord, joined]
  | cons next rest ih =>
    have hparts : fieldParts tick separator first (next :: rest) =
        ([tick], first) :: ([separator], 1) :: fieldParts tick separator next rest := rfl
    simp only [hparts, fieldsWord, List.flatMap_cons, Polynomial.eval_one]
    have hr := ih next
    simp only [fieldsWord] at hr
    rw [hr]
    simp [joined, List.intercalate_cons_cons]

private theorem splitMoves_le (first : Nat) (rest : List Nat) :
    splitMoves first rest ≤ 2 * (first + rest.sum) + 4 * rest.length := by
  induction rest generalizing first with
  | nil => simp [splitMoves]
  | cons next rest ih =>
    have := ih next
    simp only [splitMoves, List.sum_cons, List.length_cons]
    lia

private noncomputable def writeBounds (tm : SingleTapeTM Γ) (symbols : List Γ)
    (tick separator : Γ) (first : Polynomial Nat) (rest : List (Polynomial Nat)) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeFields tm symbols (fieldParts tick separator first rest)
  nextRegion tm
  splitFields tm separator rest.length
  previousRegion tm

private theorem writeBounds_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (tick separator : Γ) (hne : tick ≠ separator) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) (input : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let counts := rest.map fun p => p.eval input.length
    let words := counts.map fun count => List.replicate count tick
    let work := (fieldsWork (fieldParts tick separator first rest)).eval input.length
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeBounds tm symbols tick separator first rest
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil input
        (StackTape.separateWords (List.replicate (first.eval input.length) tick :: words)
          StackTape.nil)⟩ ∧ final.headPos = origin ∧ cost.steps ≤ elapsed +
        fieldsTimeFactor (fieldParts tick separator first rest) * (input.length + work + 1) ^ 2 +
          2 * input.length + 4 + splitMoves (first.eval input.length) counts ⦄ := by
  dsimp only
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  let raw := joined tick separator ((first :: rest).map fun p => p.eval input.length)
  let firstWord := List.replicate (first.eval input.length) tick
  let words := (rest.map fun p => p.eval input.length).map fun count => List.replicate count tick
  let work := (fieldsWork (fieldParts tick separator first rest)).eval input.length
  let clock := initial.steps + fieldsTimeFactor (fieldParts tick separator first rest) *
    (input.length + work + 1) ^ 2
  have hf := writeFields_spec (tm := tm) symbols hcover (fieldParts tick separator first rest)
    input [] label origin initial.steps
  have hs := splitFields_spec (tm := tm) tick separator hne (first.eval input.length)
    (rest.map fun p => p.eval input.length) (StackTape.mapSome input.reverse) StackTape.nil
    label (origin + input.length + 1) (clock + input.length + 1)
  simp only [List.length_map] at hs
  have hb : StackTape.mapSome raw = StackTape.prepend raw (StackTape.cons none StackTape.nil) := by
    simp
  vcgen [writeBounds, hf,
    nextRegion_le_spec (tm := tm) StackTape.nil input raw StackTape.nil label origin clock,
    hs,
    previousRegion_le_spec (tm := tm) StackTape.nil input firstWord
      (StackTape.separateWords words StackTape.nil) label (origin + input.length + 1)
      (clock + input.length + 1 + splitMoves (first.eval input.length)
        (rest.map fun p => p.eval input.length))]
  all_goals
    simp_all [raw, firstWord, words, work, clock, fieldParts_word, BiTape.segment_start]
    all_goals lia

private def createDestination (tm : SingleTapeTM Γ) (tick : Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  rightRegions tm (count + 1)
  tape ←ₜ some tick
  leftRegions tm (count + 1)

private theorem createDestination_spec (tick : Γ) (input : List Γ) (words : List (List Γ))
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil input (StackTape.separateWords words StackTape.nil)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      createDestination tm tick words.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil input
          (StackTape.separateWords words (StackTape.mapSome [tick]))⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 8 * (input.length + regionSpan words + 2) ⦄ := by
  have hr := rightRegions_spec (tm := tm) input words.reverse [] StackTape.nil
    label origin elapsed
  have hl := leftRegions_spec (tm := tm) input words.reverse [tick] StackTape.nil label
    (origin + (input.length + (words.map List.length).sum + words.length + 1 : Nat))
    (elapsed + input.length + (words.map List.length).sum + words.length + 1)
  simp only [List.length_reverse] at hr hl
  have hw (left : StackTape Γ) :
      (BiTape.segment left [] StackTape.nil).write (some tick) =
        BiTape.segment left [tick] StackTape.nil := rfl
  have hstack : StackTape.cons (some tick) StackTape.nil = StackTape.mapSome [tick] := rfl
  vcgen [createDestination, hr, hl]
  all_goals
    simp_all [counterRight, TMState.write, regionSpan]
    all_goals lia

private theorem copyInput_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (input : List Γ) (words : List (List Γ)) (tick : Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil input
          (StackTape.separateWords words (StackTape.mapSome [tick]))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      copySymbolsAcross tm symbols (fun symbol => [symbol]) words.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil input
          (StackTape.separateWords words (StackTape.mapSome (tick :: input)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          copyBitsMoves 1 input.length (regionSpan words) 1 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [copySymbolsAcross_spec (tm := tm) symbols hcover (fun symbol => [symbol]) 1
    (by simp) input words [tick] StackTape.nil label origin initial.steps]
  all_goals simp_all

private def removeInput (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseRight tm
  moveₜ .Right

private theorem removeInput_spec (input first : List Γ) (rest : List (List Γ))
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil input
        (StackTape.separateWords (first :: rest) tail)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      removeInput tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil first (StackTape.separateWords rest tail)⟩ ∧
        final.headPos = origin + input.length + 1 ∧ cost.steps ≤ elapsed + input.length + 1 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [removeInput, eraseRight_spec (tm := tm) input
    (StackTape.separateWords (first :: rest) tail) label origin initial.steps]
  all_goals simp_all [TMState.move, TMState.moveCost]

private def copyAndFrame (tm : SingleTapeTM Γ) (symbols : List Γ) (tick : Γ)
    (count : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  createDestination tm tick count
  copySymbolsAcross tm symbols (fun symbol => [symbol]) count
  rightRegions tm (count + 1)
  nextRegion tm
  tape ←ₜ some tick
  leftRegions tm (count + 2)
  removeInput tm

private theorem copyAndFrame_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (tick : Γ) (input first : List Γ) (rest : List (List Γ)) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let words := first :: rest
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil input (StackTape.separateWords words StackTape.nil)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      copyAndFrame tm symbols tick words.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil first
          (StackTape.separateWords (rest ++ [tick :: input]) (StackTape.mapSome [tick]))⟩ ∧
        final.headPos = origin + input.length + 1 ∧ cost.steps ≤ elapsed +
          128 * (input.length + regionSpan words + 2) ^ 2 ⦄ := by
  dsimp only
  let words := first :: rest
  let travel := input.length + (words.map List.length).sum + words.length + 1
  let framed := tick :: input
  let clock₁ := elapsed + 8 * (input.length + regionSpan words + 2)
  let clock₂ := clock₁ + copyBitsMoves 1 input.length (regionSpan words) 1
  let clock₃ := clock₂ + travel
  let clock₄ := clock₃ + input.length + 2
  let clock₅ := clock₄ + input.length + (framed.length + (words.map List.length).sum) +
    3 * (words.length + 1) + 3
  have hr := rightRegions_spec (tm := tm) input words.reverse framed StackTape.nil
    label origin clock₂
  have hn := nextRegion_le_spec (tm := tm) (counterLeft input words.reverse) framed [] StackTape.nil
    label (origin + travel) clock₃
  have hl := leftRegions_spec (tm := tm) input (framed :: words.reverse) [tick] StackTape.nil label
    (origin + travel + input.length + 2) clock₄
  simp only [List.length_reverse] at hr
  simp only [List.length_cons, List.length_reverse] at hl
  have hw (left : StackTape Γ) :
      (BiTape.segment left [] StackTape.nil).write (some tick) =
        BiTape.segment left [tick] StackTape.nil := rfl
  have he := removeInput_spec (tm := tm) input first (rest ++ [framed])
    (StackTape.mapSome [tick]) label origin clock₅
  have hstack : StackTape.cons (some tick) StackTape.nil = StackTape.mapSome [tick] := rfl
  have hd := createDestination_spec (tm := tm) tick input words label origin elapsed
  have hc := copyInput_spec (tm := tm) symbols hcover input words tick label origin clock₁
  dsimp only [words] at hd hc hr hl
  vcgen [copyAndFrame, hd, hc,
    hr, hn, hl, he]
  all_goals
    simp_all [clock₁, clock₂, clock₃, clock₄, clock₅, travel, framed, words,
      counterRight, counterLeft, TMState.write,
      copyBitsMoves, regionSpan, List.map_append, List.sum_append, Nat.add_assoc]
    all_goals ring_nf at *
    all_goals lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem fieldParts_work (tick separator : Γ) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) (n : Nat) :
    (fieldsWork (fieldParts tick separator first rest)).eval n =
      2 * (first.eval n + (rest.map fun p => p.eval n).sum) + 2 * rest.length := by
  induction rest generalizing first with
  | nil => simp [fieldParts, fieldsWork]
  | cons next rest ih =>
    have hparts : fieldParts tick separator first (next :: rest) =
        ([tick], first) :: ([separator], 1) :: fieldParts tick separator next rest := rfl
    have hi := ih next
    simp only [fieldsWork] at hi
    simp only [hparts, fieldsWork, List.map_cons, List.sum_cons, eval_add, eval_mul,
      eval_C, eval_one, List.length_singleton]
    rw [hi]
    simp only [List.length_cons]
    ring

/--
This describes the unary bounds, a preserved input beginning with `tick`, and the output
beginning with `tick`. A blank separates neighboring words, including an empty first bound.
-/
@[expose] def layout (tick : Γ) (first : Nat) (rest : List Nat)
    (input output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (List.replicate first tick)
    (StackTape.separateWords ((rest.map fun count => List.replicate count tick) ++ [tick :: input])
      (StackTape.mapSome (tick :: output)))

/--
This fixed template prepares unary polynomial bounds and preserves the input. The first
polynomial and the remaining polynomial list determine the bound words in their tape order.
All polynomials, symbols, and comparisons are fixed before the program runs.
-/
noncomputable def prepare (tm : SingleTapeTM Γ) (symbols : List Γ) (tick separator : Γ)
    (first : Polynomial Nat) (rest : List (Polynomial Nat)) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  writeBounds tm symbols tick separator first rest
  copyAndFrame tm symbols tick (rest.length + 1)

/-- This polynomial bounds preparation, including counting, copying, and erasing the old input. -/
noncomputable def timeBound (tick separator : Γ) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) : Polynomial Nat :=
  C (fieldsTimeFactor (fieldParts tick separator first rest) + 1024) *
    (X + fieldsWork (fieldParts tick separator first rest) + C (rest.length + 10)) ^ 2

/--
Preparation writes the required unary bounds and one preserved copy of the input. It erases
the old input, leaves an empty output region, and finishes on the first bound's first cell.
-/
@[spec] theorem prepare_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (tick separator : Γ) (hne : tick ≠ separator) (first : Polynomial Nat)
    (rest : List (Polynomial Nat)) (input : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      prepare tm symbols tick separator first rest
    ⦃ fun _ cost final => final.config = ⟨label,
        layout tick (first.eval input.length) (rest.map fun p => p.eval input.length) input []⟩ ∧
        final.headPos = origin + input.length + 1 ∧ cost.steps ≤ elapsed +
          (timeBound tick separator first rest).eval input.length ⦄ := by
  let counts := rest.map fun p => p.eval input.length
  let words := (List.replicate (first.eval input.length) tick) ::
    counts.map fun count => List.replicate count tick
  let work := (fieldsWork (fieldParts tick separator first rest)).eval input.length
  let size := input.length + work + rest.length + 10
  let firstMoves := fieldsTimeFactor (fieldParts tick separator first rest) *
    (input.length + work + 1) ^ 2 + 2 * input.length + 4 +
      splitMoves (first.eval input.length) counts
  have hw : work = 2 * (first.eval input.length + counts.sum) + 2 * rest.length :=
    fieldParts_work tick separator first rest input.length
  have hs : regionSpan words = first.eval input.length + counts.sum + rest.length + 1 := by
    simp [words, counts, regionSpan, List.map_map, Function.comp_def, Nat.add_assoc]
  have hb : input.length + work + 1 ≤ size := by dsimp [size]; lia
  have hc : input.length + regionSpan words + 2 ≤ size := by dsimp [size]; lia
  have hi : 2 * input.length + 4 + splitMoves (first.eval input.length) counts ≤ 16 * size := by
    have hsplit := splitMoves_le (first.eval input.length) counts
    dsimp [size]
    simp only [counts, List.length_map] at hsplit
    lia
  have hpositive : 0 < size := by dsimp [size]; lia
  have hlinear : size ≤ size ^ 2 := by
    simpa only [pow_two] using Nat.le_mul_of_pos_right size hpositive
  have hfirst := Nat.mul_le_mul_left (fieldsTimeFactor (fieldParts tick separator first rest))
    (Nat.pow_le_pow_left hb 2)
  have hcopy := Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hc 2)
  have htotal : firstMoves + 128 * (input.length + regionSpan words + 2) ^ 2 ≤
      (timeBound tick separator first rest).eval input.length := by
    have hlin := Nat.mul_le_mul_left 16 hlinear
    simp only [timeBound, eval_mul, eval_C, eval_pow, eval_add, eval_X]
    dsimp only [size, firstMoves, work] at *
    rw [Nat.add_mul]
    lia
  have hwrite := writeBounds_spec (tm := tm) symbols hcover tick separator hne first rest input
    label origin elapsed
  have hframe := copyAndFrame_spec (tm := tm) symbols hcover tick input
    (List.replicate (first.eval input.length) tick)
    (counts.map fun count => List.replicate count tick) label origin (elapsed + firstMoves)
  simp only [List.length_cons, List.length_map, counts] at hframe
  vcgen [prepare, hwrite, hframe]
  all_goals simp_all [layout, firstMoves, words, counts, work, Nat.add_assoc]
  all_goals lia

end Algolean.Algorithms.NPToSAT.Preparation
