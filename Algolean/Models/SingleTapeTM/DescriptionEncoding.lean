/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Description
public import Algolean.Models.SingleTapeTM.Alphabet.List
public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Mathlib.Logic.Equiv.Finset

/-!
# Encoding finite transition tables

* `Description.encoding` stores the largest state number, initial state, and every transition.
* Each table is a list of rows, and each row lists the cases for the scanned cell.
* Decoding checks the table dimensions and rejects references to nonexistent states.
* `wordEncoding` stores words over a fixed finite alphabet using binary symbol codes. Its size
  grows at most linearly with the number of input symbols.

Each transition uses a binary numeric code. Separate markers delimit rows, tables, and fields.
The machine's states are numbered from zero through `states`.
-/

@[expose] public section

namespace Cslib.Turing.SingleTapeTM.Description

open Computability Algolean.Algorithms.Alphabet

/-- These symbols separate the transitions within one row of the table. -/
abbrev RowSymbol := Extended Bool 2

/-- These symbols also separate the rows within the table. -/
abbrev TableSymbol := Extended RowSymbol 2

/-- These symbols also separate the initial state from the transition table. -/
abbrev BodySymbol := Extended TableSymbol 1

/-- These symbols also separate the largest state number from the rest of the description. -/
abbrev CodeSymbol := Extended BodySymbol 1

variable {Symbol : Type} [Fintype Symbol] [Encodable Symbol]

/-- A row records one transition for each scanned cell value, in numeric code order. -/
def rowEncoding (states : ℕ) :
    Encoding (Option Symbol → Transition Symbol states) RowSymbol :=
  ((Encoding.ofEncodable (Transition Symbol states)).finFunction
    (Fintype.card (Option Symbol))).ofEquiv
      (Equiv.arrowCongr Encodable.fintypeEquivFin (Equiv.refl _))

/-- The table records one row for every state, in state order. -/
def tableEncoding (states : ℕ) :
    Encoding (Fin (states + 1) → Option Symbol → Transition Symbol states) TableSymbol :=
  (rowEncoding states).finFunction (states + 1)

/-- The initial state precedes the table, with a separator between them. -/
def bodyEncoding (states : ℕ) :
    Encoding (Fin (states + 1) ×
      (Fin (states + 1) → Option Symbol → Transition Symbol states)) BodySymbol :=
  (((Encoding.ofEncodable (Fin (states + 1))).comp (words Bool 2)).comp
    (words RowSymbol 2)).pair (tableEncoding states)

/--
The largest state number determines the valid states and the dimensions of the transition table.
Decoding recovers the entire description, including its initial state and every transition.
-/
def encoding : Encoding (Description Symbol) CodeSymbol :=
  ((((encodingNatBool.comp (words Bool 2)).comp (words RowSymbol 2)).comp
    (words TableSymbol 1)).sigma (bodyEncoding (Symbol := Symbol))).ofEquiv equiv

/-- Boolean words use the original bits of the description alphabet and contain no markers. -/
def bitEncoding : Encoding (List Bool) CodeSymbol :=
  ((((encodingList Bool).comp (words Bool 2)).comp (words RowSymbol 2)).comp
    (words TableSymbol 1)).comp (words BodySymbol 1)

/-- Adding the description markers to the alphabet preserves the length of a Boolean word. -/
@[simp] theorem length_bitEncoding (word : List Bool) :
    (bitEncoding.encode word).length = word.length := by
  simp [bitEncoding, Encoding.comp, words, encodingList]

/-- A successfully decoded Boolean word consists of its bits with the alphabet tags added. -/
theorem decode_bitEncoding_eq_some_iff {word : List CodeSymbol} {bits : List Bool} :
    bitEncoding.decode word = some bits ↔ word = bitEncoding.encode bits := by
  simp only [bitEncoding, Encoding.decode_comp_eq_some_iff, decode_words_eq_some_iff]
  simp [encodingList, Encoding.comp, words]

omit [Fintype Symbol] in
/--
A word over the fixed finite alphabet is stored as a list of binary symbol codes. Each symbol
code has an ending, and the list has its own ending. The description alphabet stays the same
when the input alphabet changes.
-/
def wordEncoding : Encoding (List Symbol) CodeSymbol :=
  (((Encoding.ofEncodable Symbol).list.comp (words RowSymbol 2)).comp
    (words TableSymbol 1)).comp (words BodySymbol 1)

omit [Fintype Symbol] in
/-- This nonempty word stores one symbol in binary, followed by its ending separator. -/
def wordSymbolCode (symbol : Symbol) : List CodeSymbol :=
  ((Encoding.ofEncodable Symbol).encode symbol).map
    (fun bit => .inl (.inl (.inl (.inl bit)))) ++ [.inl (.inl (.inl (.inr 0)))]

/-- This symbol ends the entire encoded input word. -/
def wordEnd : CodeSymbol := .inl (.inl (.inl (.inr 1)))

omit [Fintype Symbol] in
/-- Encoding an input concatenates its symbol codes and then writes the word ending. -/
theorem encode_wordEncoding (input : List Symbol) :
    wordEncoding.encode input = input.flatMap wordSymbolCode ++ [wordEnd] := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
    simp_all [wordEncoding, wordSymbolCode, wordEnd, Encoding.comp, Encoding.list,
      words, List.map_flatMap, List.map_append, List.map_map,
      Function.comp_def, List.append_assoc]

omit [Fintype Symbol] in
/-- Every symbol code contains at least its ending separator. -/
theorem wordSymbolCode_ne_nil (symbol : Symbol) : wordSymbolCode symbol ≠ [] := by
  simp [wordSymbolCode]

omit [Fintype Symbol] in
/-- The input encoding counts every symbol code, its ending, and the ending of the whole word. -/
@[simp] theorem length_wordEncoding (word : List Symbol) :
    (wordEncoding.encode word).length =
      (word.map (fun symbol => ((Encoding.ofEncodable Symbol).encode symbol).length)).sum +
        word.length + 1 := by
  simp [wordEncoding, Encoding.comp]

omit [Fintype Symbol] in
/-- Every decoded input symbol needs an ending in the input word, so decoded words fit in it. -/
theorem length_le_of_decode_wordEncoding {word : List CodeSymbol} {input : List Symbol}
    (h : wordEncoding.decode word = some input) : input.length + 1 ≤ word.length := by
  obtain ⟨body, hbody, h⟩ := (Encoding.decode_comp_eq_some_iff _ _).mp h
  obtain ⟨table, htable, h⟩ := (Encoding.decode_comp_eq_some_iff _ _).mp h
  obtain ⟨row, hrow, h⟩ := (Encoding.decode_comp_eq_some_iff _ _).mp h
  rw [decode_words_eq_some_iff.mp hbody, decode_words_eq_some_iff.mp htable,
    decode_words_eq_some_iff.mp hrow]
  simpa using Encoding.length_le_of_decode_list (Encoding.ofEncodable Symbol) h

omit [Fintype Symbol] in
/--
For a fixed finite alphabet, encoding a word increases its length by at most a constant factor
and one ending symbol. The factor depends on the alphabet's chosen symbol codes, not on the word.
-/
theorem exists_wordEncoding_length_bound [Finite Symbol] :
    ∃ factor : ℕ, ∀ word : List Symbol,
      (wordEncoding.encode word).length ≤ factor * word.length + 1 := by
  classical
  let := Fintype.ofFinite Symbol
  let width := Finset.univ.sup (fun symbol : Symbol =>
    ((Encoding.ofEncodable Symbol).encode symbol).length)
  refine ⟨width + 1, ?_⟩
  intro word
  induction word with
  | nil => simp
  | cons symbol rest ih =>
    have hsymbol : ((Encoding.ofEncodable Symbol).encode symbol).length ≤ width :=
      Finset.le_sup (f := fun symbol : Symbol =>
        ((Encoding.ofEncodable Symbol).encode symbol).length) (Finset.mem_univ symbol)
    simp only [length_wordEncoding, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    simp only [Nat.mul_add, Nat.mul_one]
    lia

end Cslib.Turing.SingleTapeTM.Description
