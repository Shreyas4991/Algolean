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

end Cslib.Turing.SingleTapeTM.Description
