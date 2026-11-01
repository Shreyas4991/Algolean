/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Basic
public import Mathlib.Computability.Encoding
public import Mathlib.Logic.Equiv.List

/-!
# Reusing encodings on tape alphabets

This file uses Mathlib's [Encoding](##Computability.Encoding), which stores a representation as
a list of symbols, a decoder, and a proof that decoding recovers the original value. It adds
ways to compose these representations and to move words into an extended alphabet.

Mathlib already encodes pairs over two separately tagged alphabets with
[encodingProd](##Computability.encodingProd). Its [Encodable](##Encodable) instances also cover
pairs, sums, and lists as natural numbers. We reuse those instances to obtain binary words.
The chosen numeric encoding determines the word length. The [pair](##Computability.Encoding.pair)
and [list](##Computability.Encoding.list) formats give lengths in terms of the encoded parts.

## Main definitions and results

* [Encoding.comp](##Computability.Encoding.comp) encodes a value and then encodes its word.
* [Encoding.ofEncodable](##Computability.Encoding.ofEncodable) writes a numeric code in binary.
* [words](##Algolean.Algorithms.Alphabet.words) includes a word in an extended alphabet.
* [Encoding.sum](##Computability.Encoding.sum) uses two markers to distinguish two alternatives.
-/

@[expose] public section

namespace Computability.Encoding

variable {α : Type u} {β : Type v} {Γ : Type w} {Δ : Type x}

/-- The first encoding produces a word, and the second encoding represents that whole word. -/
def comp (first : Encoding α Γ) (second : Encoding (List Γ) Δ) : Encoding α Δ where
  encode a := second.encode (first.encode a)
  decode word := match second.decode word with
    | none => none
    | some intermediate => first.decode intermediate
  decode_encode a := by simp

/--
A value's existing natural-number code is written using Mathlib's
[binary encoding](##Computability.encodingNatBool).
-/
def ofEncodable (α : Type u) [Encodable α] : Encoding α Bool where
  encode a := encodingNatBool.encode (Encodable.encode a)
  decode word := match encodingNatBool.decode word with
    | none => none
    | some n => Encodable.decode n
  decode_encode a := by simp

end Computability.Encoding

namespace Algolean.Algorithms.Alphabet

open Computability

/-- Every symbol is included as an original symbol; decoding rejects any added marker. -/
def words (Symbol : Type u) (markers : ℕ) : Encoding (List Symbol) (Extended Symbol markers) where
  encode word := word.map Sum.inl
  decode word := word.mapM Sum.getLeft?
  decode_encode word := by induction word <;> simp_all

/-- Including a word in a larger alphabet preserves its length. -/
@[simp] theorem length_words (word : List Symbol) (markers : ℕ) :
    ((words Symbol markers).encode word).length = word.length := by simp [words]

end Algolean.Algorithms.Alphabet

namespace Computability.Encoding

variable {α : Type u} {β : Type v} {Γ : Type w}

open Algolean.Algorithms.Alphabet

/-- A leading marker selects the first or second encoding, whose symbols share one alphabet. -/
def sum (first : Encoding α Γ) (second : Encoding β Γ) :
    Encoding (α ⊕ β) (Extended Γ 2) where
  encode
    | .inl a => .inr 0 :: (words Γ 2).encode (first.encode a)
    | .inr b => .inr 1 :: (words Γ 2).encode (second.encode b)
  decode
    | .inr tag :: rest =>
      match (words Γ 2).decode rest with
      | none => none
      | some word =>
        if tag = 0 then
          match first.decode word with
          | none => none
          | some a => some (.inl a)
        else
          match second.decode word with
          | none => none
          | some b => some (.inr b)
    | _ => none
  decode_encode value := by
    cases value <;> simp

/-- Selecting the first alternative adds exactly one marker to its encoded length. -/
@[simp] theorem length_sum_inl (first : Encoding α Γ) (second : Encoding β Γ) (a : α) :
    ((first.sum second).encode (.inl a)).length = (first.encode a).length + 1 := by
  simp [sum]

/-- Selecting the second alternative adds exactly one marker to its encoded length. -/
@[simp] theorem length_sum_inr (first : Encoding α Γ) (second : Encoding β Γ) (b : β) :
    ((first.sum second).encode (.inr b)).length = (second.encode b).length + 1 := by
  simp [sum]

end Computability.Encoding
