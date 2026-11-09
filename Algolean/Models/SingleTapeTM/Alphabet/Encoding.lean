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

* `Encoding.ofEquiv` reuses an encoding across an equivalence of types.
* `Encoding.subtype` rejects decoded values that fail a specified condition.
* The decoding lemmas describe successful decoding through equivalences and compositions.
* [Encoding.comp](##Computability.Encoding.comp) encodes a value and then encodes its word.
* [Encoding.ofEncodable](##Computability.Encoding.ofEncodable) writes a numeric code in binary.
* [words](##Algolean.Algorithms.Alphabet.words) includes a word in an extended alphabet.
* [Encoding.sum](##Computability.Encoding.sum) uses two markers to distinguish two alternatives.
-/

@[expose] public section

namespace Computability.Encoding

variable {α : Type u} {β : Type v} {Γ : Type w} {Δ : Type x}

/-- Renaming symbols bijectively preserves the represented values and word lengths. -/
def mapSymbols (encoding : Encoding α Γ) (rename : Γ ≃ Δ) : Encoding α Δ where
  encode value := (encoding.encode value).map rename
  decode word := encoding.decode (word.map rename.symm)
  decode_encode value := by simp

/-- Renaming symbols does not change the number of symbols in an encoded word. -/
@[simp] theorem length_mapSymbols (encoding : Encoding α Γ) (rename : Γ ≃ Δ) (value : α) :
    ((encoding.mapSymbols rename).encode value).length = (encoding.encode value).length := by
  simp [mapSymbols]

/-- This decoder accepts only words that the encoder itself produces. -/
def strict (encoding : Encoding α Γ) [DecidableEq Γ] : Encoding α Γ where
  encode := encoding.encode
  decode word := do
    let value ← encoding.decode word
    if encoding.encode value = word then some value else none
  decode_encode value := by simp

/-- Successful strict decoding identifies the entire supplied word with the encoded value. -/
@[simp] theorem decode_strict_eq_some_iff (encoding : Encoding α Γ) [DecidableEq Γ]
    {word : List Γ} {value : α} :
    encoding.strict.decode word = some value ↔ word = encoding.encode value := by
  constructor
  · intro h
    cases hdecode : encoding.decode word with
    | none => simp [strict, hdecode] at h
    | some decoded =>
      simp only [strict, hdecode] at h
      change (if encoding.encode decoded = word then some decoded else none) = some value at h
      split at h
      · cases Option.some.inj h
        exact ‹encoding.encode value = word›.symm
      · cases h
  · rintro rfl
    exact encoding.strict.decode_encode value

/-- An equivalence lets an encoding represent the same data using another type. -/
def ofEquiv (encoding : Encoding α Γ) (equiv : β ≃ α) : Encoding β Γ where
  encode value := encoding.encode (equiv value)
  decode word := (encoding.decode word).map equiv.symm
  decode_encode value := by simp

/-- Successful decoding across an equivalence recovers the corresponding original value. -/
theorem decode_ofEquiv_eq_some_iff (encoding : Encoding α Γ) (equiv : β ≃ α)
    {word : List Γ} {value : β} :
    (encoding.ofEquiv equiv).decode word = some value ↔
      encoding.decode word = some (equiv value) := by
  cases h : encoding.decode word <;> simp [ofEquiv, h, Equiv.symm_apply_eq]

/-- The decoder accepts a value only when it satisfies the specified condition. -/
def subtype (encoding : Encoding α Γ) (condition : α → Prop) [DecidablePred condition] :
    Encoding {value // condition value} Γ where
  encode value := encoding.encode value.val
  decode word := do
    let value ← encoding.decode word
    if h : condition value then some ⟨value, h⟩ else none
  decode_encode value := by simp [value.property]

/-- The first encoding produces a word, and the second encoding represents that whole word. -/
def comp (first : Encoding α Γ) (second : Encoding (List Γ) Δ) : Encoding α Δ where
  encode a := second.encode (first.encode a)
  decode word := match second.decode word with
    | none => none
    | some intermediate => first.decode intermediate
  decode_encode a := by simp

/-- Successful decoding through a composition supplies a word decoded by each encoding. -/
theorem decode_comp_eq_some_iff (first : Encoding α Γ) (second : Encoding (List Γ) Δ)
    {word : List Δ} {value : α} :
    (first.comp second).decode word = some value ↔
      ∃ intermediate, second.decode word = some intermediate ∧
        first.decode intermediate = some value := by
  cases h : second.decode word <;> simp [comp, h]

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

/-- Successful decoding removes only the alphabet tags and recovers every symbol of the word. -/
theorem decode_words_eq_some_iff {word : List (Extended Symbol markers)} {value : List Symbol} :
    (words Symbol markers).decode word = some value ↔ word = value.map Sum.inl := by
  constructor
  · intro h
    induction word generalizing value with
    | nil =>
      simp [words] at h
      subst value
      rfl
    | cons symbol word ih =>
      cases symbol with
      | inr marker => simp [words] at h
      | inl symbol =>
        cases htail : word.mapM Sum.getLeft? with
        | none => simp [words, htail] at h
        | some tail =>
          have heq : symbol :: tail = value := by simpa [words, htail] using h
          subst value
          simp [ih htail]
  · rintro rfl
    exact (words Symbol markers).decode_encode value

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
