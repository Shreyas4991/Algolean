/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Encoding

/-!
# Storing two values with one separator

This file encodes a pair when both parts already use the same alphabet. One fresh symbol
separates their words, so the boundary is unambiguous even when either word is empty.
Decoding rejects a missing separator, another separator in the second part, or a part that
its own decoder rejects.

Mathlib's [encodingProd](##Computability.encodingProd) instead allows two different alphabets
and tags every symbol according to its source. The format here preserves a shared alphabet
and adds one separator cell.

## Main definitions and results

* [readWord](##Algolean.Algorithms.Alphabet.readWord) reads up to the first added marker.
* [Encoding.pair](##Computability.Encoding.pair) stores two encoded words with one separator.
* [length_pair](##Computability.Encoding.length_pair) adds their lengths and one separator cell.
-/

@[expose] public section

namespace Algolean.Algorithms.Alphabet

/-- Reading stops at the first marker and returns that marker and the remaining word, if any. -/
def readWord : List (Extended Symbol markers) →
    List Symbol × Option (Fin markers × List (Extended Symbol markers))
  | [] => ([], none)
  | .inl symbol :: rest =>
    let (word, ending) := readWord rest
    (symbol :: word, ending)
  | .inr marker :: rest => ([], some (marker, rest))

/-- Reading a word followed by a marker recovers the word and everything after that marker. -/
@[simp] theorem readWord_append_marker (word : List Symbol) (marker : Fin markers)
    (rest : List (Extended Symbol markers)) :
    readWord (word.map Sum.inl ++ .inr marker :: rest) = (word, some (marker, rest)) := by
  induction word <;> simp_all [readWord]

end Algolean.Algorithms.Alphabet

namespace Computability.Encoding

variable {α : Type u} {β : Type v} {Γ : Type w} {Δ : Type x}

open Algolean.Algorithms.Alphabet

/-- The two words use the same alphabet and are separated by one added symbol. -/
def pair (first : Encoding α Γ) (second : Encoding β Γ) : Encoding (α × β) (Extended Γ 1) where
  encode value :=
    (first.encode value.1).map .inl ++ .inr 0 :: (words Γ 1).encode (second.encode value.2)
  decode word :=
    let (firstWord, ending) := readWord word
    match ending with
    | none => none
    | some (_, rest) =>
      match first.decode firstWord, (words Γ 1).decode rest with
      | some a, some secondWord =>
        match second.decode secondWord with
        | none => none
        | some b => some (a, b)
      | _, _ => none
  decode_encode value := by
    simp only [readWord_append_marker, Encoding.decode_encode]

/-- The encoded pair has the two component lengths plus one separator cell. -/
@[simp] theorem length_pair (first : Encoding α Γ) (second : Encoding β Γ) (value : α × β) :
    ((first.pair second).encode value).length =
      (first.encode value.1).length + (second.encode value.2).length + 1 := by
  simp [pair]
  omega

end Computability.Encoding
