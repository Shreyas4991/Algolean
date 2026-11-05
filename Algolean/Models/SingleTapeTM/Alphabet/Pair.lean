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

/--
This pure Lean function returns the ordinary symbols before the first added marker. It uses
`readWord`, and returns the entire word if no marker occurs.
-/
def firstWord (word : List (Extended Symbol markers)) : List Symbol := (readWord word).1

/--
This pure Lean function returns the suffix after the first added marker. It uses the ending
returned by `readWord`, and returns an empty list if no marker occurs.
-/
def afterMarker (word : List (Extended Symbol markers)) : List (Extended Symbol markers) :=
  match (readWord word).2 with
  | none => []
  | some (_, rest) => rest

@[simp] theorem firstWord_nil : firstWord ([] : List (Extended Symbol markers)) = [] := rfl

@[simp] theorem firstWord_symbol (symbol : Symbol) (rest : List (Extended Symbol markers)) :
    firstWord (.inl symbol :: rest) = symbol :: firstWord rest := rfl

@[simp] theorem firstWord_marker (marker : Fin markers) (rest : List (Extended Symbol markers)) :
    firstWord (.inr marker :: rest) = [] := rfl

@[simp] theorem afterMarker_nil : afterMarker ([] : List (Extended Symbol markers)) = [] := rfl

@[simp] theorem afterMarker_symbol (symbol : Symbol) (rest : List (Extended Symbol markers)) :
    afterMarker (.inl symbol :: rest) = afterMarker rest := rfl

@[simp] theorem afterMarker_marker (marker : Fin markers)
    (rest : List (Extended Symbol markers)) : afterMarker (.inr marker :: rest) = rest := rfl

@[simp] theorem firstWord_append_marker (word : List Symbol) (marker : Fin markers)
    (rest : List (Extended Symbol markers)) :
    firstWord (word.map Sum.inl ++ .inr marker :: rest) = word := by
  simp [firstWord]

@[simp] theorem afterMarker_append_marker (word : List Symbol) (marker : Fin markers)
    (rest : List (Extended Symbol markers)) :
    afterMarker (word.map Sum.inl ++ .inr marker :: rest) = rest := by
  simp [afterMarker]

/--
The prefix before the first marker and the suffix after it together occupy at most the original
word's length. The marker, when present, accounts for the omitted cell.
-/
theorem lengths_firstWord_afterMarker_le (word : List (Extended Symbol markers)) :
    (firstWord word).length + (afterMarker word).length ≤ word.length := by
  induction word with
  | nil => simp
  | cons symbol rest ih => cases symbol <;> simp_all; omega

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

namespace Algolean.Algorithms.Alphabet

/--
This encoding stores two words over the same alphabet with one fresh separator between them.
It specializes `Encoding.pair` to Mathlib's identity encoding of words, so empty words and the
boundary between input and certificate remain unambiguous.
-/
def wordPair (Symbol : Type) :
    Computability.Encoding (List Symbol × List Symbol) (Extended Symbol 1) :=
  (Computability.encodingList Symbol).pair (Computability.encodingList Symbol)

@[simp] theorem wordPair_encode (first second : List Symbol) :
    (wordPair Symbol).encode (first, second) =
      first.map Sum.inl ++ .inr 0 :: second.map Sum.inl := rfl

end Algolean.Algorithms.Alphabet
