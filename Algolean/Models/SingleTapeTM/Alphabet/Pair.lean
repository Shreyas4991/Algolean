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
* `decode_pair_eq_some_iff` recovers the two fields and separator from any successful decoding.
* `Encoding.sigma` lets the first decoded value determine the second value's type and encoding.
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

/-- The word returned by the reader and any remaining marker and suffix reconstruct the input. -/
theorem readWord_reconstruct (word : List (Extended Symbol markers)) :
    (readWord word).1.map Sum.inl ++
      (match (readWord word).2 with
      | none => []
      | some (marker, rest) => .inr marker :: rest) = word := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
    cases symbol with
    | inr marker => rfl
    | inl symbol =>
      cases hread : readWord rest with
      | mk first ending =>
        simpa [readWord, hread] using congrArg (List.cons (.inl symbol)) ih

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

/-- Successful pair decoding splits the entire word into two decoded fields and one separator. -/
theorem decode_pair_eq_some_iff (first : Encoding α Γ) (second : Encoding β Γ)
    {word : List (Extended Γ 1)} {a : α} {b : β} :
    (first.pair second).decode word = some (a, b) ↔
      ∃ left right, word = left.map Sum.inl ++ .inr 0 :: right.map Sum.inl ∧
        first.decode left = some a ∧ second.decode right = some b := by
  constructor
  · intro h
    cases hread : readWord word with
    | mk left ending =>
      cases ending with
      | none => simp [pair, hread] at h
      | some ending =>
        obtain ⟨marker, rest⟩ := ending
        have hmarker : marker = 0 := Subsingleton.elim _ _
        subst marker
        cases hfirst : first.decode left with
        | none => simp [pair, hread, hfirst] at h
        | some a' =>
          cases hrest : (words Γ 1).decode rest with
          | none => simp [pair, hread, hrest] at h
          | some right =>
            cases hsecond : second.decode right with
            | none => simp [pair, hread, hfirst, hrest, hsecond] at h
            | some b' =>
              have heq : (a', b') = (a, b) := by
                simpa [pair, hread, hfirst, hrest, hsecond] using h
              cases heq
              have hword := readWord_reconstruct word
              rw [hread, decode_words_eq_some_iff.mp hrest] at hword
              exact ⟨left, right, hword.symm, hfirst, hsecond⟩
  · rintro ⟨left, right, rfl, hfirst, hsecond⟩
    simp only [pair, readWord_append_marker, hfirst]
    rw [show (words Γ 1).decode (right.map Sum.inl) = some right from
      (words Γ 1).decode_encode right]
    simp only [hsecond]

/-- The encoded pair has the two component lengths plus one separator cell. -/
@[simp] theorem length_pair (first : Encoding α Γ) (second : Encoding β Γ) (value : α × β) :
    ((first.pair second).encode value).length =
      (first.encode value.1).length + (second.encode value.2).length + 1 := by
  simp [pair]
  omega

/-- The first decoded value determines the type and encoding of the second value. -/
def sigma {family : α → Type v} (first : Encoding α Γ)
    (second : ∀ value, Encoding (family value) Γ) : Encoding (Sigma family) (Extended Γ 1) where
  encode value :=
    (first.encode value.1).map .inl ++
      .inr 0 :: (words Γ 1).encode ((second value.1).encode value.2)
  decode word :=
    let (firstWord, ending) := readWord word
    match ending with
    | none => none
    | some (_, rest) =>
      match first.decode firstWord, (words Γ 1).decode rest with
      | some value, some secondWord =>
        ((second value).decode secondWord).map (Sigma.mk value)
      | _, _ => none
  decode_encode value := by simp [readWord_append_marker]

/-- A dependent pair uses the two component lengths and one separator. -/
@[simp] theorem length_sigma {family : α → Type v} (first : Encoding α Γ)
    (second : ∀ value, Encoding (family value) Γ) (value : Sigma family) :
    ((first.sigma second).encode value).length =
      (first.encode value.1).length + ((second value.1).encode value.2).length + 1 := by
  simp [sigma]
  lia

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

/--
Decoding two words separated by the added marker recovers both words, including when either is
empty. The symbols of each word carry `Sum.inl` to distinguish them from the marker.
-/
@[simp] theorem wordPair_decode (first second : List Symbol) :
    (wordPair Symbol).decode (first.map Sum.inl ++ .inr 0 :: second.map Sum.inl) =
      some (first, second) := by
  exact (wordPair Symbol).decode_encode (first, second)

end Algolean.Algorithms.Alphabet
