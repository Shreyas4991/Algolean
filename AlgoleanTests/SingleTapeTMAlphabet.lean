/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Algolean.Models.SingleTapeTM.Alphabet.List

/-!
# Checking alphabet extensions and structured encodings

These examples check the distinction between a blank and an added marker, the boundaries of
empty encoded values, and rejection of malformed input. They also combine existing numeric
encodings and the structural list encoding without defining another encoding structure.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMAlphabet

open Algolean.Algorithms.Alphabet Computability

-- A Boolean alphabet with one start marker has four tape-cell values, including blank.
example : Fintype.card (Option (Extended Bool 1)) = 4 := by decide

-- Two added markers remain separate from both Boolean symbols and the blank.
example : Fintype.card (Option (Extended Bool 2)) = 5 := by decide

example : (none : Option (Extended Bool 1)) ≠ some (.inr 0) := by simp

-- The list decoder must preserve an empty first word and a nonempty second word.
example : ((encodingList Bool).list).decode
    [.inr 0, .inl true, .inl false, .inr 0, .inr 1] = some [[], [true, false]] := by
  decide

-- The empty list and a list containing an empty word have different representations.
example : ((encodingList Bool).list).encode [] = [.inr 1] := rfl

example : ((encodingList Bool).list).encode [[]] = [.inr 0, .inr 1] := rfl

-- A missing entry separator, a missing end marker, and trailing data are rejected.
example : ((encodingList Bool).list).decode [.inl true, .inr 1] = none := by decide

example : ((encodingList Bool).list).decode [.inl true, .inr 0] = none := by decide

example : ((encodingList Bool).list).decode [.inr 1, .inl false] = none := by decide

-- A pair can have an empty part, but it must have exactly one separator.
example : ((encodingList Bool).pair (encodingList Bool)).decode
    [.inr 0, .inl true] = some ([], [true]) := by decide

example : ((encodingList Bool).pair (encodingList Bool)).decode
    [.inl true, .inl false] = none := by decide

example : ((encodingList Bool).pair (encodingList Bool)).decode
    [.inr 0, .inr 0] = none := by decide

-- The leading marker distinguishes the same word used for either alternative.
example : ((encodingList Bool).sum (encodingList Bool)).decode
    [.inr 0, .inl true] = some (.inl [true]) := by decide

example : ((encodingList Bool).sum (encodingList Bool)).decode
    [.inr 1, .inl true] = some (.inr [true]) := by decide

-- Each level of a nested list has its own distinct markers.
example : ((encodingList Bool).list.list).decode
    [.inl (.inr 1), .inr 0, .inl (.inr 0), .inl (.inr 1), .inr 0, .inr 1] =
      some [[], [[]]] := by decide

-- Mathlib's existing instances provide numeric encodings for pairs and lists.
example : (Encoding.ofEncodable (List (ℕ × Bool))).decode
    ((Encoding.ofEncodable (List (ℕ × Bool))).encode [(0, false), (5, true)]) =
      some [(0, false), (5, true)] := by decide +kernel

-- An existing binary encoding can be included in an alphabet with a separator.
example : ((Encoding.ofEncodable ℕ).comp (words Bool 1)).decode
    [.inl true, .inl false, .inl true] = some 5 := by decide

example : ((Encoding.ofEncodable ℕ).comp (words Bool 1)).decode
    [.inl true, .inr 0] = none := by decide

end AlgoleanTests.SingleTapeTMAlphabet
