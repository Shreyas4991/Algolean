/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Encoding

/-!
# Storing lists with two markers

This file encodes a list using an existing encoding for each entry. Marker zero ends each
entry, and marker one ends the whole list. An empty list contains just the end marker; a list
with one empty encoded entry contains both markers. This keeps those cases distinct.

The decoder rejects unfinished entries, a missing end marker, and symbols after the end marker.
Nested lists use the same construction again, adding a separate pair of markers at each level.
The proof of the encoded length counts the original words and all added markers.

## Main definitions and results

* [Encoding.list](##Computability.Encoding.list) encodes lists over an alphabet with two markers.
* [length_list](##Computability.Encoding.length_list) counts every encoded entry and marker.
-/

@[expose] public section

namespace Computability.Encoding

variable {α : Type u} {β : Type v} {Γ : Type w} {Δ : Type x}

open Algolean.Algorithms.Alphabet

namespace Internal

/-- The decoder collects an entry in reverse order until its separator or the list end appears. -/
def decodeEntries (entry : Encoding α Γ) :
    List (Extended Γ 2) → List Γ → Option (List α)
  | [], _ => none
  | .inl symbol :: rest, reversed => decodeEntries entry rest (symbol :: reversed)
  | .inr marker :: rest, reversed =>
    if marker = 0 then do
      let a ← entry.decode reversed.reverse
      let remaining ← decodeEntries entry rest []
      pure (a :: remaining)
    else if reversed.isEmpty && rest.isEmpty then some [] else none

private theorem decodeEntries_append (entry : Encoding α Γ) (word : List Γ)
    (rest : List (Extended Γ 2)) (reversed : List Γ) :
    decodeEntries entry (word.map Sum.inl ++ rest) reversed =
      decodeEntries entry rest (word.reverse ++ reversed) := by
  induction word generalizing reversed with
  | nil => simp
  | cons symbol word ih => simp [decodeEntries, ih, List.reverse_cons, List.append_assoc]

end Internal

open Internal

/-- Each encoded entry ends with marker zero, and the whole list ends with marker one. -/
def list (entry : Encoding α Γ) : Encoding (List α) (Extended Γ 2) where
  encode values := values.flatMap (fun a => (entry.encode a).map .inl ++ [.inr 0]) ++ [.inr 1]
  decode word := decodeEntries entry word []
  decode_encode values := by
    induction values with
    | nil => simp [decodeEntries]
    | cons a values ih =>
      simp only [List.flatMap_cons, List.append_assoc]
      rw [decodeEntries_append]
      simp [decodeEntries, ih]

/-- The list length is the sum of entry lengths, one marker per entry, and one end marker. -/
@[simp] theorem length_list (entry : Encoding α Γ) (values : List α) :
    (entry.list.encode values).length =
      (values.map (fun a => (entry.encode a).length)).sum + values.length + 1 := by
  induction values with
  | nil => simp [list]
  | cons a values ih =>
    simp only [list, List.flatMap_cons, List.append_assoc, List.length_append,
      List.length_map, List.length_cons, List.length_nil] at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    lia

end Computability.Encoding
