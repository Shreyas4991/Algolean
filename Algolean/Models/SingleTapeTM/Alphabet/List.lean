/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Encoding
public import Mathlib.Data.Vector.Basic

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
* `Encoding.finFunction` stores a finite table in index order and checks its size when decoding.
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

/--
Successful list decoding requires one ending for each entry and one ending for the whole list.
Thus the number of decoded entries plus one cannot exceed the supplied word's length, even
when an entry's decoder accepts more than one spelling of the same value.
-/
theorem length_le_of_decode_list (entry : Encoding α Γ)
    {word : List (Extended Γ 2)} {values : List α}
    (h : entry.list.decode word = some values) : values.length + 1 ≤ word.length := by
  have bound (word : List (Extended Γ 2)) (reversed : List Γ) (values : List α)
      (h : decodeEntries entry word reversed = some values) :
      values.length + 1 ≤ word.length := by
    induction word generalizing reversed values with
    | nil => simp [decodeEntries] at h
    | cons symbol rest ih =>
      cases symbol with
      | inl symbol =>
        have hb := ih (symbol :: reversed) values h
        simp only [List.length_cons]
        lia
      | inr marker =>
        by_cases hm : marker = 0
        · cases hd : entry.decode reversed.reverse with
          | none => simp [decodeEntries, hm, hd] at h
          | some value =>
            cases hr : decodeEntries entry rest [] with
            | none => simp [decodeEntries, hm, hd, hr] at h
            | some tail =>
              have heq : value :: tail = values := by
                simpa [decodeEntries, hm, hd, hr] using h
              subst values
              have hb := ih [] tail hr
              simp only [List.length_cons]
              lia
        · have heq : (reversed = [] ∧ rest = []) ∧ values = [] := by
            simpa [decodeEntries, hm] using h.symm
          simp [heq.2]
  exact bound word [] values h

/-- A finite function is stored as its values in index order; other list lengths are rejected. -/
def finFunction (entry : Encoding α Γ) (size : ℕ) :
    Encoding (Fin size → α) (Extended Γ 2) :=
  (entry.list.subtype (fun values => values.length = size)).ofEquiv
    (Equiv.vectorEquivFin α size).symm

/-- A finite table uses one entry marker per value and one final marker. -/
@[simp] theorem length_finFunction (entry : Encoding α Γ) (size : ℕ) (table : Fin size → α) :
    ((entry.finFunction size).encode table).length =
      ((List.ofFn table).map (fun value => (entry.encode value).length)).sum + size + 1 := by
  change (entry.list.encode (List.Vector.ofFn table).toList).length = _
  simp

end Computability.Encoding
