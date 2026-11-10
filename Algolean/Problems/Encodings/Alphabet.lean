/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Encodings.Basic
public import Algolean.Models.SingleTapeTM.Alphabet.Block

/-!
# Representing a problem over another alphabet

* `Encoding.over` replaces each symbol of a finite alphabet by a fixed-length word over `Γ`.
* Two distinct symbols of `Γ` are chosen once for the whole encoding.
* Decoding first recovers the original symbols, then uses the original problem's decoder.
* The word length grows by the original alphabet's size. Changing alphabets preserves answers,
  including rejection of words that the original decoder rejects.

The target alphabet needs only two distinct symbols. It need not be finite or have a numeric
encoding. These definitions describe representations; they do not assert Turing machine time
bounds for the conversion.
-/

@[expose] public section

namespace Computability.Encoding

open Algolean.Algorithms.Alphabet

variable {α : Type u} {Symbol Γ : Type} [Fintype Symbol] [Nonempty Symbol] [Nontrivial Γ]

/--
This reuses an encoding over `Γ` by replacing every original symbol by a fixed-length word.
The word length is the original alphabet's size. Two distinct target symbols and the numbering
of the original symbols are chosen once and do not depend on the encoded value.
-/
noncomputable def over (encoding : Encoding α Symbol) : Encoding α Γ :=
  encoding.comp (finiteWordsOver Symbol Γ)

/-- Changing alphabets multiplies the encoded length by the original alphabet's size. -/
@[simp] theorem length_over (encoding : Encoding α Symbol) (value : α) :
    ((encoding.over (Γ := Γ)).encode value).length =
      (encoding.encode value).length * Fintype.card Symbol := by
  simp [over, comp]

/--
Decoding succeeds exactly when the entire word represents an original word that the original
decoder accepts. Incomplete and unrecognized symbol encodings are rejected.
-/
theorem decode_over_eq_some_iff (encoding : Encoding α Symbol) {word : List Γ} {value : α} :
    encoding.over.decode word = some value ↔
      ∃ original, word = (finiteWordsOver Symbol Γ).encode original ∧
        encoding.decode original = some value := by
  simp only [over, decode_comp_eq_some_iff, decode_finiteWordsOver_eq_some_iff]

/-- Changing the alphabet of a word preserves its decoding result, including failure. -/
@[simp] theorem decode_over_encode_word (encoding : Encoding α Symbol) (word : List Symbol) :
    encoding.over.decode ((finiteWordsOver Symbol Γ).encode word) = encoding.decode word := by
  simp [over, comp]

end Computability.Encoding

namespace Algolean.Problems

open Computability Algorithms.Alphabet

/-- Changing a word's alphabet preserves whether it belongs to the encoded problem. -/
@[simp] theorem mem_encodedLanguage_over_encode_word {α : Type u} {Symbol Γ : Type}
    [Fintype Symbol] [Nonempty Symbol] [Nontrivial Γ] (problem : DecisionProblem α)
    (encoding : Encoding α Symbol) (word : List Symbol) :
    (finiteWordsOver Symbol Γ).encode word ∈ encodedLanguage problem encoding.over ↔
      word ∈ encodedLanguage problem encoding := by
  simp [Encoding.over, encodedLanguage_comp]

end Algolean.Problems
