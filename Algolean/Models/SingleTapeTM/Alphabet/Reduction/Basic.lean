/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Block

/-!
# Alphabet codes with a separator

`BlockCode Γ Δ width` assigns distinct words of `width` target symbols to source symbols.
One fresh separator follows every payload, so even a zero-width payload occupies one tape
cell. The resulting `Encoding` concatenates these blocks and rejects every word outside its
image, including incomplete blocks and misplaced separators.

This file concerns representations. `Logarithmic` chooses the smallest possible payload
width, and `Machine` supplies the single-tape program that writes the representation.
-/

@[expose] public section

namespace Algolean.Algorithms.Alphabet

/-- An injective assignment of fixed-width payloads, before adding a separator. -/
structure BlockCode (Γ Δ : Type) (width : ℕ) where
  /-- Every source symbol has a different tuple of target symbols. -/
  digits : Γ ↪ (Fin width → Δ)

namespace BlockCode

variable {Γ Δ : Type} {width : ℕ}

/-- The single fresh symbol that terminates each payload. Tape blank remains separate. -/
def separator (Δ : Type) : Extended Δ 1 := .inr 0

/-- A source symbol is written as its payload followed by one separator. -/
def encodeSymbol (code : BlockCode Γ Δ width) (symbol : Γ) : List (Extended Δ 1) :=
  (List.ofFn (code.digits symbol)).map Sum.inl ++ [separator Δ]

/-- Each symbol uses exactly the payload width plus one tape character. -/
@[simp] theorem length_encodeSymbol (code : BlockCode Γ Δ width) (symbol : Γ) :
    (code.encodeSymbol symbol).length = width + 1 := by
  simp [encodeSymbol]

/-- The separator keeps code words nonempty even when the payload width is zero. -/
theorem encodeSymbol_ne_nil (code : BlockCode Γ Δ width) (symbol : Γ) :
    code.encodeSymbol symbol ≠ [] := by
  intro h
  have := congrArg List.length h
  simp at this

/-- Adding tags and a separator preserves the injectivity of the payload assignment. -/
theorem encodeSymbol_injective (code : BlockCode Γ Δ width) :
    Function.Injective code.encodeSymbol := by
  intro first second h
  apply code.digits.injective
  apply List.ofFn_injective
  apply List.map_injective_iff.mpr Sum.inl_injective
  exact List.append_cancel_right h

/-- The symbol decoder accepts exactly the chosen complete code words. -/
noncomputable def symbolEncoding (code : BlockCode Γ Δ width) :
    Computability.Encoding Γ (Extended Δ 1) where
  encode := code.encodeSymbol
  decode := Function.partialInv code.encodeSymbol
  decode_encode := Function.partialInv_left code.encodeSymbol_injective

/-- Symbol decoding rejects every word outside the image of the code. -/
theorem decode_symbolEncoding_eq_some_iff (code : BlockCode Γ Δ width)
    {word : List (Extended Δ 1)} {symbol : Γ} :
    code.symbolEncoding.decode word = some symbol ↔ word = code.encodeSymbol symbol := by
  exact code.encodeSymbol_injective.isPartialInv _ _ |>.trans eq_comm

/-- A source word is represented by concatenating its separated symbol blocks. -/
noncomputable def encoding (code : BlockCode Γ Δ width) :
    Computability.Encoding (List Γ) (Extended Δ 1) :=
  blockWords code.symbolEncoding (width + 1) (by omega) code.length_encodeSymbol

/-- Encoding a word applies the same fixed replacement to every source symbol. -/
theorem encode_eq_flatMap (code : BlockCode Γ Δ width) (word : List Γ) :
    code.encoding.encode word = word.flatMap code.encodeSymbol := by
  exact encode_blockWords _ _ _ _ _

/-- The output length includes exactly one separator per source symbol. -/
@[simp] theorem length_encode (code : BlockCode Γ Δ width) (word : List Γ) :
    (code.encoding.encode word).length = word.length * (width + 1) :=
  length_blockWords _ _ _ _ _

/-- Decoding accepts exactly complete encodings, with no trailing or malformed data. -/
theorem decode_eq_some_iff (code : BlockCode Γ Δ width)
    {word : List (Extended Δ 1)} {decoded : List Γ} :
    code.encoding.decode word = some decoded ↔ word = code.encoding.encode decoded :=
  decode_blockWords_eq_some_iff _ _ _ _
    (fun h => code.decode_symbolEncoding_eq_some_iff.mp h)

/-- Encoding respects concatenation and therefore the source symbol order. -/
@[simp] theorem encode_append (code : BlockCode Γ Δ width) (first second : List Γ) :
    code.encoding.encode (first ++ second) =
      code.encoding.encode first ++ code.encoding.encode second := by
  simp only [encode_eq_flatMap, List.flatMap_append]

/-- Successful decoding cannot increase word length. -/
theorem length_le_of_decode (code : BlockCode Γ Δ width)
    {word : List (Extended Δ 1)} {decoded : List Γ}
    (h : code.encoding.decode word = some decoded) : decoded.length ≤ word.length :=
  length_le_of_decode_blockWords _ _ _ _ h

end BlockCode

end Algolean.Algorithms.Alphabet
