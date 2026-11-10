/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Encodings.TMSAT

/-!
# The fixed words used to write a TMSAT instance

The instance encoding contains the verifier description, the encoded input, the certificate
length, and the time bound. Fixed words separate these four parts. Each input symbol is
replaced by a fixed word. Each numeric bound is written by repeating another fixed word.

This file identifies those words and proves that writing the parts in this order gives exactly
the result of `encodingOver`. The machine can therefore write the parts separately and still
produce the required representation of the instance.
-/

public section

namespace Algolean.Problems.TMSAT.Serialization

open Computability Cslib.Turing Algorithms.Alphabet

variable {Γ : Type} [Fintype Γ] [Nontrivial Γ]

private noncomputable abbrev inputEncodable : Encodable Γ :=
  Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)

attribute [local instance] inputEncodable

private def tag (symbol : SingleTapeTM.Description.CodeSymbol) : CodeSymbol := .inl (.inl symbol)

private noncomputable def translate (word : List CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode word

omit [Fintype Γ] in
private theorem translate_append (first second : List CodeSymbol) :
    translate (Γ := Γ) (first ++ second) = translate first ++ translate second :=
  encode_finiteWordsOver_append first second

omit [Fintype Γ] in
private theorem translate_flatMap {α : Type} (input : List α) (f : α → List CodeSymbol) :
    translate (Γ := Γ) (input.flatMap f) = input.flatMap (fun a => translate (f a)) :=
  encode_finiteWordsOver_flatMap input f

/-- This word stores the fixed verifier description and the separator before the input. -/
noncomputable def header (verifier : SingleTapeTM.Description (TapeSymbol Γ)) : List Γ :=
  translate ((SingleTapeTM.Description.encoding.encode verifier).map tag ++ [.inl (.inr 0)])

/-- This is the fixed nonempty word written for one input symbol. -/
noncomputable def symbolCode (symbol : Γ) : List Γ :=
  translate ((SingleTapeTM.Description.wordSymbolCode symbol).map tag)

/-- This word ends the encoded input and separates it from the two bounds. -/
noncomputable def ending : List Γ :=
  translate [tag SingleTapeTM.Description.wordEnd, .inr 0]

/--
This is the fixed word repeated to write either numeric bound. A bound of `k` is written as
exactly `k` copies of this word.
-/
noncomputable def unary : List Γ :=
  translate ((SingleTapeTM.Description.bitEncoding.encode [true]).map tag)

/-- This word separates the certificate length from the time bound. -/
noncomputable def separator : List Γ := translate [.inl (.inr 0)]

/-- Every input symbol code has positive length. -/
theorem symbolCode_ne_nil (symbol : Γ) : symbolCode symbol ≠ [] := by
  apply List.ne_nil_of_length_pos
  simp only [symbolCode, translate, length_finiteWordsOver, List.length_map]
  exact Nat.mul_pos
    (List.length_pos_of_ne_nil (SingleTapeTM.Description.wordSymbolCode_ne_nil symbol))
    Fintype.card_pos

omit [Fintype Γ] in
private theorem translate_unary (n : Nat) :
    translate (Γ := Γ) ((SingleTapeTM.Description.bitEncoding.encode (unaryEncodeNat n)).map tag) =
      (List.replicate n (unary (Γ := Γ))).flatten := by
  change translate
    ((SingleTapeTM.Description.bitEncoding.encode (unaryEncoding.encode n)).map tag) = _
  rw [encode_unaryEncoding, SingleTapeTM.Description.encode_bitEncoding]
  simp only [List.map_replicate, translate]
  rw [encode_finiteWordsOver_replicate]
  rfl

/--
The word produced by `encodingOver` contains the fixed verifier description, the input symbol
codes, the input ending, the certificate length, the separator, and the time bound, in that
order. Each bound is written as the specified number of copies of one fixed word.
-/
theorem encode_instance (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (input : List Γ) (m t : Nat) :
    encodingOver.encode (⟨verifier, input, m, t⟩ : Instance Γ) =
      header verifier ++ input.flatMap symbolCode ++ ending ++
        (List.replicate m (unary (Γ := Γ))).flatten ++ separator ++
          (List.replicate t (unary (Γ := Γ))).flatten := by
  have hraw : encoding.encode (⟨verifier, input, m, t⟩ : Instance Γ) =
      (SingleTapeTM.Description.encoding.encode verifier).map tag ++ [.inl (.inr 0)] ++
        input.flatMap (fun symbol =>
          (SingleTapeTM.Description.wordSymbolCode symbol).map tag) ++
        [tag SingleTapeTM.Description.wordEnd, .inr 0] ++
        (SingleTapeTM.Description.bitEncoding.encode (unaryEncodeNat m)).map tag ++
        [.inl (.inr 0)] ++
        (SingleTapeTM.Description.bitEncoding.encode (unaryEncodeNat t)).map tag := by
    dsimp only [tag]
    simp [encoding, Encoding.ofEquiv, Instance.equiv, payloadEncoding, boundsEncoding,
      Encoding.pair, Encoding.comp, words, unaryEncoding,
      SingleTapeTM.Description.encode_wordEncoding, List.map_flatMap, List.map_map,
      List.map_append, List.append_assoc, Function.comp_def]
    rfl
  change translate (encoding.encode (⟨verifier, input, m, t⟩ : Instance Γ)) = _
  rw [hraw]
  simp only [header, ending, separator, translate_append, translate_flatMap,
    translate_unary, List.append_assoc]
  rfl

end Algolean.Problems.TMSAT.Serialization
