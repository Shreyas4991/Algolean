/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.TMSAT.Encoding

/-!
# The fixed words used to write a TMSAT instance

The instance encoding consists of a fixed machine description, the input symbol codes, an
input ending, and two unary fields separated by a fixed word. This file identifies those
pieces over the chosen alphabet. The equality with `encodingOver` lets the serializer write
these pieces separately while producing exactly the existing encoding.
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
@[simp] private theorem translate_nil : translate (Γ := Γ) [] = [] := by
  unfold translate
  rw [encode_finiteWordsOver]
  rfl

omit [Fintype Γ] in
private theorem translate_flatMap {α : Type} (input : List α) (f : α → List CodeSymbol) :
    translate (Γ := Γ) (input.flatMap f) = input.flatMap (fun a => translate (f a)) := by
  induction input with
  | nil => simp
  | cons a input ih => simp only [List.flatMap_cons, translate_append, ih]

/-- This word stores the fixed verifier description and the separator before the input. -/
noncomputable def header (verifier : SingleTapeTM.Description (TapeSymbol Γ)) : List Γ :=
  translate ((SingleTapeTM.Description.encoding.encode verifier).map tag ++ [.inl (.inr 0)])

/-- This is the fixed nonempty word written for one input symbol. -/
noncomputable def symbolCode (symbol : Γ) : List Γ :=
  translate ((SingleTapeTM.Description.wordSymbolCode symbol).map tag)

/-- This word ends the encoded input and separates it from the two bounds. -/
noncomputable def ending : List Γ :=
  translate [tag SingleTapeTM.Description.wordEnd, .inr 0]

/-- Each unary unit in either bound is represented by this fixed word. -/
noncomputable def unary : List Γ :=
  translate ((SingleTapeTM.Description.bitEncoding.encode [true]).map tag)

/-- This word separates the certificate length from the time bound. -/
noncomputable def separator : List Γ := translate [.inl (.inr 0)]

/-- Every input symbol code has positive length. -/
theorem symbolCode_ne_nil (symbol : Γ) : symbolCode symbol ≠ [] := by
  have hpos := Fintype.card_pos (α := CodeSymbol)
  intro h
  have hlen := congrArg List.length h
  simp only [symbolCode, translate, length_finiteWordsOver, List.length_map,
    SingleTapeTM.Description.wordSymbolCode, List.length_append, List.length_map,
    List.length_singleton, List.length_nil] at hlen
  have : 0 < (((Encoding.ofEncodable Γ).encode symbol).length + 1) *
      Fintype.card CodeSymbol := Nat.mul_pos (by lia) hpos
  lia

private theorem unary_eq_replicate (n : Nat) : unaryEncodeNat n = List.replicate n true := by
  induction n <;> simp_all [unaryEncodeNat, List.replicate_succ]

omit [Fintype Γ] in
private theorem translate_unary (n : Nat) :
    translate (Γ := Γ) ((SingleTapeTM.Description.bitEncoding.encode (unaryEncodeNat n)).map tag) =
      (List.replicate n (unary (Γ := Γ))).flatten := by
  induction n with
  | zero =>
    have hempty : SingleTapeTM.Description.bitEncoding.encode [] = [] := rfl
    simp only [unaryEncodeNat, hempty, List.map_nil, translate_nil,
      List.replicate_zero, List.flatten_nil]
  | succ n ih =>
    have hcons : SingleTapeTM.Description.bitEncoding.encode (true :: unaryEncodeNat n) =
        SingleTapeTM.Description.bitEncoding.encode [true] ++
          SingleTapeTM.Description.bitEncoding.encode (unaryEncodeNat n) := by
      simp [SingleTapeTM.Description.bitEncoding, Encoding.comp, words, encodingList]
    simp only [unaryEncodeNat, hcons, List.map_append, translate_append, ih,
      List.replicate_succ, List.flatten_cons, unary]

/--
The canonical instance encoding is exactly the fixed header, the input codes, the input ending,
the unary certificate length, the separator, and the unary time bound, in that order.
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
