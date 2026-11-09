/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.TMSAT.Basic
public import Algolean.Problems.Encoding
public import Algolean.Models.SingleTapeTM.DescriptionEncoding

/-!
# Encoding Turing machine satisfiability

* `encoding` stores the machine, input, certificate length, and time bound in that order.
* Both the certificate length and time bound are written in unary.
* `language` contains the words that decode to satisfiable instances.
* Encoding an instance preserves its answer, and failed decoding gives a no answer.
* Successfully decoded certificate lengths and time bounds cannot exceed the supplied word's length.

The unary fields have exactly the specified lengths. Separators preserve the boundaries between
the four fields, and the machine description includes its complete finite transition table.

The encoder chooses one word for each instance. The decoder can also accept other words that
describe the same instance. This lets us reuse the existing number decoders and follows the
use of multiple machine descriptions in [Barak's lecture notes][barak2006]. All such words give
the same yes or no answer. Their lengths can differ, so the size proofs use the length of the
word supplied to the decoder and cover every word it accepts.

[barak2006]: https://www.cs.princeton.edu/courses/archive/spr06/cos522/lec2.pdf
-/

@[expose] public section

namespace Algolean.Problems.TMSAT

open Computability Cslib.Turing Algorithms.Alphabet

/-- A natural number is written as true bits; the decoder rejects any false bit. -/
def unaryEncoding : Encoding ℕ Bool where
  encode := unaryEncodeNat
  decode word := if word.all id then some word.length else none
  decode_encode time := by
    induction time with
    | zero => rfl
    | succ time ih => simpa [unaryEncodeNat] using congrArg (Option.map Nat.succ) ih

/-- The unary representation has exactly the specified length. -/
@[simp] theorem length_unaryEncoding (value : ℕ) : (unaryEncoding.encode value).length = value := by
  induction value <;> simp_all [unaryEncoding, unaryEncodeNat]

/-- A successfully decoded unary value equals the number of bits in the supplied word. -/
theorem unary_eq_length_of_decode {word : List Bool} {value : ℕ}
    (h : unaryEncoding.decode word = some value) : value = word.length := by
  simp only [unaryEncoding] at h
  split at h <;> simp_all

/-- This alphabet separates the fields within the machine-input pair and the pair of bounds. -/
abbrev PayloadSymbol := Extended SingleTapeTM.Description.CodeSymbol 1

/-- This alphabet separates the machine-input pair from the two unary bounds. -/
abbrev CodeSymbol := Extended PayloadSymbol 1

/-- The payload stores the complete verifier description and then the input word. -/
def payloadEncoding : Encoding (SingleTapeTM.Description TapeSymbol × List Bool) PayloadSymbol :=
  SingleTapeTM.Description.encoding.pair SingleTapeTM.Description.bitEncoding

/-- The certificate length and time bound are stored independently, with one separator. -/
def boundsEncoding : Encoding (ℕ × ℕ) PayloadSymbol :=
  (unaryEncoding.comp SingleTapeTM.Description.bitEncoding).pair
    (unaryEncoding.comp SingleTapeTM.Description.bitEncoding)

/-- The field order is the verifier, input, certificate length, and time bound. -/
def Instance.equiv : Instance ≃
    (SingleTapeTM.Description TapeSymbol × List Bool) × (ℕ × ℕ) where
  toFun problem := ((problem.verifier, problem.input), (problem.certificateLength, problem.time))
  invFun problem := ⟨problem.1.1, problem.1.2, problem.2.1, problem.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The certificate length and time are unary, and three separators delimit the fields. -/
def encoding : Encoding Instance CodeSymbol :=
  (payloadEncoding.pair boundsEncoding).ofEquiv Instance.equiv

/-- The length counts the machine code, input, two unary fields, and three separators. -/
@[simp] theorem length_encoding (problem : Instance) :
    (encoding.encode problem).length =
      (SingleTapeTM.Description.encoding.encode problem.verifier).length + problem.input.length +
        problem.certificateLength + problem.time + 3 := by
  simp [encoding, Encoding.ofEquiv, Instance.equiv, payloadEncoding, boundsEncoding, Encoding.comp]
  lia

/--
The decoded input, certificate length, time bound, and three separators fit in the supplied word.
This holds for every successful decoding, including noncanonical machine descriptions.
-/
theorem input_length_add_bounds_le_length_of_decode {word : List CodeSymbol} {problem : Instance}
    (h : encoding.decode word = some problem) :
    problem.input.length + problem.certificateLength + problem.time + 3 ≤ word.length := by
  have hfields := (Encoding.decode_ofEquiv_eq_some_iff _ _).mp h
  change (payloadEncoding.pair boundsEncoding).decode word =
    some ((problem.verifier, problem.input), (problem.certificateLength, problem.time)) at hfields
  obtain ⟨payload, bounds, rfl, hpayload, hbounds⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hfields
  obtain ⟨machine, inputWord, rfl, _, hinput⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hpayload
  obtain ⟨certificateWord, timeWord, rfl, hcertificate, htime⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hbounds
  obtain ⟨certificateBits, hcertificateWord, hcertificate⟩ :=
    (Encoding.decode_comp_eq_some_iff _ _).mp hcertificate
  obtain ⟨timeBits, htimeWord, htime⟩ := (Encoding.decode_comp_eq_some_iff _ _).mp htime
  rw [SingleTapeTM.Description.decode_bitEncoding_eq_some_iff.mp hinput,
    SingleTapeTM.Description.decode_bitEncoding_eq_some_iff.mp hcertificateWord,
    SingleTapeTM.Description.decode_bitEncoding_eq_some_iff.mp htimeWord]
  have hlength := unary_eq_length_of_decode hcertificate
  have htime := unary_eq_length_of_decode htime
  simp only [List.length_append, List.length_cons, List.length_map,
    SingleTapeTM.Description.length_bitEncoding]
  lia

/-- A successfully decoded certificate length is bounded by the supplied word's length. -/
theorem certificateLength_le_length_of_decode {word : List CodeSymbol} {problem : Instance}
    (h : encoding.decode word = some problem) : problem.certificateLength ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- A successfully decoded time bound is bounded by the supplied word's length. -/
theorem time_le_length_of_decode {word : List CodeSymbol} {problem : Instance}
    (h : encoding.decode word = some problem) : problem.time ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- A successfully decoded input is no longer than the supplied word. -/
theorem input_length_le_length_of_decode {word : List CodeSymbol} {problem : Instance}
    (h : encoding.decode word = some problem) : problem.input.length ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- The specified certificate length cannot exceed the length of the encoded instance. -/
theorem certificateLength_le_length_encoding (problem : Instance) :
    problem.certificateLength ≤ (encoding.encode problem).length :=
  certificateLength_le_length_of_decode (encoding.decode_encode problem)

/-- The unary bound cannot exceed the length of the encoded instance. -/
theorem time_le_length_encoding (problem : Instance) :
    problem.time ≤ (encoding.encode problem).length :=
  time_le_length_of_decode (encoding.decode_encode problem)

/-- This language consists of words that decode to instances with an accepting certificate. -/
def language : Language CodeSymbol := encodedLanguage satisfiable encoding

/-- Encoding a structured instance preserves whether it has an accepting certificate. -/
@[simp] theorem encode_mem_language (problem : Instance) :
    encoding.encode problem ∈ language ↔ problem ∈ satisfiable := by
  simp [language]

end Algolean.Problems.TMSAT
