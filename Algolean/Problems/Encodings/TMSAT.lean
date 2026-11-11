/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.TMSAT.Basic
public import Algolean.Problems.Encodings.Alphabet
public import Algolean.Models.SingleTapeTM.DescriptionEncoding

/-!
# Writing TMSAT instances as words

* `encoding` writes the machine, input, certificate length, and time bound in that order.
* The machine description contains the complete finite transition table.
* `language` contains the words that decode to satisfiable instances. Failed decoding gives a
  no answer.
* `encodingOver` and `languageOver` represent the same problem using only symbols of `Γ`.
  This requires two distinct symbols of `Γ`, chosen once for the whole language.
* Encoding an instance preserves its answer. Every decoded certificate length and time bound
  fits within the length of the word given to the decoder.

The alphabet `Γ` is fixed. Input symbols are represented by binary words determined by a fixed
`Encodable Γ` instance. Since `Γ` is finite, one constant bounds all these symbol-code lengths.
Extra symbols separate the four parts of the instance.

Each transition has separate fields for the written cell value, movement, and next state.
The written cell values are numbered within the fixed finite tape alphabet, including blank.
Movement code zero means no movement, one means left, and two means right. Next-state code
zero means halt, and code `q + 1` means continue in state `q`. Separating these fields lets a
machine read them without undoing a numeric pairing function. Decoding checks each field and
rejects references to states missing from the table.

In `encoding`, a bound of `k` is written as exactly `k` symbols. In `encodingOver`, each of those
symbols is replaced by a fixed-length word over `Γ`. This multiplies the length of each bound
by one fixed constant. The bound's value stays the same.

The encoder chooses one word for each instance. The decoder can also accept other words that
describe the same instance. This lets us reuse the existing number decoders and follows the
use of multiple machine descriptions in [Barak's lecture notes][barak2006]. All such words give
the same yes or no answer. Their lengths can differ, so the size proofs use the length of the
word passed to the decoder and cover every word it accepts.

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

/-- A unary bound of `n` is written as `n` true bits. -/
theorem encode_unaryEncoding (n : Nat) : unaryEncoding.encode n = List.replicate n true := by
  induction n <;> simp_all [unaryEncoding, unaryEncodeNat, List.replicate_succ]

/-- The unary representation has exactly the specified length. -/
@[simp] theorem length_unaryEncoding (value : ℕ) : (unaryEncoding.encode value).length = value := by
  rw [encode_unaryEncoding, List.length_replicate]

/-- A successfully decoded unary value equals the number of bits in the input word. -/
theorem unary_eq_length_of_decode {word : List Bool} {value : ℕ}
    (h : unaryEncoding.decode word = some value) : value = word.length := by
  simp only [unaryEncoding] at h
  split at h <;> simp_all

/-- This alphabet separates the fields within the machine-input pair and the pair of bounds. -/
abbrev PayloadSymbol := Extended SingleTapeTM.Description.CodeSymbol 1

/-- This alphabet separates the machine-input pair from the two unary bounds. -/
abbrev CodeSymbol := Extended PayloadSymbol 1

/-- Equality of description symbols uses only their fixed alphabet tags and binary digits. -/
instance : DecidableEq CodeSymbol := by
  letI : DecidableEq SingleTapeTM.Description.MovementSymbol := inferInstance
  letI : DecidableEq SingleTapeTM.Description.TransitionSymbol := inferInstance
  letI : DecidableEq SingleTapeTM.Description.RowSymbol := inferInstance
  letI : DecidableEq SingleTapeTM.Description.TableSymbol := inferInstance
  letI : DecidableEq SingleTapeTM.Description.BodySymbol := inferInstance
  letI : DecidableEq SingleTapeTM.Description.CodeSymbol := inferInstance
  letI : DecidableEq PayloadSymbol := inferInstance
  infer_instance

namespace CodeSymbol

/-- This is one binary digit in a machine description, input-symbol number, or unary bound. -/
def digit (bit : Bool) : CodeSymbol :=
  .inl (.inl (SingleTapeTM.Description.bitSymbol bit))

/-- This separates the written cell value from the movement in one transition. -/
def writeEnd : CodeSymbol := .inl (.inl (.inl (.inl (.inl (.inl (.inr 0))))))

/-- This separates the movement from the next state in one transition. -/
def movementEnd : CodeSymbol := .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inr 0)))))))

/-- This ends one transition's numeric code or one input symbol's numeric code. -/
def entryEnd : CodeSymbol := .inl (.inl (.inl (.inl (.inl (.inr 0)))))

/-- This ends a transition-table row or the encoded input word. -/
def listEnd : CodeSymbol := .inl (.inl SingleTapeTM.Description.wordEnd)

/-- This follows each completed row of the transition table. -/
def rowSeparator : CodeSymbol := .inl (.inl (.inl (.inl (.inr 0))))

/-- This ends the complete transition table. -/
def tableEnd : CodeSymbol := .inl (.inl (.inl (.inl (.inr 1))))

/-- This separates the initial state from the transition table. -/
def initialEnd : CodeSymbol := .inl (.inl (.inl (.inr 0)))

/-- This separates the largest state number from the rest of the verifier description. -/
def headerEnd : CodeSymbol := .inl (.inl (.inr 0))

/-- This separates the verifier from its input and the certificate length from the time bound. -/
def fieldSeparator : CodeSymbol := .inl (.inr 0)

/-- This separates the machine-input pair from the two bounds. -/
def boundsSeparator : CodeSymbol := .inr 0

end CodeSymbol

variable {Γ : Type} [Fintype Γ] [Encodable Γ]

/-- This encoding stores the complete verifier description and then the encoded input word. -/
def payloadEncoding : Encoding (SingleTapeTM.Description (TapeSymbol Γ) × List Γ) PayloadSymbol :=
  SingleTapeTM.Description.encoding.pair SingleTapeTM.Description.wordEncoding

/-- The certificate length and time bound are stored independently, with one separator. -/
def boundsEncoding : Encoding (ℕ × ℕ) PayloadSymbol :=
  (unaryEncoding.comp SingleTapeTM.Description.bitEncoding).pair
    (unaryEncoding.comp SingleTapeTM.Description.bitEncoding)

/-- The field order is the verifier, input, certificate length, and time bound. -/
def Instance.equiv : Instance Γ ≃
    (SingleTapeTM.Description (TapeSymbol Γ) × List Γ) × (ℕ × ℕ) where
  toFun problem := ((problem.verifier, problem.input), (problem.certificateLength, problem.time))
  invFun problem := ⟨problem.1.1, problem.1.2, problem.2.1, problem.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The certificate length and time are unary, and three separators delimit the fields. -/
def encoding : Encoding (Instance Γ) CodeSymbol :=
  (payloadEncoding.pair boundsEncoding).ofEquiv Instance.equiv

/-- The length counts the machine code, input, two unary fields, and three separators. -/
@[simp] theorem length_encoding (problem : Instance Γ) :
    (encoding.encode problem).length =
      (SingleTapeTM.Description.encoding.encode problem.verifier).length +
        (SingleTapeTM.Description.wordEncoding.encode problem.input).length +
        problem.certificateLength + problem.time + 3 := by
  simp [encoding, Encoding.ofEquiv, Instance.equiv, payloadEncoding, boundsEncoding, Encoding.comp]
  lia

/--
The number of states, decoded input, certificate length, time bound, and three separators fit
in the input word.
This holds for every successful decoding, including other words describing the same machine.
-/
theorem states_add_input_length_add_bounds_le_length_of_decode
    {word : List CodeSymbol} {problem : Instance Γ}
    (h : encoding.decode word = some problem) :
    problem.verifier.states + 1 + problem.input.length + problem.certificateLength +
      problem.time + 3 ≤ word.length := by
  have hfields := (Encoding.decode_ofEquiv_eq_some_iff _ _).mp h
  change (payloadEncoding.pair boundsEncoding).decode word =
    some ((problem.verifier, problem.input), (problem.certificateLength, problem.time)) at hfields
  obtain ⟨payload, bounds, rfl, hpayload, hbounds⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hfields
  obtain ⟨machine, inputWord, rfl, hmachine, hinput⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hpayload
  obtain ⟨certificateWord, timeWord, rfl, hcertificate, htime⟩ :=
    (Encoding.decode_pair_eq_some_iff _ _).mp hbounds
  obtain ⟨certificateBits, hcertificateWord, hcertificate⟩ :=
    (Encoding.decode_comp_eq_some_iff _ _).mp hcertificate
  obtain ⟨timeBits, htimeWord, htime⟩ := (Encoding.decode_comp_eq_some_iff _ _).mp htime
  have hinputLength := SingleTapeTM.Description.length_le_of_decode_wordEncoding hinput
  have hmachineLength := SingleTapeTM.Description.states_le_length_of_decode hmachine
  rw [SingleTapeTM.Description.decode_bitEncoding_eq_some_iff.mp hcertificateWord,
    SingleTapeTM.Description.decode_bitEncoding_eq_some_iff.mp htimeWord]
  have hlength := unary_eq_length_of_decode hcertificate
  have htime := unary_eq_length_of_decode htime
  simp only [List.length_append, List.length_cons, List.length_map,
    SingleTapeTM.Description.length_bitEncoding]
  lia

/-- The decoded input and the two unary bounds fit in every word accepted by the decoder. -/
theorem input_length_add_bounds_le_length_of_decode {word : List CodeSymbol} {problem : Instance Γ}
    (h : encoding.decode word = some problem) :
    problem.input.length + problem.certificateLength + problem.time + 3 ≤ word.length := by
  have := states_add_input_length_add_bounds_le_length_of_decode h
  lia

/-- A successfully decoded certificate length is bounded by the input word's length. -/
theorem certificateLength_le_length_of_decode {word : List CodeSymbol} {problem : Instance Γ}
    (h : encoding.decode word = some problem) : problem.certificateLength ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- A successfully decoded time bound is bounded by the input word's length. -/
theorem time_le_length_of_decode {word : List CodeSymbol} {problem : Instance Γ}
    (h : encoding.decode word = some problem) : problem.time ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- A successfully decoded input is no longer than the input word. -/
theorem input_length_le_length_of_decode {word : List CodeSymbol} {problem : Instance Γ}
    (h : encoding.decode word = some problem) : problem.input.length ≤ word.length := by
  have := input_length_add_bounds_le_length_of_decode h
  lia

/-- The specified certificate length cannot exceed the length of the encoded instance. -/
theorem certificateLength_le_length_encoding (problem : Instance Γ) :
    problem.certificateLength ≤ (encoding.encode problem).length :=
  certificateLength_le_length_of_decode (encoding.decode_encode problem)

/-- The unary bound cannot exceed the length of the encoded instance. -/
theorem time_le_length_encoding (problem : Instance Γ) :
    problem.time ≤ (encoding.encode problem).length :=
  time_le_length_of_decode (encoding.decode_encode problem)

/-- This language consists of words that decode to instances with an accepting certificate. -/
def language (yes : Γ) : Language CodeSymbol := encodedLanguage (satisfiable yes) encoding

/-- Encoding a structured instance preserves whether it has an accepting certificate. -/
@[simp] theorem encode_mem_language (yes : Γ) (problem : Instance Γ) :
    encoding.encode problem ∈ language yes ↔ problem ∈ satisfiable yes := by
  simp [language]

/--
This writes a TMSAT instance using only symbols of `Γ`. Each symbol of the existing instance
encoding becomes a fixed-length word over two chosen symbols of `Γ`. The symbol choices and
the numbering of the finite alphabet are fixed independently of the instance.
-/
noncomputable def encodingOver [Nontrivial Γ] : Encoding (Instance Γ) Γ :=
  letI : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  encoding.over

omit [Encodable Γ] in
/-- Writing the instance over `Γ` multiplies its existing encoded length by one fixed constant. -/
theorem length_encodingOver [Nontrivial Γ] (problem : Instance Γ) :
    (encodingOver.encode problem).length =
      letI : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
      (encoding.encode problem).length * Fintype.card CodeSymbol := by
  simp [encodingOver]

omit [Encodable Γ] in
/--
The decoded number of states, input, and unary bounds all fit in the word over `Γ`. This holds
for every accepted spelling of the machine description, not only the encoder's chosen spelling.
-/
theorem states_add_input_length_add_bounds_le_length_of_decodeOver [Nontrivial Γ]
    {word : List Γ} {problem : Instance Γ} (h : encodingOver.decode word = some problem) :
    problem.verifier.states + 1 + problem.input.length + problem.certificateLength +
      problem.time + 3 ≤ word.length := by
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  change encoding.over.decode word = some problem at h
  obtain ⟨raw, hword, hproblem⟩ := (Encoding.decode_over_eq_some_iff _).mp h
  rw [hword, length_finiteWordsOver]
  exact (states_add_input_length_add_bounds_le_length_of_decode hproblem).trans
    (Nat.le_mul_of_pos_right _ Fintype.card_pos)

omit [Encodable Γ] in
/--
Every successfully decoded word over `Γ` has room for its input, certificate length, and time
bound. This covers every word accepted by the decoder, including different words describing
the same instance.
-/
theorem input_length_add_bounds_le_length_of_decodeOver [Nontrivial Γ]
    {word : List Γ} {problem : Instance Γ} (h : encodingOver.decode word = some problem) :
    problem.input.length + problem.certificateLength + problem.time + 3 ≤ word.length := by
  have := states_add_input_length_add_bounds_le_length_of_decodeOver h
  lia

/-- This is TMSAT with its instances, as well as their inputs and certificates, encoded over `Γ`. -/
noncomputable def languageOver [Nontrivial Γ] (yes : Γ) : Language Γ :=
  encodedLanguage (satisfiable yes) encodingOver

omit [Encodable Γ] in
/-- Encoding an instance as a word over `Γ` preserves whether it is satisfiable. -/
@[simp] theorem encode_mem_languageOver [Nontrivial Γ] (yes : Γ) (problem : Instance Γ) :
    encodingOver.encode problem ∈ languageOver yes ↔ problem ∈ satisfiable yes := by
  simp [languageOver]

omit [Encodable Γ] in
/-- Changing a word of instance symbols to `Γ` preserves its TMSAT membership. -/
@[simp] theorem encode_word_mem_languageOver [Nontrivial Γ] (yes : Γ) (word : List CodeSymbol) :
    (finiteWordsOver CodeSymbol Γ).encode word ∈ languageOver yes ↔
      letI : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
      word ∈ language yes := by
  simp [languageOver, encodingOver, language]

end Algolean.Problems.TMSAT
