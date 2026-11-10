/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Basic
public import Algolean.Problems.Encoding
public import Algolean.Models.SingleTapeTM.Alphabet.List
public import Algolean.Models.SingleTapeTM.Alphabet.Pair

/-!
# Encoding Boolean formulas with binary variable names

* A variable name is a finite list of binary digits. Leading zeros distinguish names.
* A literal is a variable or its negation. A clause is a disjunction of literals.
* A formula is a conjunction of clauses. Its encoding uses the symbols described in `CodeSymbol`.
* `language` contains the encodings of satisfiable formulas.
  Incorrectly formatted lists are rejected.
* `verifierEncoding` stores a formula and its certificate with one symbol between them.

A certificate lists variables and proposed truth values. Only variables occurring in the formula
need to be listed, and the length bound counts the actual binary digits of their names.
-/

@[expose] public section

namespace Algolean.Problems.SAT

open Computability Algorithms.Alphabet

/-- A variable is named by a finite list of binary digits, which may be empty. -/
abbrev Variable := List Bool

/-- These symbols are binary digits and two additional symbols for a variable and its negation. -/
abbrev LiteralSymbol := Extended Bool 2

/-- Two more symbols end each variable name and end the clause containing those variables. -/
abbrev ClauseSymbol := Extended LiteralSymbol 2

/--
The tape uses binary digits and six additional symbols. A digit is written as `Sum.inl b`,
and an additional symbol is written as `Sum.inr k`.

* Symbol 0 begins a variable without negation, and symbol 1 begins a negated variable.
* Symbol 2 ends a variable name, and symbol 3 ends a clause or an assignment list.
* Symbol 4 follows each clause, and symbol 5 ends the formula.
-/
abbrev CodeSymbol := Extended Bool 6

/-- A literal begins with a symbol saying whether it is negated, followed by its binary name. -/
def literalEncoding : Encoding (Literal Variable) LiteralSymbol :=
  ((encodingList Bool).sum (encodingList Bool)).ofEquiv Literal.equiv

/--
A clause lists its literals, with a symbol after each name and another symbol ending the list.
-/
def clauseEncoding : Encoding (Clause Variable) ClauseSymbol := literalEncoding.list

/-- A formula lists its clauses in order. Decoding checks all symbols separating and ending them. -/
def encoding : Encoding (CNF Variable) CodeSymbol :=
  (clauseEncoding.list.mapSymbols (Extended.flattenThreeEquiv Bool 2 2 2)).strict

/--
A certificate lists variables and proposed truth values. The literal type records these values:
`.pos name` assigns true to `name`, and `.neg name` assigns false. The first assignment to a
name takes precedence, and a name absent from the list is assigned false.

This finite list can be written on a Turing machine's tape. `Certificate.assignment` in
`Problems.SAT.Verification` converts it into the assignment function already used in
`Problems.SAT.Basic` to evaluate formulas and define satisfiability.
-/
abbrev Certificate := Clause Variable

/-- A certificate writes its assignments in the same format as a clause, using `CodeSymbol`. -/
def certificateEncoding : Encoding Certificate CodeSymbol :=
  ((clauseEncoding.comp (words ClauseSymbol 2)).mapSymbols
    (Extended.flattenThreeEquiv Bool 2 2 2)).strict

/--
The verifier receives an encoded formula and certificate with one separate symbol between them.
-/
def verifierEncoding : Encoding (CNF Variable × Certificate) (Extended CodeSymbol 1) :=
  encoding.pair certificateEncoding

/-- The verifier's input uses the same pair format as the definition of NP. -/
theorem verifierEncoding_encode (formula : CNF Variable) (certificate : Certificate) :
    verifierEncoding.encode (formula, certificate) = (wordPair CodeSymbol).encode
      (encoding.encode formula, certificateEncoding.encode certificate) := rfl

/-- Writing a certificate with `CodeSymbol` takes as many symbols as writing it as a clause. -/
@[simp] theorem length_certificateEncoding (certificate : Certificate) :
    (certificateEncoding.encode certificate).length =
      (clauseEncoding.encode certificate).length := by
  simp [certificateEncoding, Encoding.strict, Encoding.comp]

/-- A literal uses its name's digits and one symbol saying whether the variable is negated. -/
@[simp] theorem length_literalEncoding (literal : Literal Variable) :
    (literalEncoding.encode literal).length = literal.name.length + 1 := by
  cases literal <;> simp [literalEncoding, Encoding.ofEquiv, Literal.equiv, encodingList]

/-- Each literal uses its name's digits and two extra symbols; one more symbol ends the clause. -/
@[simp] theorem length_clauseEncoding (clause : Clause Variable) :
    (clauseEncoding.encode clause).length =
      (clause.map (fun literal => literal.name.length + 2)).sum + 1 := by
  simp only [clauseEncoding, Encoding.length_list, length_literalEncoding]
  induction clause with
  | nil => simp
  | cons literal rest ih => simp_all [Nat.add_assoc]; lia

/--
Each clause adds its encoded length and one separating symbol; one final symbol ends the formula.
-/
@[simp] theorem length_encoding (formula : CNF Variable) :
    (encoding.encode formula).length =
      (formula.map (fun clause => (clauseEncoding.encode clause).length + 1)).sum + 1 := by
  simp only [encoding, Encoding.strict, Encoding.length_mapSymbols, Encoding.length_list]
  induction formula with
  | nil => simp
  | cons clause rest ih => simp_all [Nat.add_assoc]; lia

/--
With no assignments to record, the encoding is just `Sum.inr 3`, which ends the assignment list.
-/
theorem certificateEncoding_encode_nil :
    certificateEncoding.encode [] = [(.inr 3 : CodeSymbol)] := rfl

/--
An assignment of true starts with `Sum.inr 0`, which records the value true, followed by the
variable's binary name. `Sum.inr 2` ends that name; the other assignments come next.
-/
theorem certificateEncoding_encode_pos (name : Variable) (rest : Certificate) :
    certificateEncoding.encode (.pos name :: rest) =
      .inr 0 :: name.map Sum.inl ++ .inr 2 :: certificateEncoding.encode rest := by
  simp [certificateEncoding, clauseEncoding, literalEncoding, Encoding.strict,
    Encoding.mapSymbols, Encoding.comp, Encoding.list, Encoding.ofEquiv, Encoding.sum,
    words, encodingList, Literal.equiv, List.map_append, List.map_map,
    Function.comp_def, Extended.flattenThreeEquiv, Extended.flattenEquiv, finSumFinEquiv]

/--
An assignment of false starts with `Sum.inr 1`, which records the value false, followed by the
variable's binary name. `Sum.inr 2` ends that name; the other assignments come next.
-/
theorem certificateEncoding_encode_neg (name : Variable) (rest : Certificate) :
    certificateEncoding.encode (.neg name :: rest) =
      .inr 1 :: name.map Sum.inl ++ .inr 2 :: certificateEncoding.encode rest := by
  simp [certificateEncoding, clauseEncoding, literalEncoding, Encoding.strict,
    Encoding.mapSymbols, Encoding.comp, Encoding.list, Encoding.ofEquiv, Encoding.sum,
    words, encodingList, Literal.equiv, List.map_append, List.map_map,
    Function.comp_def, Extended.flattenThreeEquiv, Extended.flattenEquiv, finSumFinEquiv]

/-- With no clauses to record, the encoding is just `Sum.inr 5`, which ends the formula. -/
theorem encoding_encode_nil : encoding.encode [] = [(.inr 5 : CodeSymbol)] := rfl

/--
The first clause is written in the same format as a certificate containing the same literals.
The symbol `Sum.inr 4` follows this clause, and the encoding of the remaining clauses comes next.
-/
theorem encoding_encode_cons (clause : Clause Variable) (rest : CNF Variable) :
    encoding.encode (clause :: rest) =
      certificateEncoding.encode clause ++ .inr 4 :: encoding.encode rest := by
  simp [encoding, certificateEncoding, Encoding.strict, Encoding.mapSymbols,
    Encoding.comp, Encoding.list, words, List.map_append, List.map_map,
    Function.comp_def, Extended.flattenThreeEquiv, Extended.flattenEquiv, finSumFinEquiv]

/-- Decoding returns a formula exactly when the supplied list is that formula's full encoding. -/
@[simp] theorem decode_encoding_eq_some_iff {word : List CodeSymbol} {formula : CNF Variable} :
    encoding.decode word = some formula ↔ word = encoding.encode formula :=
  Encoding.decode_strict_eq_some_iff
    (clauseEncoding.list.mapSymbols (Extended.flattenThreeEquiv Bool 2 2 2))

/-- Decoding returns a certificate exactly when the supplied list is its full encoding. -/
@[simp] theorem decode_certificateEncoding_eq_some_iff
    {word : List CodeSymbol} {certificate : Certificate} :
    certificateEncoding.decode word = some certificate ↔
      word = certificateEncoding.encode certificate :=
  Encoding.decode_strict_eq_some_iff
    ((clauseEncoding.comp (words ClauseSymbol 2)).mapSymbols
      (Extended.flattenThreeEquiv Bool 2 2 2))

/-- Decoding returns a formula and certificate exactly when the whole input is their encoding. -/
@[simp] theorem decode_verifierEncoding_eq_some_iff
    {word : List (Extended CodeSymbol 1)} {formula : CNF Variable} {certificate : Certificate} :
    verifierEncoding.decode word = some (formula, certificate) ↔
      word = verifierEncoding.encode (formula, certificate) := by
  rw [verifierEncoding, Encoding.decode_pair_eq_some_iff]
  constructor
  · rintro ⟨first, second, hword, hformula, hcertificate⟩
    rw [decode_encoding_eq_some_iff] at hformula
    rw [decode_certificateEncoding_eq_some_iff] at hcertificate
    simpa [verifierEncoding, Encoding.pair, words, hformula, hcertificate] using hword
  · rintro rfl
    exact ⟨encoding.encode formula, certificateEncoding.encode certificate, rfl,
      encoding.decode_encode formula, certificateEncoding.decode_encode certificate⟩

/-- This language consists of encoded formulas that have a satisfying assignment. -/
def language : Language CodeSymbol := encodedLanguage CNF.satisfiable encoding

/-- Encoding preserves whether a formula has a satisfying assignment. -/
@[simp] theorem encode_mem_language (formula : CNF Variable) :
    encoding.encode formula ∈ language ↔ formula ∈ CNF.satisfiable := by simp [language]

end Algolean.Problems.SAT
