/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Basic
public import Algolean.Problems.Encoding
public import Algolean.Models.SingleTapeTM.Alphabet.List

/-!
# Encoding Boolean formulas with binary variable names

* Variables are named by finite Boolean words. Their names are compared as words.
* A literal stores its sign followed by its variable name.
* Six markers record the two signs, literal and clause ends, clause separators, and the formula end.
* `language` contains exactly the encoded satisfiable formulas. Malformed words are rejected.

Variable names are stored directly. An assignment certificate therefore needs values only for
names occurring in the formula, regardless of how large a number a name might represent.
-/

@[expose] public section

namespace Algolean.Problems.SAT

open Computability Algorithms.Alphabet

/-- A variable is named by a finite word of binary digits, including the empty word. -/
abbrev Variable := List Bool

/-- This alphabet contains binary digits and two literal signs. -/
abbrev LiteralSymbol := Extended Bool 2

/-- This alphabet also contains markers separating literals and ending a clause. -/
abbrev ClauseSymbol := Extended LiteralSymbol 2

/-- The formula alphabet contains Boolean digits and six distinct markers. -/
abbrev CodeSymbol := Extended Bool 6

/-- A literal is stored as one sign marker followed by the binary digits of its name. -/
def literalEncoding : Encoding (Literal Variable) LiteralSymbol :=
  ((encodingList Bool).sum (encodingList Bool)).ofEquiv Literal.equiv

/-- A clause stores its literals in order and ends with a separate clause marker. -/
def clauseEncoding : Encoding (Clause Variable) ClauseSymbol := literalEncoding.list

/-- A formula stores its clauses in order, with all boundaries checked during decoding. -/
def encoding : Encoding (CNF Variable) CodeSymbol :=
  (clauseEncoding.list.mapSymbols (Extended.flattenThreeEquiv Bool 2 2 2)).strict

/--
A certificate lists signed names, assigning true to positive names and false to negative names.
-/
abbrev Certificate := Clause Variable

/-- A certificate uses the clause format, with its symbols included in the formula alphabet. -/
def certificateEncoding : Encoding Certificate CodeSymbol :=
  ((clauseEncoding.comp (words ClauseSymbol 2)).mapSymbols
    (Extended.flattenThreeEquiv Bool 2 2 2)).strict

/-- A certificate has the length of its encoded signed list, with no additional separators. -/
@[simp] theorem length_certificateEncoding (certificate : Certificate) :
    (certificateEncoding.encode certificate).length =
      (clauseEncoding.encode certificate).length := by
  simp [certificateEncoding, Encoding.strict, Encoding.comp]

/-- Encoding a literal uses one symbol for its sign in addition to its name. -/
@[simp] theorem length_literalEncoding (literal : Literal Variable) :
    (literalEncoding.encode literal).length = literal.name.length + 1 := by
  cases literal <;> simp [literalEncoding, Encoding.ofEquiv, Literal.equiv, encodingList]

/-- The encoded clause includes every name, each sign and separator, and one end marker. -/
@[simp] theorem length_clauseEncoding (clause : Clause Variable) :
    (clauseEncoding.encode clause).length =
      (clause.map (fun literal => literal.name.length + 2)).sum + 1 := by
  simp only [clauseEncoding, Encoding.length_list, length_literalEncoding]
  induction clause with
  | nil => simp
  | cons literal rest ih => simp_all [Nat.add_assoc]; lia

/-- Each clause contributes its own encoded length, one separator, and the formula end marker. -/
@[simp] theorem length_encoding (formula : CNF Variable) :
    (encoding.encode formula).length =
      (formula.map (fun clause => (clauseEncoding.encode clause).length + 1)).sum + 1 := by
  simp only [encoding, Encoding.strict, Encoding.length_mapSymbols, Encoding.length_list]
  induction formula with
  | nil => simp
  | cons clause rest ih => simp_all [Nat.add_assoc]; lia

/-- Successful decoding identifies the complete encoded formula, including every marker. -/
@[simp] theorem decode_encoding_eq_some_iff {word : List CodeSymbol} {formula : CNF Variable} :
    encoding.decode word = some formula ↔ word = encoding.encode formula :=
  Encoding.decode_strict_eq_some_iff
    (clauseEncoding.list.mapSymbols (Extended.flattenThreeEquiv Bool 2 2 2))

/-- This language consists of encoded formulas that have a satisfying assignment. -/
def language : Language CodeSymbol := encodedLanguage CNF.satisfiable encoding

/-- Encoding preserves whether a formula has a satisfying assignment. -/
@[simp] theorem encode_mem_language (formula : CNF Variable) :
    encoding.encode formula ∈ language ↔ formula ∈ CNF.satisfiable := by simp [language]

end Algolean.Problems.SAT
