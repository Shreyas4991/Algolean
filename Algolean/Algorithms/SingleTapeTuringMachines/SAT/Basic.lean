/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SingleTapeTM.Encodings.SAT
public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Tactic.FinCases

/-!
# Symbols and states for reading SAT inputs

* The tape contains an encoded formula, one separating symbol, and an encoded certificate.
* `Symbol` uses the formula's existing symbols and adds only the separator used by `wordPair`.
  Blank cells are represented separately by `none`.
* The named symbols below explain how to read variable names, truth values, and clause endings.
* `FormatState` records which part of the formula or certificate the machine is reading.

The same name may appear several times in a certificate, and some names may be absent. These
are allowed by the format. The assignment function in
`Problems.SingleTapeTM.SAT.Verification` gives each name its first value, or false if it is absent.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT

open Alphabet Problems.SAT

/-- The tape uses the SAT encoding's symbols and one symbol separating formula and certificate. -/
abbrev Symbol := Extended Problems.SAT.CodeSymbol 1

/-- This symbol records one binary digit of a variable name. -/
def digit (value : Bool) : Symbol := .inl (.inl value)

/-- This symbol begins an unnegated variable in a formula or records true in a certificate. -/
def positiveSign : Symbol := .inl (.inr 0)

/-- This symbol begins a negated variable in a formula or records false in a certificate. -/
def negativeSign : Symbol := .inl (.inr 1)

/-- This symbol follows the last binary digit of each variable name, including an empty name. -/
def nameEnd : Symbol := .inl (.inr 2)

/-- This symbol ends a clause or the list of assignments in a certificate. -/
def clauseEnd : Symbol := .inl (.inr 3)

/-- This symbol follows each clause's ending, including the last clause in a formula. -/
def clauseSeparator : Symbol := .inl (.inr 4)

/-- This symbol ends the formula, including a formula with no clauses. -/
def formulaEnd : Symbol := .inl (.inr 5)

/-- This symbol separates the encoded formula from its certificate, as in `Alphabet.wordPair`. -/
def certificateSeparator : Symbol := .inr 0

/--
`sign true` begins an unnegated variable in a formula or records true in a certificate.
`sign false` begins a negated variable or records false in a certificate.
-/
def sign (positive : Bool) : Symbol := if positive then positiveSign else negativeSign

/-- These are the symbols of a certificate as they appear on the verifier's tape. -/
def certificateSymbols (certificate : Certificate) : List Symbol :=
  (certificateEncoding.encode certificate).map Sum.inl

/-- These are the symbols of a formula as they appear on the verifier's tape. -/
def formulaSymbols (formula : CNF Variable) : List Symbol :=
  (encoding.encode formula).map Sum.inl

/-- An empty certificate is written with just the symbol ending the list of assignments. -/
theorem certificateSymbols_nil : certificateSymbols [] = [clauseEnd] := rfl

/-- A true assignment writes its value, the binary name, and the symbol ending that name. -/
theorem certificateSymbols_pos (name : Variable) (rest : Certificate) :
    certificateSymbols (.pos name :: rest) =
      positiveSign :: name.map digit ++ nameEnd :: certificateSymbols rest := by
  simp [certificateSymbols, certificateEncoding_encode_pos, List.map_append, List.map_map,
    Function.comp_def, positiveSign, nameEnd, digit]

/-- A false assignment writes its value, the binary name, and the symbol ending that name. -/
theorem certificateSymbols_neg (name : Variable) (rest : Certificate) :
    certificateSymbols (.neg name :: rest) =
      negativeSign :: name.map digit ++ nameEnd :: certificateSymbols rest := by
  simp [certificateSymbols, certificateEncoding_encode_neg, List.map_append, List.map_map,
    Function.comp_def, negativeSign, nameEnd, digit]

/-- Each listed literal writes its sign, its binary name, and the symbol ending that name. -/
theorem certificateSymbols_cons (positive : Bool) (name : Variable) (rest : Certificate) :
    certificateSymbols ((if positive then .pos name else .neg name) :: rest) =
      sign positive :: name.map digit ++ nameEnd :: certificateSymbols rest := by
  cases positive <;> simp [certificateSymbols_pos, certificateSymbols_neg, sign]

/-- An empty formula is written with just the symbol ending the formula. -/
theorem formulaSymbols_nil : formulaSymbols [] = [formulaEnd] := rfl

/-- The first clause is followed by its separating symbol and the remaining clauses. -/
theorem formulaSymbols_cons (clause : Clause Variable) (rest : CNF Variable) :
    formulaSymbols (clause :: rest) =
      certificateSymbols clause ++ clauseSeparator :: formulaSymbols rest := by
  simp [formulaSymbols, certificateSymbols, encoding_encode_cons, List.map_append,
    clauseSeparator]

/-- The verifier's input places the encoded formula before its separator and certificate. -/
theorem verifierEncoding_symbols (formula : CNF Variable) (certificate : Certificate) :
    verifierEncoding.encode (formula, certificate) =
      formulaSymbols formula ++ certificateSeparator :: certificateSymbols certificate := rfl

/-- The extra symbol separating formula and certificate cannot occur inside either encoded part. -/
theorem certificateSeparator_not_mem (word : List CodeSymbol) :
    certificateSeparator ∉ word.map (Sum.inl : CodeSymbol → Symbol) := by
  simp [certificateSeparator, List.mem_map]

/-- The scanner compares the symbol under the head with these symbols, from first to last. -/
def symbols : List Symbol :=
  [digit false, digit true, positiveSign, negativeSign, nameEnd, clauseEnd,
    clauseSeparator, formulaEnd, certificateSeparator]

/-- Every tape symbol appears in `symbols`, so the scanner's comparisons can find it. -/
theorem mem_symbols (symbol : Symbol) : symbol ∈ symbols := by
  rcases symbol with ((value | marker) | separator)
  · cases value <;> decide
  · fin_cases marker <;> decide
  · fin_cases separator; decide

/-- These states record what may legally follow the part of the input already read. -/
inductive FormatState where
  /-- The next symbol may start a literal, end an empty clause, or end the formula. -/
  | clauseStart
  /-- The machine is reading the binary name of a variable in the formula. -/
  | formulaName
  /-- A name has ended; another literal or the clause's ending must follow. -/
  | nextLiteral
  /-- A clause has ended; its separating symbol must follow. -/
  | afterClause
  /-- The formula has ended; the symbol separating it from the certificate must follow. -/
  | certificateSeparator
  /-- The next symbol may start an assignment or end the certificate. -/
  | certificateStart
  /-- The machine is reading the binary name of a variable in the certificate. -/
  | certificateName
  /-- The formula and certificate have ended; any further symbol makes the input invalid. -/
  | inputEnd
  /-- A symbol has appeared where the format does not allow it. -/
  | reject
deriving DecidableEq

/-- This list contains every state needed to check the format of a formula and certificate. -/
def FormatState.states : List FormatState :=
  [.clauseStart, .formulaName, .nextLiteral, .afterClause, .certificateSeparator,
    .certificateStart, .certificateName, .inputEnd, .reject]

/-- Every state used to check the input format appears in `FormatState.states`. -/
theorem FormatState.mem_states (label : FormatState) : label ∈ states := by
  cases label <;> decide

instance : Fintype FormatState := .ofList FormatState.states FormatState.mem_states

end Algolean.Algorithms.SingleTapeTuringMachines.SAT
