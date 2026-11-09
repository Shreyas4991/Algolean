/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Encoding
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
are allowed by the format. The assignment function in `Problems.SAT.Verification` gives each
name its first listed value, or false if it is absent.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT

open Alphabet

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
