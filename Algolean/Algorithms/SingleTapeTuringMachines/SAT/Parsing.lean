/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Basic
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FiniteState
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning

/-!
# Checking how a formula and certificate are written

* `checkFormat` reads the entire input and returns the head to its starting cell without changing
  any tape symbols. It finishes in state `FormatState.inputEnd` exactly for correctly written pairs.
* A correct pair contains an encoded formula, `certificateSeparator`, and an encoded certificate.
  Missing endings, misplaced symbols, and data after the certificate are rejected.
* `checkFormat_correct` records tape preservation and the exact `2 * word.length + 2` move
  count when using the checker inside the verifier. The checker reports its answer in a control
  state; the complete verifier writes its answer as a clean output word.

This program checks only how the input is written. A certificate may omit variables or list a name
more than once. Checking whether its values satisfy the formula is a separate operation.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/--
This rule records what can come next while reading a formula and its certificate. For example,
while reading a variable name, a binary digit continues the name and `nameEnd` finishes it.
An unexpected symbol sets the state to `reject`; that state persists through the rest of the input.
After the certificate ends, any further symbol is unexpected.
-/
private def formatNext : FormatState → Symbol → FormatState
  | .clauseStart, .inl (.inr 0) => .formulaName
  | .clauseStart, .inl (.inr 1) => .formulaName
  | .clauseStart, .inl (.inr 3) => .afterClause
  | .clauseStart, .inl (.inr 5) => .certificateSeparator
  | .formulaName, .inl (.inl _) => .formulaName
  | .formulaName, .inl (.inr 2) => .nextLiteral
  | .nextLiteral, .inl (.inr 0) => .formulaName
  | .nextLiteral, .inl (.inr 1) => .formulaName
  | .nextLiteral, .inl (.inr 3) => .afterClause
  | .afterClause, .inl (.inr 4) => .clauseStart
  | .certificateSeparator, .inr _ => .certificateStart
  | .certificateStart, .inl (.inr 0) => .certificateName
  | .certificateStart, .inl (.inr 1) => .certificateName
  | .certificateStart, .inl (.inr 3) => .inputEnd
  | .certificateName, .inl (.inl _) => .certificateName
  | .certificateName, .inl (.inr 2) => .certificateStart
  | _, _ => .reject

/--
This machine provides the state names for the format-checking query program. Its transition table
preserves the current symbol and halts. Query execution instead follows the instructions of
`checkFormat`; the query compiler can construct a transition table from those instructions.
-/
abbrev formatMachine : SingleTapeTM Symbol where
  State := FormatState
  q₀ := .clauseStart
  tr _ symbol := (⟨symbol, none⟩, none)

/-- The scanner uses `formatNext` and the complete lists of state names and tape symbols. -/
private def formatTable : ScanTable formatMachine where
  states := FormatState.states
  symbols := symbols
  next := formatNext
  mem_states := FormatState.mem_states
  mem_symbols := mem_symbols

namespace Parsing

open Problems.SAT

/-- Reading binary digits leaves the machine in the state for reading a formula's variable name. -/
private theorem foldl_formulaName (name : Variable) :
    (name.map digit).foldl formatNext .formulaName = .formulaName := by
  induction name with
  | nil => rfl
  | cons value rest ih => simpa [digit, formatNext] using ih

/-- Reading binary digits leaves the machine in the state for reading a certificate's name. -/
private theorem foldl_certificateName (name : Variable) :
    (name.map digit).foldl formatNext .certificateName = .certificateName := by
  induction name with
  | nil => rfl
  | cons value rest ih => simpa [digit, formatNext] using ih

/-- Reading a complete certificate reaches the state that requires the end of the input. -/
private theorem foldl_certificateSymbols (certificate : Certificate) :
    (certificateSymbols certificate).foldl formatNext .certificateStart = .inputEnd := by
  induction certificate with
  | nil => rfl
  | cons literal rest ih =>
    cases literal <;>
      simp [certificateSymbols_pos, certificateSymbols_neg, List.foldl_append, formatNext,
        positiveSign, negativeSign, nameEnd, foldl_certificateName, ih]

/-- Reading a complete clause reaches the state that requires its separating symbol. -/
private theorem foldl_clauseSymbols (clause : Clause Variable) (label : FormatState)
    (hstate : label = .clauseStart ∨ label = .nextLiteral) :
    (certificateSymbols clause).foldl formatNext label = .afterClause := by
  induction clause generalizing label with
  | nil => rcases hstate with rfl | rfl <;> rfl
  | cons literal rest ih =>
    have hrest := ih .nextLiteral (Or.inr rfl)
    rcases hstate with rfl | rfl <;> cases literal <;>
      simpa [certificateSymbols_pos, certificateSymbols_neg, List.foldl_append,
        formatNext, positiveSign, negativeSign, nameEnd, foldl_formulaName] using hrest

/-- Reading a complete formula reaches the state that requires the certificate separator. -/
private theorem foldl_formulaSymbols (formula : CNF Variable) :
    (formulaSymbols formula).foldl formatNext .clauseStart = .certificateSeparator := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
    simpa [formulaSymbols_cons, List.foldl_append,
      foldl_clauseSymbols clause .clauseStart (Or.inl rfl), clauseSeparator, formatNext] using ih

/-- Every correctly encoded formula-certificate pair reaches the input-ending state. -/
private theorem foldl_encoded_pair (formula : CNF Variable) (certificate : Certificate) :
    ((Alphabet.wordPair CodeSymbol).encode
      (encoding.encode formula, certificateEncoding.encode certificate)).foldl
        formatNext .clauseStart = .inputEnd := by
  change (formulaSymbols formula ++ certificateSeparator :: certificateSymbols certificate).foldl
    formatNext .clauseStart = .inputEnd
  simp [List.foldl_append, foldl_formulaSymbols, certificateSeparator, formatNext,
    foldl_certificateSymbols]

/--
This describes the symbols still required to finish a correctly written input from each state.
The formula and certificate in this description are used in proofs; the machine does not receive
these Lean values. For example, `certificateName` still requires the rest of a binary name, its
ending symbol, and the remaining assignments.
-/
private def Suffix : FormatState → List Symbol → Prop
  | .clauseStart, word => ∃ formula certificate,
      word = formulaSymbols formula ++ certificateSeparator :: certificateSymbols certificate
  | .formulaName, word => ∃ name : Variable, ∃ literals formula certificate,
      word = name.map digit ++ nameEnd :: certificateSymbols literals ++
        clauseSeparator :: formulaSymbols formula ++
          certificateSeparator :: certificateSymbols certificate
  | .nextLiteral, word => ∃ literals formula certificate,
      word = certificateSymbols literals ++ clauseSeparator :: formulaSymbols formula ++
        certificateSeparator :: certificateSymbols certificate
  | .afterClause, word => ∃ formula certificate,
      word = clauseSeparator :: formulaSymbols formula ++
        certificateSeparator :: certificateSymbols certificate
  | .certificateSeparator, word => ∃ certificate,
      word = certificateSeparator :: certificateSymbols certificate
  | .certificateStart, word => ∃ certificate, word = certificateSymbols certificate
  | .certificateName, word => ∃ name : Variable, ∃ certificate,
      word = name.map digit ++ nameEnd :: certificateSymbols certificate
  | .inputEnd, word => word = []
  | .reject, _ => False

/--
If the remaining symbols can finish a correct input after one state change, putting the symbol
just read back in front gives a correct continuation from the previous state.
-/
private theorem Suffix.prepend (label : FormatState) (symbol : Symbol) (word : List Symbol)
    (h : Suffix (formatNext label symbol) word) : Suffix label (symbol :: word) := by
  cases label with
  | clauseStart =>
    rcases symbol with ((value | marker) | separator)
    · exact False.elim h
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      · obtain ⟨name, literals, formula, certificate, rfl⟩ := h
        refine ⟨(.pos name :: literals) :: formula, certificate, ?_⟩
        simp [formulaSymbols_cons, certificateSymbols_pos, positiveSign, List.append_assoc]
      · obtain ⟨name, literals, formula, certificate, rfl⟩ := h
        refine ⟨(.neg name :: literals) :: formula, certificate, ?_⟩
        simp [formulaSymbols_cons, certificateSymbols_neg, negativeSign, List.append_assoc]
      · obtain ⟨formula, certificate, rfl⟩ := h
        exact ⟨[] :: formula, certificate, by
          simp [formulaSymbols_cons, certificateSymbols_nil, clauseEnd]⟩
      · obtain ⟨certificate, rfl⟩ := h
        exact ⟨[], certificate, by simp [formulaSymbols_nil, formulaEnd]⟩
    · exact False.elim h
  | formulaName =>
    rcases symbol with ((value | marker) | separator)
    · obtain ⟨name, literals, formula, certificate, rfl⟩ := h
      exact ⟨value :: name, literals, formula, certificate, by simp [digit]⟩
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      obtain ⟨literals, formula, certificate, rfl⟩ := h
      exact ⟨[], literals, formula, certificate, rfl⟩
    · exact False.elim h
  | nextLiteral =>
    rcases symbol with ((value | marker) | separator)
    · exact False.elim h
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      · obtain ⟨name, literals, formula, certificate, rfl⟩ := h
        exact ⟨.pos name :: literals, formula, certificate, by
          simp [certificateSymbols_pos, positiveSign, List.append_assoc]⟩
      · obtain ⟨name, literals, formula, certificate, rfl⟩ := h
        exact ⟨.neg name :: literals, formula, certificate, by
          simp [certificateSymbols_neg, negativeSign, List.append_assoc]⟩
      · obtain ⟨formula, certificate, rfl⟩ := h
        exact ⟨[], formula, certificate, by simp [certificateSymbols_nil, clauseEnd]⟩
    · exact False.elim h
  | afterClause =>
    rcases symbol with ((value | marker) | separator)
    · exact False.elim h
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      obtain ⟨formula, certificate, rfl⟩ := h
      exact ⟨formula, certificate, rfl⟩
    · exact False.elim h
  | certificateSeparator =>
    rcases symbol with ((value | marker) | separator)
    · exact False.elim h
    · exact False.elim h
    · fin_cases separator
      obtain ⟨certificate, rfl⟩ := h
      exact ⟨certificate, rfl⟩
  | certificateStart =>
    rcases symbol with ((value | marker) | separator)
    · exact False.elim h
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      · obtain ⟨name, certificate, rfl⟩ := h
        exact ⟨.pos name :: certificate, by simp [certificateSymbols_pos, positiveSign]⟩
      · obtain ⟨name, certificate, rfl⟩ := h
        exact ⟨.neg name :: certificate, by simp [certificateSymbols_neg, negativeSign]⟩
      · subst word
        exact ⟨[], rfl⟩
    · exact False.elim h
  | certificateName =>
    rcases symbol with ((value | marker) | separator)
    · obtain ⟨name, certificate, rfl⟩ := h
      exact ⟨value :: name, certificate, by simp [digit]⟩
    · fin_cases marker <;> simp only [formatNext, Suffix] at h ⊢
      obtain ⟨certificate, rfl⟩ := h
      exact ⟨[], certificate, rfl⟩
    · exact False.elim h
  | inputEnd => exact False.elim h
  | reject => exact False.elim h

/-- If reading a word reaches `inputEnd`, that word encodes a complete formula-certificate pair. -/
private theorem encoded_pair_of_foldl (word : List Symbol)
    (h : word.foldl formatNext .clauseStart = .inputEnd) :
    ∃ formula certificate, word = (Alphabet.wordPair CodeSymbol).encode
      (encoding.encode formula, certificateEncoding.encode certificate) := by
  have recover (word : List Symbol) (label : FormatState) :
      Suffix (word.foldl formatNext label) [] → Suffix label word := by
    induction word generalizing label with
    | nil => exact id
    | cons symbol word ih => exact fun h => Suffix.prepend label symbol word (ih _ h)
  have hs : Suffix .clauseStart word := recover word .clauseStart (by simp [h, Suffix])
  exact hs

/-- Reading reaches `inputEnd` exactly for the complete encodings of formula-certificate pairs. -/
private theorem foldl_inputEnd_iff (word : List Symbol) :
    word.foldl formatNext .clauseStart = .inputEnd ↔
      ∃ formula certificate, word = (Alphabet.wordPair CodeSymbol).encode
        (encoding.encode formula, certificateEncoding.encode certificate) := by
  constructor
  · exact encoded_pair_of_foldl word
  · rintro ⟨formula, certificate, rfl⟩
    exact foldl_encoded_pair formula certificate

end Parsing

/--
This Turing machine program starts at the first input symbol, reads through the entire input,
then returns to its starting cell. It leaves every symbol unchanged. State `inputEnd` means
that the input contains a correctly encoded formula and certificate; any other final state
means that the format is wrong. The program resets its state before reading.
-/
def checkFormat : Prog (TMQuery formatMachine) Unit := do [TMQuery formatMachine]
  state ←ₜ FormatState.clauseStart
  scan formatTable
  seekLeftEnd formatMachine

/--
The format checker preserves the tape, restores the head, and reports exactly the valid pairs.
-/
@[spec] theorem checkFormat_spec (word : List Symbol) (label : Option FormatState)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, cursor [] word⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      checkFormat
    ⦃ fun _ cost final => final.config.BiTape = cursor [] word ∧ final.headPos = origin ∧
        (final.config.state = some .inputEnd ↔
          ∃ formula certificate, word = (Alphabet.wordPair Problems.SAT.CodeSymbol).encode
            (Problems.SAT.encoding.encode formula,
              Problems.SAT.certificateEncoding.encode certificate)) ∧
        cost.steps = elapsed + 2 * word.length + 2 ⦄ := by
  have hformat := Parsing.foldl_inputEnd_iff word
  vcgen [checkFormat, scan_spec (tm := formatMachine) formatTable StackTape.nil StackTape.nil
      word .clauseStart origin elapsed,
    seekLeftEnd_spec (tm := formatMachine) word.reverse []
      (some (word.foldl formatTable.next .clauseStart))
      (origin + word.length) (elapsed + word.length)]
  all_goals cases word
  all_goals simp_all [formatTable, cursor, BiTape.segment]
  all_goals lia

/--
For every input word, the format checker finishes on its starting cell with the original tape.
Its state is `inputEnd` exactly when the word is an encoded formula-certificate pair. It uses
exactly twice the input length plus two head moves, whether the input is correctly written or not.
-/
theorem checkFormat_correct (word : List Symbol) (s : TMState formatMachine)
    (htape : s.config.BiTape = cursor [] word) :
    ∃ cost final, Completes checkFormat s cost final ∧
      final.config.BiTape = s.config.BiTape ∧ final.headPos = s.headPos ∧
      (final.config.state = some .inputEnd ↔
        ∃ formula certificate, word = (Alphabet.wordPair Problems.SAT.CodeSymbol).encode
          (Problems.SAT.encoding.encode formula,
            Problems.SAT.certificateEncoding.encode certificate)) ∧
      cost.steps = 2 * word.length + 2 := by
  apply Spec.completes
  vcgen [checkFormat_spec word s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all


end Algolean.Algorithms.SingleTapeTuringMachines.SAT
