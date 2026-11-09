/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Encoding
public import Algolean.Complexity.PolytimeBasicClasses

/-!
# Certificates for Boolean satisfiability

An assignment certificate lists binary variable names and their assigned values. The first
entry for a name determines its value; names absent from the certificate are assigned false.
The checker evaluates every clause using that single assignment.

Every satisfiable encoded formula has an accepting certificate no longer than the formula word.
This bound counts the supplied word's symbols rather than the numeric values of variable names.
-/

@[expose] public section

namespace Algolean.Problems.SAT

open Algorithms.Alphabet

namespace Certificate

/-- The first certificate entry for a variable supplies its value; absent names receive false. -/
def assignment : Certificate → Variable → Bool
  | [], _ => false
  | .pos key :: rest, name => if key = name then true else assignment rest name
  | .neg key :: rest, name => if key = name then false else assignment rest name

/-- This entry records the supplied value of a binary variable name. -/
def entry (name : Variable) (value : Bool) : Literal Variable :=
  if value then .pos name else .neg name

/-- An assignment entry retains its variable name, regardless of the assigned value. -/
@[simp] theorem name_entry (name : Variable) (value : Bool) : (entry name value).name = name := by
  cases value <;> rfl

/-- This certificate records the assignment for each variable occurrence in the formula. -/
def ofAssignment (formula : CNF Variable) (assignment : Variable → Bool) : Certificate :=
  formula.flatten.map (fun literal => entry literal.name (assignment literal.name))

/-- Looking up a name in a list of entries from one assignment recovers its assigned value. -/
theorem assignment_map_entry {names : List Variable} (values : Variable → Bool)
    {name : Variable} (h : name ∈ names) :
    assignment (names.map (fun key => entry key (values key))) name = values name := by
  induction names with
  | nil => simp at h
  | cons key rest ih =>
    by_cases heq : key = name
    · subst key
      cases hvalue : values name <;> simp [entry, assignment, hvalue]
    · have hrest : name ∈ rest := by simpa [Ne.symm heq] using h
      cases hvalue : values key <;> simpa [entry, assignment, hvalue, heq] using ih hrest

/-- The constructed certificate agrees with the original assignment on every literal occurrence. -/
theorem assignment_ofAssignment {formula : CNF Variable} (values : Variable → Bool)
    {literal : Literal Variable} (h : literal ∈ formula.flatten) :
    assignment (ofAssignment formula values) literal.name = values literal.name := by
  have hname : literal.name ∈ formula.flatten.map Literal.name := List.mem_map_of_mem h
  simpa only [ofAssignment, List.map_map, Function.comp_def] using assignment_map_entry values hname

/-- Replacing each sign by its assignment value preserves the encoded certificate length. -/
theorem length_map_entry (literals : List (Literal Variable)) (values : Variable → Bool) :
    (clauseEncoding.encode
      (literals.map (fun literal => entry literal.name (values literal.name)))).length =
        (clauseEncoding.encode literals).length := by
  simp [length_clauseEncoding, List.map_map, Function.comp_def]

/-- Joining two encoded signed lists shares their final end marker. -/
theorem length_append (first second : Certificate) :
    (clauseEncoding.encode (first ++ second)).length + 1 =
      (clauseEncoding.encode first).length + (clauseEncoding.encode second).length := by
  simp only [length_clauseEncoding, List.map_append, List.sum_append]
  lia

/-- The constructed certificate fits within the encoded formula, even when names are very long. -/
theorem length_ofAssignment_le (formula : CNF Variable) (values : Variable → Bool) :
    (certificateEncoding.encode (ofAssignment formula values)).length ≤
      (encoding.encode formula).length := by
  rw [length_certificateEncoding, ofAssignment, length_map_entry]
  induction formula with
  | nil => simp
      [clauseEncoding, encoding, Computability.Encoding.strict, Computability.Encoding.list]
  | cons clause rest ih =>
    have happend := length_append clause rest.flatten
    simp only [List.flatten_cons, length_encoding, List.map_cons, List.sum_cons] at ih ⊢
    lia

end Certificate

/-- Checking the constructed certificate gives the same formula value as its original assignment. -/
theorem eval_certificate_ofAssignment (formula : CNF Variable) (values : Variable → Bool) :
    formula.eval (Certificate.assignment (Certificate.ofAssignment formula values)) =
      formula.eval values :=
  formula.eval_eq_of_agree _ _ (fun _ h => Certificate.assignment_ofAssignment values h)

/-- The checker decodes the formula and signed assignment list, rejecting any malformed field. -/
def verify (word certificate : List CodeSymbol) : Bool :=
  match encoding.decode word, certificateEncoding.decode certificate with
  | some formula, some entries => formula.eval (Certificate.assignment entries)
  | _, _ => false

/-- Every encoded satisfying assignment makes the checker return true. -/
theorem verify_ofAssignment (formula : CNF Variable) (values : Variable → Bool) :
    verify (encoding.encode formula)
        (certificateEncoding.encode (Certificate.ofAssignment formula values)) =
      formula.eval values := by
  simp only [verify, Computability.Encoding.decode_encode, eval_certificate_ofAssignment]

/-- An accepting certificate supplies a satisfying assignment for the decoded formula. -/
theorem mem_language_of_verify {word certificate : List CodeSymbol}
    (h : verify word certificate = true) : word ∈ language := by
  cases hf : encoding.decode word with
  | none => simp [verify, hf] at h
  | some formula =>
    cases hc : certificateEncoding.decode certificate with
    | none => simp [verify, hc] at h
    | some entries =>
      rw [decode_encoding_eq_some_iff.mp hf, encode_mem_language]
      exact ⟨Certificate.assignment entries, by simpa [verify, hf, hc, CNF.SatisfiedBy] using h⟩

/-- The encoded SAT language has accepting certificates bounded by the supplied formula length. -/
theorem certificate_characterization (word : List CodeSymbol) :
    word ∈ language ↔ ∃ certificate : List CodeSymbol,
      certificate.length ≤ word.length ∧ verify word certificate = true := by
  constructor
  · intro h
    cases hf : encoding.decode word with
    | none => simp [language, encodedLanguage, hf] at h
    | some formula =>
      have hs := (mem_encodedLanguage_iff_of_decode_eq_some CNF.satisfiable encoding hf).mp h
      obtain ⟨values, hvalues⟩ := hs
      rw [decode_encoding_eq_some_iff.mp hf]
      exact ⟨certificateEncoding.encode (Certificate.ofAssignment formula values),
        Certificate.length_ofAssignment_le formula values,
        (verify_ofAssignment formula values).trans hvalues⟩
  · rintro ⟨certificate, _, h⟩
    exact mem_language_of_verify h

end Algolean.Problems.SAT
