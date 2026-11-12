/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SingleTapeTM.Encodings.SAT

/-!
# Certificates for Boolean satisfiability

`Problems.SAT.Basic` evaluates formulas using an assignment function that gives a truth value
to every variable. A Turing machine receives a finite list of symbols, so a certificate instead
lists variable names and their proposed truth values. Only names occurring in the formula need
to be listed.

`Certificate.assignment` converts this finite list into the assignment function used by
`CNF.eval` in `Basic`. If a name appears more than once, its first value is used. A name absent
from the list is assigned false. The checker uses the existing `CNF.eval` and the proofs use
the existing `CNF.satisfiable` to relate its result to satisfiability.

Every satisfiable formula has a certificate that the checker accepts. Its encoding is no longer
than the formula's encoding, counting every digit and additional symbol.
-/

@[expose] public section

namespace Algolean.Problems.SAT

open Algorithms.Alphabet

namespace Certificate

/--
This function converts a finite certificate into an assignment `Variable → Bool`, the form
already used to evaluate formulas in `Problems.SAT.Basic`. It gives each variable its first
value in the certificate, or false if the variable is not listed.
-/
def assignment : Certificate → Variable → Bool
  | [], _ => false
  | .pos key :: rest, name => if key = name then true else assignment rest name
  | .neg key :: rest, name => if key = name then false else assignment rest name

/-- To record a variable's value, use `.pos name` for true and `.neg name` for false. -/
def entry (name : Variable) (value : Bool) : Literal Variable :=
  if value then .pos name else .neg name

/-- Recording a truth value for a variable leaves its name unchanged. -/
@[simp] theorem name_entry (name : Variable) (value : Bool) : (entry name value).name = name := by
  cases value <;> rfl

/--
Given an assignment function as used in `Problems.SAT.Basic`, this constructs a finite
certificate by listing the value of each variable whenever it occurs in the formula.
-/
def ofAssignment (formula : CNF Variable) (assignment : Variable → Bool) : Certificate :=
  formula.flatten.map (fun literal => entry literal.name (assignment literal.name))

/--
If listed names receive their values from one assignment, looking up any of them gives that value.
-/
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

/--
Every variable appearing in the formula receives its original value in the constructed certificate.
-/
theorem assignment_ofAssignment {formula : CNF Variable} (values : Variable → Bool)
    {literal : Literal Variable} (h : literal ∈ formula.flatten) :
    assignment (ofAssignment formula values) literal.name = values literal.name := by
  have hname : literal.name ∈ formula.flatten.map Literal.name := List.mem_map_of_mem h
  simpa only [ofAssignment, List.map_map, Function.comp_def] using assignment_map_entry values hname

/-- Choosing true or false for each listed variable does not change the number of symbols needed. -/
theorem length_map_entry (literals : List (Literal Variable)) (values : Variable → Bool) :
    (clauseEncoding.encode
      (literals.map (fun literal => entry literal.name (values literal.name)))).length =
        (clauseEncoding.encode literals).length := by
  simp [length_clauseEncoding, List.map_map, Function.comp_def]

/-- Joining two certificates saves one symbol because the combined list needs only one ending. -/
theorem length_append (first second : Certificate) :
    (clauseEncoding.encode (first ++ second)).length + 1 =
      (clauseEncoding.encode first).length + (clauseEncoding.encode second).length := by
  simp only [length_clauseEncoding, List.map_append, List.sum_append]
  lia

/-- The constructed certificate's encoding is no longer than the formula's encoding. -/
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

/--
The formula has the same truth value under the constructed certificate and the original assignment.
-/
theorem eval_certificate_ofAssignment (formula : CNF Variable) (values : Variable → Bool) :
    formula.eval (Certificate.assignment (Certificate.ofAssignment formula values)) =
      formula.eval values :=
  formula.eval_eq_of_agree _ _ (fun _ h => Certificate.assignment_ofAssignment values h)

/--
The checker reads the encoded formula and the proposed variable values, then returns true if
every clause is true. It returns false if either input is incorrectly formatted.
-/
def verify (word certificate : List CodeSymbol) : Bool :=
  match encoding.decode word, certificateEncoding.decode certificate with
  | some formula, some entries => formula.eval (Certificate.assignment entries)
  | _, _ => false

/--
Using a certificate built from an assignment gives the same result as evaluating with it directly.
-/
theorem verify_ofAssignment (formula : CNF Variable) (values : Variable → Bool) :
    verify (encoding.encode formula)
        (certificateEncoding.encode (Certificate.ofAssignment formula values)) =
      formula.eval values := by
  simp only [verify, Computability.Encoding.decode_encode, eval_certificate_ofAssignment]

/-- If the checker returns true, the supplied formula is correctly encoded and satisfiable. -/
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

/--
A supplied list encodes a satisfiable formula exactly when some certificate makes the checker
return true and uses no more symbols than that list.
-/
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
