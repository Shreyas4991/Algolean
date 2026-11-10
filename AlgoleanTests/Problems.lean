/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Encodings.Basic
public import Algolean.Problems.SAT.Basic

/-!
# Checking problem statements and their encoded languages

These examples distinguish false answers from failed decoding. The SAT examples check empty
formulas, empty clauses, and the requirement that every clause share one satisfying assignment.
They also check renaming with an empty variable type and the need for injectivity.
-/

@[expose] public section

namespace AlgoleanTests.Problems

open Algolean.Problems Algolean.Problems.SAT

/-- This encoding represents a Boolean value by exactly one bit and rejects other word lengths. -/
def singleBit : Computability.Encoding Bool Bool where
  encode bit := [bit]
  decode
    | [bit] => some bit
    | _ => none
  decode_encode _ := rfl

example : [true] ∈ encodedLanguage {true} singleBit := by
  simp [encodedLanguage, singleBit]

example : [false] ∉ encodedLanguage {true} singleBit := by
  simp [encodedLanguage, singleBit]

example : [] ∉ encodedLanguage {true} singleBit :=
  not_mem_encodedLanguage_of_decode_eq_none _ _ rfl

example : [true, false] ∉ encodedLanguage {true} singleBit :=
  not_mem_encodedLanguage_of_decode_eq_none _ _ rfl

-- Empty formulas are satisfiable even when the variable type is empty.
example : ([] : CNF Empty) ∈ CNF.satisfiable := ⟨fun _ => false, rfl⟩

-- An empty clause makes a formula unsatisfiable.
example : ([[]] : CNF Empty) ∉ CNF.satisfiable := by
  simp [CNF.satisfiable, CNF.SatisfiedBy, CNF.eval, Clause.eval]

-- Each clause can be satisfied separately, but no assignment satisfies both at once.
example : ([[.pos 0], [.neg 0]] : CNF ℕ) ∉ CNF.satisfiable := by
  rintro ⟨assignment, h⟩
  cases hvalue : assignment 0 <;>
    simp [CNF.SatisfiedBy, CNF.eval, Clause.eval, hvalue] at h

-- Renaming preserves satisfiability without assuming the variable types are inhabited.
example (formula : CNF Empty) :
    formula.rename (Empty.elim : Empty → Bool) ∈ CNF.satisfiable ↔
      formula ∈ CNF.satisfiable :=
  CNF.rename_mem_satisfiable_iff formula Empty.elim (by intro name; cases name)

-- Identifying two distinct variables can turn a satisfiable formula into a contradiction.
example : ([[.pos false], [.neg true]] : CNF Bool) ∈ CNF.satisfiable ∧
    CNF.rename ([[.pos false], [.neg true]] : CNF Bool) (fun _ => ()) ∉ CNF.satisfiable := by
  constructor
  · exact ⟨Bool.not, rfl⟩
  · rintro ⟨assignment, h⟩
    cases hvalue : assignment () <;>
      simp [CNF.SatisfiedBy, CNF.eval, CNF.rename, Clause.eval, Clause.rename,
        Literal.rename, hvalue] at h

end AlgoleanTests.Problems
