/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Verification

/-!
# Checking SAT encodings and certificates

* The flat alphabet uses six markers with distinct roles.
* Empty formulas and empty clauses retain their different meanings.
* Malformed words are rejected, including words with trailing data.
* Certificates use one assignment consistently across all clauses.
-/

@[expose] public section

namespace AlgoleanTests.SAT

open Algolean.Problems.SAT

-- An empty formula consists of its end marker.
example : encoding.encode [] = [(.inr 5 : CodeSymbol)] := by decide +kernel

-- An empty clause has a clause end, a clause separator, and a formula end.
example : encoding.encode [[]] = [(.inr 3 : CodeSymbol), .inr 4, .inr 5] := by decide +kernel

-- Markers zero and one are signs. Marker two ends a literal; markers three to five frame clauses.
example : encoding.encode [[.pos [false, true], .neg [true]]] =
    [(.inr 0 : CodeSymbol), .inl false, .inl true, .inr 2, .inr 1, .inl true,
      .inr 2, .inr 3, .inr 4, .inr 5] := by decide +kernel

-- The formula decoder rejects a missing end marker.
example : encoding.decode [] = none := by decide +kernel

-- Data after the formula end is rejected.
example : encoding.decode [(.inr 5 : CodeSymbol), .inl true] = none := by decide +kernel

-- Every formula survives encoding and decoding, including all binary variable names.
example (formula : CNF Variable) : encoding.decode (encoding.encode formula) = some formula := by
  simp

-- An empty assignment suffices for the empty conjunction.
example : verify (encoding.encode []) (certificateEncoding.encode []) = true := by decide +kernel

-- No assignment satisfies an empty clause.
example (certificate : List CodeSymbol) : verify (encoding.encode [[]]) certificate = false := by
  cases hc : certificateEncoding.decode certificate <;>
    simp [verify, hc, CNF.eval, Clause.eval]

-- Contradictory entries cannot give the same variable different values in different clauses.
example : verify (encoding.encode [[.pos [true]], [.neg [true]]])
    (certificateEncoding.encode [.pos [true], .neg [true]]) = false := by decide +kernel

-- Distinct binary words name distinct variables, even when one begins with an extra zero.
example : verify (encoding.encode [[.pos [true]], [.neg [false, true]]])
    (certificateEncoding.encode [.pos [true], .neg [false, true]]) = true := by decide +kernel

-- The certificate bound applies to the actual supplied formula word.
example (word : List CodeSymbol) (h : word ∈ language) :
    ∃ certificate : List CodeSymbol,
      certificate.length ≤ word.length ∧ verify word certificate = true :=
  (certificate_characterization word).mp h

end AlgoleanTests.SAT
