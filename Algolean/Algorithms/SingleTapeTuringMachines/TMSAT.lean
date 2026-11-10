/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Serialization
public import Algolean.Problems.TMSAT.Serialization

/-!
# Writing TMSAT instances in polynomial time

The serializer writes a fixed verifier description, the encoded input, and unary certificate
and time bounds. Both bounds are fixed polynomials evaluated at the input length. Its output
is exactly the canonical TMSAT encoding over the input alphabet.

The verifier and both polynomials are chosen once for the entire reduction. One finite machine
runs on every input; it computes the lengths of the unary fields from the word on its tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing Polynomial Problems.TMSAT
open PolynomialWriter

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
This is a polynomial-time Turing machine that writes the canonical TMSAT instance for
its input. The verifier and both polynomials are fixed when constructing the machine and are
independent of every runtime input. The tape alphabet is the same `Γ` used for the input,
certificates, and encoded instances.
-/
noncomputable def tmsatSerializer (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (m t : Polynomial Nat) :
    TMQuery.PolyTimeComputable (fun input =>
      encodingOver.encode (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
        Instance Γ)) := by
  classical
  let fields := [(Serialization.unary (Γ := Γ), m), (Serialization.separator (Γ := Γ), 1),
    (Serialization.unary (Γ := Γ), t)]
  have heq : (fun input : List Γ => Serialization.header verifier ++
      input.flatMap Serialization.symbolCode ++ Serialization.ending ++
        fieldsWord fields input.length) =
      (fun input => encodingOver.encode
        (⟨verifier, input, m.eval input.length, t.eval input.length⟩ : Instance Γ)) := by
    funext input
    rw [Serialization.encode_instance]
    simp [fields, fieldsWord, List.append_assoc]
  rw [← heq]
  exact serializerComputer Serialization.symbolCode Serialization.symbolCode_ne_nil
    (Serialization.header verifier) Serialization.ending fields

end Algolean.Algorithms.SingleTapeTuringMachines
