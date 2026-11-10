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

The machine writes a fixed verifier description, the encoded input, and the certificate and
time bounds. Each bound is a fixed polynomial evaluated at the input length. The bound is
written as that many copies of a fixed word. The complete result is exactly the word produced
by `encodingOver`.

The verifier and both polynomials are chosen once for the whole reduction. One finite machine
handles every input length and uses the same alphabet for its input and output.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing Polynomial Problems.TMSAT
open PolynomialWriter

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

/--
This constructs a machine with a proved polynomial time bound for writing the word that
`encodingOver` assigns to its TMSAT instance. The verifier and both polynomials are fixed when
constructing the machine. The machine reads the input from its tape and computes both bounds
from the input length. It uses the same alphabet `Γ` for the input and the encoded instance.
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
