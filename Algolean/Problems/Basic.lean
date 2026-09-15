/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Logic.Basic

/-!
# Model-independent computational problems

`Problem Input Output` specifies admissible inputs and the outputs allowed for each input.
The specification is relational: an input may admit several outputs. No representation,
algorithm, execution model, or resource bound is part of the problem itself.

Correctness will require the specification only on admissible inputs. The structure does not
assert existence or uniqueness of valid outputs, or the existence of an algorithm.
`Problem.restrict` strengthens the input precondition without changing the output relation.
-/

@[expose] public section

namespace Algolean

/-- An input/output specification independent of any computational model. -/
structure Problem (Input : Type u) (Output : Type v) where
  /-- Inputs on which an implementation must satisfy the specification. -/
  admissible : Input → Prop
  /-- The valid outputs for each admissible input. -/
  spec : Input → Output → Prop

namespace Problem

/-- Restrict a problem to inputs satisfying an additional precondition. -/
def restrict (P : Problem Input Output) (precondition : Input → Prop) : Problem Input Output where
  admissible input := P.admissible input ∧ precondition input
  spec := P.spec

@[simp, grind =] theorem restrict_admissible (P : Problem Input Output)
    (precondition : Input → Prop) (input : Input) :
    (P.restrict precondition).admissible input ↔ P.admissible input ∧ precondition input := Iff.rfl

@[simp, grind =] theorem restrict_spec (P : Problem Input Output)
    (precondition : Input → Prop) (input : Input) (output : Output) :
    (P.restrict precondition).spec input output ↔ P.spec input output := Iff.rfl

end Problem

end Algolean
