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

/-- Total correctness of a fixed program, relative to an execution relation and input/output
representations. Every representing initial state must terminate, and every completed execution
must represent a valid output. Inputs outside the representation's domain are not covered. -/
structure Solves (P : Problem Input Output) (program : Program)
    (run : Program → State → Cost → State → Prop)
    (repInput : Input → State → Prop) (repOutput : Output → State → Prop) : Prop where
  /-- Every represented admissible input has a completed execution. -/
  terminates : ∀ input s, P.admissible input → repInput input s → ∃ cost t, run program s cost t
  /-- All completed executions produce a represented answer satisfying the problem. -/
  correct : ∀ input s, P.admissible input → repInput input s →
    ∀ cost t, run program s cost t → ∃ output, repOutput output t ∧ P.spec input output

/-- A terminating resource guarantee for a fixed program. The execution relation determines
what costs mean; the bound may depend on the abstract input. -/
structure RunsWithin (P : Problem Input Output) (program : Program)
    (run : Program → State → Cost → State → Prop)
    (repInput : Input → State → Prop) (bound : Input → Cost → Prop) : Prop where
  /-- Divergence cannot satisfy a resource guarantee vacuously. -/
  terminates : ∀ input s, P.admissible input → repInput input s → ∃ cost t, run program s cost t
  /-- Every completed execution satisfies the resource bound. -/
  bounded : ∀ input s, P.admissible input → repInput input s →
    ∀ cost t, run program s cost t → bound input cost

/-- Weaken a resource guarantee without changing the program or execution model. -/
theorem RunsWithin.mono {P : Problem Input Output}
    {run : Program → State → Cost → State → Prop} {repInput : Input → State → Prop}
    {bound bound' : Input → Cost → Prop}
    (h : P.RunsWithin program run repInput bound)
    (hle : ∀ input cost, bound input cost → bound' input cost) :
    P.RunsWithin program run repInput bound' :=
  ⟨h.terminates, fun input s ha hi cost t hr => hle input cost (h.bounded input s ha hi cost t hr)⟩

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
