/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Alex Meiburg
-/

module

public import Algolean.QueryModel
public import Mathlib.Algebra.Lie.OfAssociative

@[expose] public section

namespace Algolean

namespace Algorithms

namespace Prog

/--
A generic circuit type for fan-in-2 circuits. This can be instantiated to
arithmetic as well as boolean circuits. Note that despite the inductive structure
resembling formulas rather than circuits, we call these circuits, since we in accounting size,
we can both count the size of the formula tree and corresponding circuit DAG. Thus we assign
the more generic name `FanInTwoCircuit`.
-/
inductive FanInTwoCircuit (α : Type u) : Type u → Type u where
  /-- Construct a leaf `const` node -/
  | const (x : α) : FanInTwoCircuit α α
  /-- Construct an `add` node, the addition/or/xor gate -/
  | add (c₁ c₂ : FanInTwoCircuit α α) : FanInTwoCircuit α α
  /-- Construct a `mul` node, the multiplication/and gate -/
  | mul (c₁ c₂ : FanInTwoCircuit α α) : FanInTwoCircuit α α
  /-- Construct a `neg` node, the negation/not gate -/
  | neg (c : FanInTwoCircuit α α) : FanInTwoCircuit α α
deriving DecidableEq

/--
`FanInTwoCircuitCosts` is the cost structure for circuits that stores the `size` and `depth`
of a circuit
-/
structure FanInTwoCircuitCosts where
  /-- The `depth` of a circuit -/
  depth : ℕ
  /-- The circuit `size` of a circuit. Counts identical nodes only once -/
  circuitSize : ℕ
  /-- The formula `size` of a circuit. Counts every node in the formula-tree of the circuit
  separately -/
  formulaSize : ℕ
deriving BEq, DecidableEq

instance : Zero FanInTwoCircuitCosts where
  zero := ⟨0,0,0⟩

instance : Add FanInTwoCircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2, x.3 + y.3⟩

instance : AddZero FanInTwoCircuitCosts where

/-- Evaluate a circuit -/
@[simp, grind]
def FanInTwoCircuit.circEval {α : Type u} [Add α] [Mul α] [Neg α] (c : FanInTwoCircuit α ι) : ι :=
  match c with
  | .const x => x
  | .add c₁ c₂ => circEval c₁ + circEval c₂
  | .mul c₁ c₂ => circEval c₁ * circEval c₂
  | .neg c => - circEval c

/-- Compute the depth of a circuit -/
@[simp, grind]
def FanInTwoCircuit.depthOf (q : FanInTwoCircuit α β) :=
  match q with
  | .const c => 0
  | .add c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .mul c₁ c₂ => 1 + max (depthOf c₁) (depthOf c₂)
  | .neg c => 1 + depthOf c

/-- Compute the formula size of a circuit -/
@[simp, grind]
def FanInTwoCircuit.formulaSize (q : FanInTwoCircuit α β) :=
  match q with
  | .const c => 1
  | .add c₁ c₂ => 1 + (formulaSize c₁) + (formulaSize c₂)
  | .mul c₁ c₂ => 1 + (formulaSize c₁) + (formulaSize c₂)
  | .neg c => 1 + (formulaSize c)

/-- Compute the set of subcircuits -/
@[simp, grind]
def FanInTwoCircuit.subcircuits {α} [DecidableEq α] (c : FanInTwoCircuit α α) :
    Finset (FanInTwoCircuit α α) :=
  insert c (
    match c with
    | .const _ => {}
    | .add c₁ c₂ => c₁.subcircuits ∪ c₂.subcircuits
    | .mul c₁ c₂ => c₁.subcircuits ∪ c₂.subcircuits
    | .neg c' => c'.subcircuits
)

/-- Compute circuit size, that is size of the circuit without double counting identical nodes -/
@[simp, grind]
def FanInTwoCircuit.circuitSize [DecidableEq α] (c : FanInTwoCircuit α β) :=
  match c with
  | .const x => (subcircuits (.const x)).card
  | .add c₁ c₂ => (subcircuits (.add c₁ c₂)).card
  | .mul c₁ c₂ => (subcircuits (.mul c₁ c₂)).card
  | .neg c' => (subcircuits (.neg c')).card

@[simp]
lemma circuitSize_eq_subcircuits_card (c : FanInTwoCircuit Bool Bool) :
    c.subcircuits.card = c.circuitSize := by
  cases c <;> simp [FanInTwoCircuit.circuitSize, FanInTwoCircuit.subcircuits]

/--
A model for the circuit query
-/
@[simps, grind]
def circModel [Add α] [Mul α] [Neg α] [DecidableEq α] :
    Model (FanInTwoCircuit α) FanInTwoCircuitCosts where
  evalQuery q := q.circEval
  cost q := ⟨q.depthOf, q.circuitSize, q.formulaSize⟩

end Prog

end Algorithms

end Algolean
