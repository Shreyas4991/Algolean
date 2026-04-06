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

instance [DecidableEq α] : DecidableEq (List α) := by infer_instance
/--
A generic circuit type for unbounded fan in circuits. This can be instantiated to
arithmetic as well as boolean circuits. Note that despite the inductive structure
resembling formulas rather than circuits, we call these circuits, since we in accounting size,
we can both count the size of the formula tree and corresponding circuit DAG. Thus we assign
the more generic name `Circuit`.
-/
inductive Circuit (α : Type u) : Type u → Type u where
  /-- Construct a leaf `const` node -/
  | const (x : α) : Circuit α α
  /-- Construct an `add` node, the addition/or/xor gate -/
  | add (lc : List <| Circuit α α) : Circuit α α
  /-- Construct a `mul` node, the multiplication/and gate -/
  | mul (lc : List <| Circuit α α) : Circuit α α
  /-- Construct a `neg` node, the negation/not gate -/
  | neg (c : Circuit α α) : Circuit α α

mutual

  /-- one part of a mutually inductive definition of DecidableEq (Circuit α α) -/
  def circuitDecEq [DecidableEq α] : (c₁ c₂ : Circuit α α) → Decidable (c₁ = c₂)
    | .const x, .const y =>
        match decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
    | .const _, .add _ => isFalse (by intro h; cases h)
    | .const _, .mul _ => isFalse (by intro h; cases h)
    | .const _, .neg _ => isFalse (by intro h; cases h)
    | .add _, .const _ => isFalse (by intro h; cases h)
    | .add xs, .add ys =>
        match listCircuitDecEq xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
    | .add _, .mul _ => isFalse (by intro h; cases h)
    | .add _, .neg _ => isFalse (by intro h; cases h)
    | .mul _, .const _ => isFalse (by intro h; cases h)
    | .mul _, .add _ => isFalse (by intro h; cases h)
    | .mul xs, .mul ys =>
        match listCircuitDecEq xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)
    | .mul _, .neg _ => isFalse (by intro h; cases h)
    | .neg _, .const _ => isFalse (by intro h; cases h)
    | .neg _, .add _ => isFalse (by intro h; cases h)
    | .neg _, .mul _ => isFalse (by intro h; cases h)
    | .neg x, .neg y =>
        match circuitDecEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro hc; cases hc; exact h rfl)

  /-- Decidable Equality of lists of Circuit α α -/
  def listCircuitDecEq [DecidableEq α] :
      (xs ys : List (Circuit α α)) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | x :: xs, y :: ys =>
        match circuitDecEq x y, listCircuitDecEq xs ys with
        | isTrue hx, isTrue hxs => isTrue (by cases hx; cases hxs; rfl)
        | isFalse hx, _ => isFalse (by intro h; cases h; exact hx rfl)
        | _, isFalse hxs => isFalse (by intro h; cases h; exact hxs rfl)
end

instance [DecidableEq α] : DecidableEq (Circuit α α) := circuitDecEq

/--
`CircuitCosts` is the cost structure for circuits that stores the `size` and `depth`
of a circuit
-/
structure CircuitCosts where
  /-- The `depth` of a circuit -/
  depth : ℕ
  /-- The circuit `size` of a circuit. Counts identical nodes only once -/
  circuitSize : ℕ
  /-- The formula `size` of a circuit. Counts every node in the formula-tree of the circuit
  separately -/
  formulaSize : ℕ
deriving BEq, DecidableEq

instance : Zero CircuitCosts where
  zero := ⟨0,0,0⟩

instance : Add CircuitCosts where
  add x y := ⟨x.1 + y.1, x.2 + y.2, x.3 + y.3⟩

instance : AddZero CircuitCosts where

/-- Evaluate a circuit -/
@[simp, grind]
def Circuit.circEval {α : Type u} [Zero α] [One α] [Add α] [Mul α] [Neg α]
    (c : Circuit α ι) : ι :=
  match c with
  | .const x => x
  | .add cl => List.sum (List.map circEval cl)
  | .mul cl => List.prod (List.map circEval cl)
  | .neg c => - circEval c

mutual
  /-- Compute the depth of a circuit -/
  @[simp, grind]
  def Circuit.depthOf (q : Circuit α β) :=
    match q with
    | .const _ => 0
    | .add cl => 1 + depthOfList cl
    | .mul cl => 1 + depthOfList cl
    | .neg c => 1 + Circuit.depthOf c

  /-- Compute the maximum depth of a list of circuits. -/
  @[simp, grind]
  def depthOfList : List (Circuit α α) → ℕ
    | [] => 0
    | c :: cs => max c.depthOf (depthOfList cs)
end

mutual
  /-- Compute the formula size of a circuit -/
  @[simp, grind]
  def Circuit.formulaSize (q : Circuit α β) :=
    match q with
    | .const _ => 1
    | .add cl => 1 + formulaSizeList cl
    | .mul cl => 1 + formulaSizeList cl
    | .neg c => 1 + Circuit.formulaSize c

  /-- Compute the total formula size of a list of circuits. -/
  @[simp, grind]
  def formulaSizeList : List (Circuit α α) → ℕ
    | [] => 0
    | c :: cs => c.formulaSize + formulaSizeList cs
end

mutual
  /-- Compute the set of subcircuits -/
  @[simp, grind]
  def Circuit.subcircuits {α} [DecidableEq α] (c : Circuit α α) :
      Finset (Circuit α α) :=
    insert c <|
      match c with
      | .const _ => {}
      | .add cl => subcircuitsList cl
      | .mul cl => subcircuitsList cl
      | .neg c' => c'.subcircuits

  /-- Compute the union of the subcircuits of a list of circuits. -/
  @[simp, grind]
  def subcircuitsList {α} [DecidableEq α] : List (Circuit α α) → Finset (Circuit α α)
    | [] => {}
    | c :: cs => c.subcircuits ∪ subcircuitsList cs
end

/-- Compute circuit size, that is size of the circuit without double counting identical nodes -/
@[simp, grind]
def Circuit.circuitSize [DecidableEq α] (c : Circuit α β) :=
  match c with
  | .const x => (subcircuits (.const x)).card
  | .add cl => (subcircuits (.add cl)).card
  | .mul cl => (subcircuits (.mul cl)).card
  | .neg c' => (subcircuits (.neg c')).card

@[simp]
lemma circuitSize_eq_subcircuits_card (c : Circuit Bool Bool) :
    c.subcircuits.card = c.circuitSize := by
  cases c <;> simp [Circuit.circuitSize, Circuit.subcircuits]

/--
A model for the circuit query
-/
@[simps, grind]
def circModel [Zero α] [One α] [Add α] [Mul α] [Neg α] [DecidableEq α] :
    Model (Circuit α) CircuitCosts where
  evalQuery q := q.circEval
  cost q := ⟨q.depthOf, q.circuitSize, q.formulaSize⟩

end Prog

end Algorithms

end Algolean
