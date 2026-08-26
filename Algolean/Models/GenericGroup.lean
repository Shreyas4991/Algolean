/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.QueryModel
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Order.Monoid.Defs

/-!
# Query Type for Generic Group Algorithms

In this file we define a query type `GroupQuery` for algorithms in the *generic group model*. A
program holds group elements but cannot compute with them: `add x y` asks an oracle for the sum of
two elements it holds, `neg x` for the negation of one, and `eq x y` for the single bit saying
whether two of them are equal.

## Costs

`GroupCosts` counts `add`, `neg` and `eq` queries separately, since the two kinds are charged
differently: the classical analysis of a generic group algorithm counts only the element-producing
queries, which is `GroupCosts.groupOps`, and treats comparison as free.

## References

Ueli Maurer, *Abstract Models of Computation in Cryptography*, IMA 2005.

Victor Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, EUROCRYPT 1997.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog

universe u

variable {V G α β ι : Type u}

/-!
## The query type
-/

/--
The queries of the generic group model over elements of type `V`. `add x y` asks the oracle for
the sum of `x` and `y`, `neg x` for the negation of `x`, and `eq x y` whether `x` and `y` are
equal.
-/
inductive GroupQuery (V : Type u) : Type u → Type (u + 1) where
  /-- Ask for the sum of `x` and `y`. -/
  | add (x y : V) : GroupQuery V V
  /-- Ask for the negation of `x`. -/
  | neg (x : V) : GroupQuery V V
  /-- Ask whether `x` and `y` are equal. -/
  | eq (x y : V) : GroupQuery V (ULift.{u} Bool)

/-!
## Costs
-/

/-- The cost structure of the generic group model. -/
@[ext, grind]
structure GroupCosts where
  /-- the number of calls to the `add` query -/
  adds : ℕ
  /-- the number of calls to the `neg` query -/
  negs : ℕ
  /-- the number of calls to the `eq` query -/
  eqs : ℕ

/-- Equivalence between `GroupCosts` and a product type. -/
@[simps]
def GroupCosts.equivProd : GroupCosts ≃ (ℕ × ℕ × ℕ) where
  toFun gc := (gc.adds, gc.negs, gc.eqs)
  invFun triple := ⟨triple.1, triple.2.1, triple.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace GroupCosts

@[simps, grind]
instance : Zero GroupCosts := ⟨0, 0, 0⟩

@[simps]
instance : LE GroupCosts where
  le gc₁ gc₂ := gc₁.adds ≤ gc₂.adds ∧ gc₁.negs ≤ gc₂.negs ∧ gc₁.eqs ≤ gc₂.eqs

instance : LT GroupCosts where
  lt gc₁ gc₂ := gc₁ ≤ gc₂ ∧ ¬gc₂ ≤ gc₁

@[grind]
instance : PartialOrder GroupCosts :=
  fast_instance% GroupCosts.equivProd.injective.partialOrder _ .rfl .rfl

@[simps (attr := grind =)]
instance : Add GroupCosts where
  add gc₁ gc₂ := ⟨gc₁.adds + gc₂.adds, gc₁.negs + gc₂.negs, gc₁.eqs + gc₂.eqs⟩

@[simps]
instance : SMul ℕ GroupCosts where
  smul n gc := ⟨n • gc.adds, n • gc.negs, n • gc.eqs⟩

instance : AddCommMonoid GroupCosts :=
  fast_instance%
    GroupCosts.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

lemma le_iff {gc₁ gc₂ : GroupCosts} :
    gc₁ ≤ gc₂ ↔ gc₁.adds ≤ gc₂.adds ∧ gc₁.negs ≤ gc₂.negs ∧ gc₁.eqs ≤ gc₂.eqs :=
  Iff.rfl

instance : IsOrderedAddMonoid GroupCosts where
  add_le_add_left _ _ h _ := by
    simp only [le_iff, add_adds, add_negs, add_eqs] at h ⊢
    lia

/--
The queries that produce a new group element. This is the count a classical generic group bound
speaks about: equality tests are free to it, and the group operations are not.
-/
@[simp, grind] def groupOps (gc : GroupCosts) : ℕ := gc.adds + gc.negs

@[simp] lemma groupOps_zero : (0 : GroupCosts).groupOps = 0 := rfl

@[grind =] lemma groupOps_add (gc₁ gc₂ : GroupCosts) :
    (gc₁ + gc₂).groupOps = gc₁.groupOps + gc₂.groupOps := by
  simp only [groupOps, add_adds, add_negs]; lia

lemma groupOps_le_groupOps {gc₁ gc₂ : GroupCosts} (h : gc₁ ≤ gc₂) :
    gc₁.groupOps ≤ gc₂.groupOps := by
  obtain ⟨h₁, h₂, -⟩ := le_iff.mp h
  simp only [groupOps]
  lia

end GroupCosts

/-- The cost of a single query: one unit in the component naming its operation. -/
@[simp, grind] def GroupQuery.charge (q : GroupQuery V ι) : GroupCosts :=
  match q with
  | .add _ _ => ⟨1, 0, 0⟩
  | .neg _ => ⟨0, 1, 0⟩
  | .eq _ _ => ⟨0, 0, 1⟩

/-!
## The oracle is the group

The three operations are answered by the `AddCommGroup` and `DecidableEq` instances of the group
the program is run in.
-/

/-- The answer the group `G` gives to a single query. -/
@[simp, grind] def GroupQuery.answer [AddCommGroup G] [DecidableEq G] : GroupQuery G ι → ι
  | .add x y => x + y
  | .neg x => -x
  | .eq x y => ULift.up (decide (x = y))

/--
The group read as a `Model` of `GroupQuery G`: it answers a query with `GroupQuery.answer` and
charges it `GroupQuery.charge`, so `GroupProg.eval` and `GroupProg.cost` below are the `Prog.eval`
and `Prog.time` of `Algolean.QueryModel`.
-/
def groupModel (G : Type u) [AddCommGroup G] [DecidableEq G] :
    Model (GroupQuery G) GroupCosts where
  evalQuery q := q.answer
  cost q := q.charge

@[simp, grind =] lemma groupModel_evalQuery [AddCommGroup G] [DecidableEq G] (q : GroupQuery G ι) :
    (groupModel G).evalQuery q = q.answer := rfl

@[simp, grind =] lemma groupModel_cost [AddCommGroup G] [DecidableEq G] (q : GroupQuery G ι) :
    (groupModel G).cost q = q.charge := rfl

/-- Register `groupModel` as the default model for `GroupQuery`, so the global
`WP (Prog (GroupQuery G)) .pure` / `HasHandler` instances fire and `Triple`/`mvcgen` reasoning
works on generic group programs out of the box. -/
instance [AddCommGroup G] [DecidableEq G] : HasModel (GroupQuery G) GroupCosts where
  model := groupModel G

/-- The default generic group model unfolds to `groupModel`. -/
@[simp, grind =] theorem GroupQuery.hasModel_model [AddCommGroup G] [DecidableEq G] :
    (HasModel.model : Model (GroupQuery G) GroupCosts) = groupModel G := rfl

/-!
## Programs
-/

/-- A generic group program over elements of type `V`, returning an `α`. -/
abbrev GroupProg (V α : Type u) : Type (u + 1) := Prog (GroupQuery V) α

namespace GroupProg

/-!
### The observables of a run

Everything below is stated for the ambient `AddCommGroup` instance, and a lower bound is free to
supply an instance of its own making.
-/

section Run

variable [AddCommGroup G] [DecidableEq G]

/-- What a program computes, run in the group `G`. -/
abbrev eval (oa : GroupProg G α) : α := Prog.eval oa (groupModel G)

/-- The queries a program issues, tallied by operation. -/
abbrev cost (oa : GroupProg G α) : GroupCosts := Prog.time oa (groupModel G)

/-- The element-producing queries a program issues: the count a classical generic group bound
speaks about. -/
abbrev groupOps (oa : GroupProg G α) : ℕ := (cost oa).groupOps

@[grind =] lemma eval_liftBind (q : GroupQuery G ι) (cont : ι → GroupProg G α) :
    eval (FreeM.liftBind q cont) = eval (cont q.answer) :=
  Prog.eval_liftBind q cont (groupModel G)

@[grind =] lemma cost_liftBind (q : GroupQuery G ι) (cont : ι → GroupProg G α) :
    cost (FreeM.liftBind q cont) = q.charge + cost (cont q.answer) :=
  Prog.time_liftBind q cont (groupModel G)

@[grind =] lemma groupOps_liftBind (q : GroupQuery G ι) (cont : ι → GroupProg G α) :
    groupOps (FreeM.liftBind q cont) = q.charge.groupOps + groupOps (cont q.answer) := by
  rw [groupOps, cost_liftBind, GroupCosts.groupOps_add, groupOps]

/-!
### The queries as Hoare specs

`groupModel` is the registered default model of `GroupQuery`, so the weakest-precondition
instances of `Algolean.QueryModel` fire on `GroupProg`. The three specs below are all that stands
between that and `mvcgen`: the generic `Spec.query` discharges a lifted query but leaves the
model's answer unevaluated, so these take priority over it and read that answer back in `G`.

Cost is not in view here. The `.pure` post-shape sees only the returned value, and the query counts
remain the business of `cost` above.
-/

section Specs

open Std.Do

/-- The oracle answers `add x y` with the sum of `x` and `y`. -/
@[spec high]
theorem add_spec (x y : G) {Q' : PostCond G .pure} :
    Triple (GroupQuery.add x y : GroupProg G G) (Q'.1 (x + y)) Q' :=
  Spec.query (Cost := GroupCosts) (GroupQuery.add x y)

/-- The oracle answers `neg x` with the negation of `x`. -/
@[spec high]
theorem neg_spec (x : G) {Q' : PostCond G .pure} :
    Triple (GroupQuery.neg x : GroupProg G G) (Q'.1 (-x)) Q' :=
  Spec.query (Cost := GroupCosts) (GroupQuery.neg x)

/-- The oracle answers `eq x y` with the lifted decision of `x = y`. -/
@[spec high]
theorem eq_spec (x y : G) {Q' : PostCond (ULift Bool) .pure} :
    Triple (GroupQuery.eq x y : GroupProg G (ULift Bool))
      (Q'.1 (ULift.up (decide (x = y)))) Q' :=
  Spec.query (Cost := GroupCosts) (GroupQuery.eq x y)

/-- A triple with a trivial precondition is a statement about what the program `eval`uates to in
`G`, which is the form the rest of the development is written in. -/
theorem eval_of_triple {oa : GroupProg G α} {φ : α → Prop}
    (h : ⦃⌜True⌝⦄ oa ⦃⇓r => ⌜φ r⌝⦄) : φ (eval oa) :=
  Algolean.Algorithms.eval_of_triple (Cost := GroupCosts) h

end Specs

end Run

end GroupProg

/--
A generic group algorithm taking `n` inputs: a program uniformly in the type of group elements,
which also receives the order of the group it is run in. One fixed program text therefore has to
serve every group of that order, which is what a statement about a `GroupAlg` exploits.
-/
abbrev GroupAlg (n : ℕ) (α : Type) : Type 1 := ∀ V : Type, ℕ → (Fin n → V) → GroupProg V α

end Algorithms

end Algolean
