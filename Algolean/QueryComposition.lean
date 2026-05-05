/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas, Eric Wieser
-/

module

--public import Cslib
public import Algolean.QueryModel

@[expose] public section

/-
# Query model Composition

In this module we define models and reductions for composition of queries,
that is, the direct sum of query times.

## Tags
query model, free monad, time complexity, Prog
-/

namespace Algolean

namespace Algorithms

/--
The composition of two queries is their direct sum
-/
def compositeQuery (Q₁ Q₂ : Type u → Type v) : Type u → Type v :=
  fun α => Sum (Q₁ α) (Q₂ α)

/--
The composite model of `composeQuery Q₁ Q₂` obtained by
composing their models `m₁ : Model Q₁ c₁` and `m₂ : Model Q₂ c₂`.
The cost type of the composite model is the product type `c₁ × c₂`
-/
def compositeModel [AddZero c₁] [AddZero c₂]
    (m₁ : Model Q₁ c₁)
    (m₂ : Model Q₂ c₂) :
    Model (compositeQuery Q₁ Q₂) (c₁ × c₂) where
  evalQuery
    | .inl q => m₁.evalQuery q
    | .inr q => m₂.evalQuery q
  cost
    | .inl q => (m₁.cost q, 0)
    | .inr q => (0, m₂.cost q)


end Algorithms

end Algolean
