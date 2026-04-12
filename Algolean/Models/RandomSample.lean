/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.QueryModel
public import Mathlib.Probability.ProbabilityMassFunction.Monad

@[expose] public section

/-!
# Query Type for Random Sampling
-/

namespace Algolean

namespace Algorithms

/--
A query type for sampling from distributions on `α`.

Since `Model.evalQuery` is pure, we represent the result of a sampling query by
the corresponding `PMF α` rather than by a single sampled value.
-/
inductive RandomSample (α : Type u) : Type u → Type u where
  | sample : RandomSample α (PMF α)

/--
`RandomizeQuery Q α` extends a query type `Q` with access to a hidden sampling
oracle on `α`.

The left summand contains the original queries from `Q`, while the right summand
contains the new sampling query.
-/
abbrev RandomizeQuery (Q : Type u → Type v) (α : Type u) : Type u → Type (max u v) :=
  fun β => Sum (Q β) (RandomSample α β)

/-- A model of `RandomSample` that counts each sampling query with unit cost. -/
@[simps]
def RandomSample.natCost (dist : PMF α) : Model (RandomSample α) ℕ where
  evalQuery
    | .sample => dist
  cost _ := 1

/-- Combine a model for `Q` with a sampling model to interpret `RandomizeQuery Q α`. -/
@[simps]
def RandomizeQuery.model (M : Model Q Cost) (S : Model (RandomSample α) Cost) :
    Model (RandomizeQuery Q α) Cost where
  evalQuery
    | .inl q => M.evalQuery q
    | .inr q => S.evalQuery q
  cost
    | .inl q => M.cost q
    | .inr q => S.cost q


end Algorithms

end Algolean
