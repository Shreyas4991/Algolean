/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.QueryModel

@[expose] public section

/-!
# Query Complexity Classes

Complexity classes defined parametrically over query types and cost types.
A single framework covers comparison complexity, query complexity,
Turing machine time/space, circuit depth, and any other cost model
expressible via `Model Q Cost`.

## Main definitions

- `QueryProblem Q Cost α`: a problem whose specification depends on the model
- `Solves`: a program correctly solves a problem for all models
- `SolvesWithin`: a program solves a problem within a cost bound for all models
- `InQueryComplexity`: a problem is in a complexity class (existential over programs)
- `ProblemReducesTo`: one problem reduces to another with bounded overhead

## Design

The key idea is that in the query model, the problem specification depends
on the oracle (model). For sorting, "correct" means "the output is the
sorted version of the input determined by the comparison oracle." This
dependence is captured by `QueryProblem.spec : Model Q Cost → α → Prop`.
-/

namespace Algolean
namespace Algorithms

open Cslib

variable {Q : Type u → Type u} {Cost : Type*}

/-- A problem in the query model. The specification depends on the model
because the "correct answer" is determined by the oracle. -/
structure QueryProblem (Q : Type u → Type u) (Cost : Type*) (α : Type u) where
  /-- The correctness specification, parameterized by the model. -/
  spec : Model Q Cost → α → Prop

/-- `P` solves `prob` for all models: the result satisfies the spec
regardless of oracle. -/
def Solves (P : Prog Q α) (prob : QueryProblem Q Cost α) : Prop :=
  ∀ M : Model Q Cost, prob.spec M (P.eval M)

/-- `P` solves `prob` within cost `bound` under a specific model `M`.
This is the model-specific version, used when the model is fixed
(e.g., Turing machines have a unique model `TMModel tm`). -/
def SolvesWithinModel [AddZero Cost] [Preorder Cost]
    (P : Prog Q α) (prob : QueryProblem Q Cost α)
    (M : Model Q Cost) (bound : Cost) : Prop :=
  prob.spec M (P.eval M) ∧ P.time M ≤ bound

/-- `P` solves `prob` within cost `bound` for all models.
This is the oracle-universal version, used when the program must be
correct regardless of which oracle it faces (e.g., comparison sort
must work for all orderings). -/
def SolvesWithin [AddZero Cost] [Preorder Cost]
    (P : Prog Q α) (prob : QueryProblem Q Cost α) (bound : Cost) : Prop :=
  ∀ M : Model Q Cost, SolvesWithinModel P prob M bound

/-- A problem is in the complexity class determined by `bound`:
there exists a program solving it within that bound. -/
def InClass [AddZero Cost] [Preorder Cost]
    (prob : QueryProblem Q Cost α) (bound : Cost) : Prop :=
  ∃ P : Prog Q α, SolvesWithin P prob bound

/-- `SolvesWithin` implies `Solves`. -/
theorem SolvesWithin.solves [AddZero Cost] [Preorder Cost]
    {P : Prog Q α} {prob : QueryProblem Q Cost α} {bound : Cost}
    (h : SolvesWithin P prob bound) : Solves P prob :=
  fun M => (h M).1

/-! ## Composition via bind -/

/-- Composition of programs via bind: if `op` runs within `bound₁`
and the continuation runs within `bound₂` on the result, then
`op >>= cont` runs within `bound₁ + bound₂`. The combined problem
asks for the continuation's spec applied to the result of `op`. -/
theorem SolvesWithinModel.bind [AddCommMonoid Cost] [Preorder Cost]
    [CovariantClass Cost Cost (· + ·) (· ≤ ·)]
    {op : Prog Q α} {cont : α → Prog Q β}
    {prob_op : QueryProblem Q Cost α}
    {prob_cont : α → QueryProblem Q Cost β}
    {M : Model Q Cost} {bound₁ bound₂ : Cost}
    (hop : SolvesWithinModel op prob_op M bound₁)
    (hcont : ∀ a, prob_op.spec M a →
      SolvesWithinModel (cont a) (prob_cont a) M bound₂) :
    SolvesWithinModel (op.bind cont) (prob_cont (op.eval M)) M (bound₁ + bound₂) := by
  obtain ⟨hspec, htime⟩ := hop
  obtain ⟨hspec', htime'⟩ := hcont _ hspec
  refine ⟨?_, ?_⟩
  · rwa [Prog.eval_bind]
  · rw [Prog.time_bind]; exact add_le_add htime htime'

/-- Oracle-universal version of bind composition. -/
theorem SolvesWithin.bind [AddCommMonoid Cost] [Preorder Cost]
    [CovariantClass Cost Cost (· + ·) (· ≤ ·)]
    {op : Prog Q α} {cont : α → Prog Q β}
    {prob_op : QueryProblem Q Cost α}
    {prob_cont : α → QueryProblem Q Cost β}
    {bound₁ bound₂ : Cost}
    (hop : SolvesWithin op prob_op bound₁)
    (hcont : ∀ M a, prob_op.spec M a →
      SolvesWithinModel (cont a) (prob_cont a) M bound₂) :
    ∀ M, SolvesWithinModel (op.bind cont)
      (prob_cont (op.eval M)) M (bound₁ + bound₂) :=
  fun M => SolvesWithinModel.bind (hop M) (hcont M)

/-! ## Reductions between problems -/

/-- Contravariant map on `QueryProblem`: transport a problem along a
map of models. Analogous to `Filter.comap`, `Ideal.comap`, etc. -/
def QueryProblem.comap
    (prob : QueryProblem Q₁ Cost₁ α)
    (f : Model Q₂ Cost₂ → Model Q₁ Cost₁) :
    QueryProblem Q₂ Cost₂ α where
  spec M₂ a := prob.spec (f M₂) a

@[simp]
theorem QueryProblem.comap_id (prob : QueryProblem Q Cost α) :
    prob.comap id = prob :=
  rfl

theorem QueryProblem.comap_comp (prob : QueryProblem Q₁ Cost₁ α)
    (f : Model Q₂ Cost₂ → Model Q₁ Cost₁)
    (g : Model Q₃ Cost₃ → Model Q₂ Cost₂) :
    (prob.comap f).comap g = prob.comap (f ∘ g) :=
  rfl

/-- If `P` solves `prob` for all models, and the reduction correctly
implements each query, then the reduced program solves the transported
problem. -/
theorem Solves.reduceProg
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (prob : QueryProblem Q₁ Cost₁ α)
    (pullback : Model Q₂ Cost₂ → Model Q₁ Cost₁)
    (hCorrect : ∀ (M₂ : Model Q₂ Cost₂) {ι} (q : Q₁ ι),
      (red.reduce q).eval M₂ = (pullback M₂).evalQuery q)
    (hSolves : Solves P prob) :
    Solves (P.reduceProg red) (prob.comap pullback) := by
  intro M₂
  simp only [QueryProblem.comap]
  rw [Prog.reduceProg_eval P red (pullback M₂) M₂ (hCorrect M₂)]
  exact hSolves (pullback M₂)

/-- A problem `prob₁` reduces to `prob₂` if any program solving `prob₂`
can be transformed into one solving `prob₁` within bounded overhead. -/
def ProblemReducesTo [AddZero Cost] [Preorder Cost]
    (prob₁ prob₂ : QueryProblem Q Cost α)
    (overhead : Cost) : Prop :=
  ∀ (P : Prog Q α) (bound : Cost),
    SolvesWithin P prob₂ bound →
    ∃ P' : Prog Q α, SolvesWithin P' prob₁ (bound + overhead)

/-- If `prob` is in the complexity class for `bound`, and has
overhead `c` reduction to `prob'` which is in class `bound'`,
then `prob` is in class `bound' + c`. -/
theorem InQueryComplexity.of_reduces [AddZero Cost] [Preorder Cost]
    {prob prob' : QueryProblem Q Cost α}
    {bound overhead : Cost}
    (hRed : ProblemReducesTo prob prob' overhead)
    (hIn : InClass prob' bound) :
    InClass prob (bound + overhead) := by
  obtain ⟨P, hP⟩ := hIn
  obtain ⟨P', hP'⟩ := hRed P bound hP
  exact ⟨P', hP'⟩

end Algorithms
end Algolean
