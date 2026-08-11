/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Tanner Duve
-/

module

public import Algolean.ModelM
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Random sampling query models

Sampling queries return sampled values to `Prog`; probability appears only in their `PMF`
interpretation. `RandomSample.sample dist : RandomSample α` carries a distribution in each query.
The query result is `α`, not `PMF α`; `Prog.evalM` into `PMF` supplies the probabilistic bind that
explores the possible returned values.

Standard randomized query models treat internal randomness as free: random choices determine which
costed queries execute but do not themselves contribute query cost. `RandomSample.free` provides
that interpretation, while `RandomSample.sampleCount` explicitly counts draws when random-sample
complexity is the quantity of interest.

For a randomized model, `Prog.costM` is the distribution of total query cost from which expected,
worst-case, and high-probability runtime bounds can be derived. Analyses conditioned on program
success additionally use `Prog.runM` internally to retain the correlation between a result and its
cost.
-/

@[expose] public section

noncomputable section

/-- `PMF.map_const` at the monad level, stated on the lambda so that `simp` can match it.

Mapping a constant over a distribution discards the randomness entirely; this is what makes
sampling queries whose results are ignored invisible to cost distributions. The right-hand side
is the monadic `pure`, written `Pure.pure` because inside the `PMF` namespace a plain `pure`
denotes `PMF.pure`.
-/
@[simp] theorem PMF.map_const' (p : PMF α) (b : β) :
    (fun _ => b) <$> p = Pure.pure b := by
  simp only [PMF.monad_map_eq_map, PMF.map, Function.comp_def, PMF.bind_const]
  rfl

namespace Algolean.Algorithms

open Cslib Std.Do

/-!
## Weakest-precondition semantics for `PMF`

A postcondition holds of a `PMF` exactly when it holds of every value in its support. This
interpretation keeps which results are possible and forgets how likely they are, so a proved
triple states that the returned value satisfies its postcondition with probability one. That is
the right notion for algorithms whose answer must be correct on every run. Reasoning about the
probabilities themselves is quantitative and not captured by these instances.

These instances make every `ModelM Q PMF Cost` interpretation (for example `RandomSample.free`)
plug into `Std.Do`'s `Triple`/`mvcgen` infrastructure through `ModelM.handler`, just as a
deterministic `Model` does.
-/

/-- Support-based weakest-precondition interpretation of a `PMF`. -/
instance instWPPMF : WP PMF .pure where
  wp x :=
    { trans := fun Q => ⟨∀ a ∈ x.support, (Q.1 a).down⟩
      conjunctiveRaw := by
        intro Q₁ Q₂
        simp only [SPred.bientails_nil, SPred.and_nil]
        grind }

/-- The support interpretation is a monad morphism, so `mvcgen` reasoning applies. -/
instance instWPMonadPMF : WPMonad PMF .pure where
  wp_pure a := by
    apply PredTrans.ext
    intro Q
    have hp : (pure a : PMF _) = PMF.pure a := rfl
    rw [hp, PredTrans.apply_Pure_pure]
    apply ULift.ext
    simp only [WP.wp, PredTrans.apply, PMF.mem_support_pure_iff, forall_eq]
  wp_bind x f := by
    apply PredTrans.ext
    intro Q
    have hxf : (x >>= f) = x.bind f := rfl
    rw [hxf, PredTrans.apply_Bind_bind]
    apply ULift.ext
    simp only [WP.wp, PredTrans.apply, PMF.mem_support_bind_iff]
    grind

/-- Sample from a distribution supplied by this query. -/
inductive RandomSample : Type u → Type u where
  | sample (dist : PMF α) : RandomSample α

namespace RandomSample

/-- Lift a distribution-carrying sampling query into a program. -/
def draw (dist : PMF α) : Prog RandomSample α :=
  FreeM.lift (.sample dist)

/-- PMF semantics with a caller-chosen cost for each draw. -/
def model (sampleCost : Cost) : ModelM RandomSample PMF Cost where
  evalQuery
    | .sample dist => dist
  cost _ := sampleCost

@[simp] theorem model_evalQuery_sample (sampleCost : Cost) (dist : PMF α) :
    (model sampleCost).evalQuery (.sample dist) = dist := rfl

@[simp] theorem model_cost (sampleCost : Cost) (q : RandomSample α) :
    (model sampleCost).cost q = sampleCost := rfl

/-- Standard randomized-query semantics in which internal sampling is free. -/
abbrev free [Zero Cost] : ModelM RandomSample PMF Cost :=
  model 0

/-- Random-sample complexity semantics in which every draw contributes one. -/
abbrev sampleCount : ModelM RandomSample PMF ℕ :=
  model 1

@[simp] theorem evalM_draw (dist : PMF α) (sampleCost : Cost) :
    (draw dist).evalM (model sampleCost) = dist := by
  simp [draw]

@[simp] theorem costM_draw [AddMonoid Cost] (dist : PMF α) (sampleCost : Cost) :
    (draw dist).costM (model sampleCost) = pure sampleCost := by
  simp [draw]

end RandomSample

/-- Add distribution-carrying sampling queries to another query language. -/
abbrev RandomizeQuery (Q : Type u → Type v) : Type u → Type (max u v) :=
  fun α => Sum (Q α) (RandomSample α)

namespace RandomizeQuery

/-- Lift an original `Q` query into the randomized query language. -/
def query (q : Q α) : Prog (RandomizeQuery Q) α :=
  FreeM.lift (.inl q)

/-- Draw from a distribution inside the randomized query language. -/
def draw (dist : PMF α) : Prog (RandomizeQuery Q) α :=
  FreeM.lift (.inr (.sample dist))

@[simp] theorem evalM_query [Monad m] [LawfulMonad m]
    (M : ModelM (RandomizeQuery Q) m Cost) (q : Q α) :
    (query q).evalM M = M.evalQuery (.inl q) := by
  simp [query]

@[simp] theorem evalM_draw [Monad m] [LawfulMonad m]
    (M : ModelM (RandomizeQuery Q) m Cost) (dist : PMF α) :
    (draw dist).evalM M = M.evalQuery (.inr (.sample dist)) := by
  simp [draw]

end RandomizeQuery

/-- A `Q` model extended with internal randomness and interpreted probabilistically. -/
abbrev RandomizeModel (Q : Type u → Type v) (Cost : Type u) :=
  ModelM (RandomizeQuery Q) PMF Cost

namespace RandomizeModel

/-- Add free internal randomness to a model already interpreted in `PMF`. -/
abbrev ofModelM [Zero Cost] (M : ModelM Q PMF Cost) : RandomizeModel Q Cost :=
  M.sum RandomSample.free

/-- Lift a deterministic model into `PMF` and add free internal randomness.

This is the standard randomized-query construction: the original queries retain their costs while
random choices only determine which queries execute.
-/
abbrev ofModel [Zero Cost] (M : Model Q Cost) : RandomizeModel Q Cost :=
  ofModelM
    { evalQuery := fun q => PMF.pure (M.evalQuery q)
      cost := M.cost }

end RandomizeModel

/-- A `HasModel` on `Q` induces a handler on `RandomizeQuery Q` in which `Q` queries follow
their model and draws are free. -/
noncomputable instance instHasHandlerRandomizeQuery [HasModel Q Cost] [Zero Cost] :
    Cslib.FreeM.HasHandler (RandomizeQuery Q) .pure :=
  (RandomizeModel.ofModel (HasModel.model : Model Q Cost)).hasHandler

end Algolean.Algorithms
