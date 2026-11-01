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

namespace PMF

variable {α β : Type*}

/-- The monadic `pure` of `PMF` is `PMF.pure`. -/
theorem monad_pure_eq_pure {α : Type u} (a : α) : (Pure.pure a : PMF α) = PMF.pure a := rfl

/-- The monadic bind of `PMF` is `PMF.bind`. -/
theorem monad_bind_eq_bind {α β : Type u} (p : PMF α) (f : α → PMF β) :
    p >>= f = p.bind f := rfl

/-! ### Expected values

The expected value of `f : α → ℝ≥0∞` under `p : PMF α` is `∑' a, p a * f a`. -/

open scoped ENNReal

/-- The expected value of a constant `c` under any distribution is `c`. -/
theorem tsum_mul_const (p : PMF α) (c : ℝ≥0∞) : ∑' a, p a * c = c := by
  rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- The expected value of `f` under the point mass at `a` is `f a`. -/
theorem tsum_pure_mul (a : α) (f : α → ℝ≥0∞) : ∑' b, PMF.pure a b * f b = f a := by
  simp [pure_apply, ite_mul]

/-- The expected value of `f` under `p.bind q` is the expected value under `p` of the function
sending `a` to the expected value of `f` under `q a`. -/
theorem tsum_bind_mul (p : PMF α) (q : α → PMF β) (f : β → ℝ≥0∞) :
    ∑' b, p.bind q b * f b = ∑' a, p a * ∑' b, q a b * f b := by
  simp_rw [bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

/-- The expected value of `f` under `p.map g` is the expected value of `f ∘ g` under `p`. -/
theorem tsum_map_mul (p : PMF α) (g : α → β) (f : β → ℝ≥0∞) :
    ∑' b, p.map g b * f b = ∑' a, p a * f (g a) := by
  rw [← bind_pure_comp, tsum_bind_mul]
  simp

/-- For `p : PMF ℕ` and `c : ℕ`, the expected value of `p.map (c + ·)` is `c` plus the expected
value of `p`. -/
theorem tsum_map_add_left_mul (p : PMF ℕ) (c : ℕ) :
    ∑' k, p.map (c + ·) k * k = c + ∑' k, p k * k := by
  simp_rw [tsum_map_mul, Nat.cast_add, mul_add, ENNReal.tsum_add, tsum_mul_const]

/-- For `p q : PMF ℕ`, the expected value of the sum of independent draws from `p` and `q` is the
sum of their expected values. -/
theorem tsum_bind_map_add_mul (p q : PMF ℕ) :
    ∑' k, (p.bind fun a => q.map (a + ·)) k * k = ∑' k, p k * k + ∑' k, q k * k := by
  simp_rw [tsum_bind_mul, tsum_map_add_left_mul, mul_add, ENNReal.tsum_add, tsum_mul_const]

end PMF

namespace Algolean.Algorithms

open Cslib Lean.Order Std.WP

/-!
## Weakest-precondition semantics for `PMF`

A postcondition holds of a `PMF` exactly when it holds of every value in its support. This
interpretation keeps which results are possible and forgets how likely they are, so a proved
triple states that the returned value satisfies its postcondition with probability one. That is
the right notion for algorithms whose answer must be correct on every run. Reasoning about the
probabilities themselves is quantitative and not captured by these instances.

These instances make every `ModelM Q PMF Cost` interpretation (for example `RandomSample.free`)
plug into `Std.WP`'s `Triple`/`vcgen` infrastructure through `ModelM.handler`, just as a
deterministic `Model` does.
-/

/-- Support-based weakest-precondition interpretation of a `PMF`. -/
instance instWPPMF : WP (PMF α) α Prop EStack⟨⟩ where
  wpTrans x := ⟨fun Q _ => ∀ a ∈ x.support, Q a⟩
  wp_trans_monotone x := by
    intro Q Q' E E' _ hQ h a ha
    exact hQ a (h a ha)

/-- The support interpretation respects pure and bind, so `vcgen` reasoning applies. -/
instance instWPMonadPMF : WPMonad PMF Prop EStack⟨⟩ where
  toWP _ := inferInstance
  pure_le_wp_pure a Q E := by
    change Q a → ∀ b ∈ (PMF.pure a).support, Q b
    simp only [PMF.mem_support_pure_iff, forall_eq]
    exact id
  bind_le_wp_bind x f Q E := by
    change (∀ a ∈ x.support, ∀ b ∈ (f a).support, Q b) →
      ∀ b ∈ (x.bind f).support, Q b
    simp only [PMF.mem_support_bind_iff]
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
  ofModelM (ModelM.ofModel M)

end RandomizeModel

/-- A `HasModel` on `Q` induces a handler on `RandomizeQuery Q` in which `Q` queries follow
their model and draws are free. -/
noncomputable instance instHasHandlerRandomizeQuery [HasModel Q Cost] [Zero Cost] :
    Cslib.FreeM.HasHandler (RandomizeQuery Q) Prop EStack⟨⟩ :=
  (RandomizeModel.ofModel (HasModel.model : Model Q Cost)).hasHandler

end Algolean.Algorithms
