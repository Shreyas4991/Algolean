/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.RandomSample

/-!
# Random sampling examples

Sanity checks for the `RandomSample` query language and its `PMF` models. The examples confirm
that the `model` simp lemmas apply to `free` and `sampleCount` and that the `RandomizeModel`
constructions compute by `simp`.
-/

@[expose] public section

noncomputable section

namespace AlgoleanTests.RandomSampleExamples

open Algolean.Algorithms Cslib RandomSample Std.Do

example (dist : PMF ℕ) : (draw dist).evalM (free (Cost := ℕ)) = dist := by
  simp

example (dist : PMF ℕ) : (draw dist).costM (free (Cost := ℕ)) = pure 0 := by
  simp

example (dist : PMF ℕ) : (draw dist).costM sampleCount = pure 1 := by
  simp

example (M : ModelM Q PMF Cost) [Zero Cost] (q : Q α) :
    (RandomizeQuery.query q).evalM (RandomizeModel.ofModelM M) = M.evalQuery q := by
  simp

example (M : ModelM Q PMF Cost) [Zero Cost] (dist : PMF α) :
    (RandomizeQuery.draw dist).evalM (RandomizeModel.ofModelM M) = dist := by
  simp

example (M : Model Q Cost) [Zero Cost] (q : Q α) :
    (RandomizeQuery.query q).evalM (RandomizeModel.ofModel M) = PMF.pure (M.evalQuery q) := by
  simp

/-- One branch stops after one draw while the other performs a second draw. -/
def branchWithExtraDraw (coin : PMF Bool) (extra : PMF α) : Prog RandomSample Bool := do
  let b ← draw coin
  if b then
    return true
  else
    let _ ← draw extra
    return false

/-- The sample-count distribution is one draw on the `true` branch and two on the `false` branch.

The values drawn from `extra` do not affect the count; only the fact that the second draw occurs
matters. This theorem concerns random-sample complexity, not standard randomized query runtime.
-/
theorem costM_branchWithExtraDraw (coin : PMF Bool) (extra : PMF α) :
    (branchWithExtraDraw coin extra).costM sampleCount =
      (fun b => if b then 1 else 2) <$> coin := by
  simp only [branchWithExtraDraw, draw, Prog.costM_liftBind,
    model_evalQuery_sample, model_cost]
  rw [← bind_pure_comp]
  apply bind_congr
  intro b
  cases b <;> simp

-- Almost-sure reasoning through the support interpretation. `mvcgen` discharges the triple that a
-- drawn value always lies in the distribution's support, using `free`'s handler as the selected
-- interpretation of the query language.
set_option mvcgen.warning false in
example {α : Type} (dist : PMF α) :
    letI := (free (Cost := ℕ)).hasHandler
    ⦃⌜True⌝⦄ draw dist ⦃⇓ a => ⌜a ∈ dist.support⌝⦄ := by
  letI := (free (Cost := ℕ)).hasHandler
  mvcgen [draw]
  exact fun a ha => ha

end AlgoleanTests.RandomSampleExamples
