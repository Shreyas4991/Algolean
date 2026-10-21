/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Models.RandomSample

/-!
# Computable finite sampling queries

`UniformSample.fin n` requests an index in `Fin (n + 1)`. The query stores only the bound;
the noncomputable uniform distribution lives in `UniformSample.pmfModel`. Computable interpreters
can supply their own finite sampler via `UniformSample.model`.
-/

@[expose] public section

namespace Algolean.Algorithms

/-- A finite sampling request, with a nonempty range by construction. -/
inductive UniformSample : Type → Type where
  | fin (n : Nat) : UniformSample (Fin (n + 1))

namespace UniformSample

/-- Interpret finite draws using a supplied sampler and cost per draw. -/
def model (sample : (n : Nat) → m (Fin (n + 1))) (sampleCost : Cost) :
    ModelM UniformSample m Cost where
  evalQuery
    | .fin n => sample n
  cost _ := sampleCost

/-- Uniform probabilistic semantics; internal randomness contributes no query cost. -/
noncomputable def pmfModel [Zero Cost] : ModelM UniformSample PMF Cost :=
  model (fun n => PMF.ofFintype
    (fun _ : Fin (n + 1) => (n + 1 : ENNReal)⁻¹) (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      exact ENNReal.mul_inv_cancel (by simp) (by simp))) 0

end UniformSample

end Algolean.Algorithms
