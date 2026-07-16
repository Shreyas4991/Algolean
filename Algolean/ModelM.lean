/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.AddWriter.Transformer
public import Algolean.QueryModel

/-!
# Monadic query models

`ModelM` is a parallel, effectful counterpart to `Model`. It leaves the existing deterministic API
unchanged and interprets the same `Prog Q α` syntax in an arbitrary monad `m`.

`Prog.evalM` is the primary semantics. Evaluation and per-query cost remain separate in `ModelM`.
`Prog.runM` records enough operational information to derive the runtime views used for randomized
algorithms: expected runtime, worst-case runtime over random choices, high-probability runtime, and
expected runtime conditioned on success. The joint result-cost value is supporting data rather than
itself a complexity measure; conditioning on success is the reason the correlation must be retained.

Value-correctness reasoning is independent of cost. A model whose semantic monad has a
`Std.Do.WPMonad` supplies the same `mvcgen` infrastructure as the existing pure `Model` API through
`ModelM.handler` and `ModelM.hasHandler`. Quantitative PMF reasoning remains a separate future
layer.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib

structure ModelM (Q : Type u → Type v) (m : Type u → Type w) (Cost : Type u) where
  evalQuery : Q α → m α
  cost : Q α → Cost

namespace ModelM

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Interpret one query jointly, pairing every semantic branch with the query's fixed cost. -/
def runQuery [Functor m] (M : ModelM Q m Cost) (q : Q α) : AddWriterT Cost m α :=
  AddWriterT.mk ((fun result => ⟨result, M.cost q⟩) <$> M.evalQuery q)

@[simp] theorem runQuery_value [Functor m] [LawfulFunctor m]
    (M : ModelM Q m Cost) (q : Q α) :
    (M.runQuery q).value = M.evalQuery q := by
  simp [runQuery, AddWriterT.value]

@[simp] theorem runQuery_cost [Functor m] [LawfulFunctor m]
    (M : ModelM Q m Cost) (q : Q α) :
    (M.runQuery q).cost = (fun _ => M.cost q) <$> M.evalQuery q := by
  simp [runQuery, AddWriterT.cost]

/-- Construct an effectful model from its separate evaluator and cost functions. -/
def ofEvalCost (evalQuery : {α : Type u} → Q α → m α)
    (cost : {α : Type u} → Q α → Cost) : ModelM Q m Cost :=
  ⟨evalQuery, cost⟩

/-- Lift an existing deterministic model into `Id` without changing its semantics. -/
def ofModel (M : Algolean.Algorithms.Model Q Cost) : ModelM Q Id Cost where
  evalQuery q := M.evalQuery q
  cost q := M.cost q

@[simp] theorem ofModel_evalQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).evalQuery q = M.evalQuery q := rfl

@[simp] theorem ofModel_cost (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).cost q = M.cost q := rfl

/-- Change the semantic monad through a polymorphic natural transformation. -/
def mapK {n : Type u → Type y} (lift : {α : Type u} → m α → n α)
    (M : ModelM Q m Cost) : ModelM Q n Cost where
  evalQuery q := lift (M.evalQuery q)
  cost q := M.cost q

@[simp] theorem mapK_evalQuery {n : Type u → Type y}
    (lift : {α : Type u} → m α → n α) (M : ModelM Q m Cost) (q : Q α) :
    (M.mapK lift).evalQuery q = lift (M.evalQuery q) := rfl

@[simp] theorem mapK_cost {n : Type u → Type y}
    (lift : {α : Type u} → m α → n α) (M : ModelM Q m Cost) (q : Q α) :
    (M.mapK lift).cost q = M.cost q := rfl

/-- Sum two query languages interpreted in the same monad with the same cost type. -/
def sum {Q₂ : Type u → Type x} (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) :
    ModelM (fun α => Sum (Q α) (Q₂ α)) m Cost where
  evalQuery
    | .inl q => M₁.evalQuery q
    | .inr q => M₂.evalQuery q
  cost
    | .inl q => M₁.cost q
    | .inr q => M₂.cost q

@[simp] theorem sum_evalQuery_inl {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).evalQuery (.inl q) = M₁.evalQuery q := rfl

@[simp] theorem sum_evalQuery_inr {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).evalQuery (.inr q) = M₂.evalQuery q := rfl

@[simp] theorem sum_cost_inl {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).cost (.inl q) = M₁.cost q := rfl

@[simp] theorem sum_cost_inr {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).cost (.inr q) = M₂.cost q := rfl

end ModelM

namespace Prog

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Evaluate a query program in the semantic monad of `M`. -/
def evalM [Monad m] (P : Prog Q α) (M : ModelM Q m Cost) : m α :=
  P.liftM M.evalQuery

/-- Record results and accumulated costs in the same semantic branch.

This is foundational data for runtime analyses, not a chosen notion of randomized complexity.
Keeping the correlation is necessary for analyses such as expected runtime conditioned on success.
-/
def runM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) : AddWriterT Cost m α :=
  P.liftM M.runQuery

/-- The total-runtime marginal of `runM`.

For probabilistic semantics this is the runtime distribution used to derive expected, worst-case,
and high-probability bounds. Analyses conditioned on the returned result must use `runM` so that
the result-cost correlation is not discarded.
-/
def costM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) : m Cost :=
  (P.runM M).cost

@[simp] theorem evalM_pure [Monad m] (a : α) (M : ModelM Q m Cost) :
    evalM (pure a : Prog Q α) M = pure a := rfl

@[simp] theorem evalM_liftBind [Monad m]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    evalM (FreeM.liftBind q f) M = (M.evalQuery q >>= fun a => evalM (f a) M) := rfl

@[simp] theorem evalM_lift [Monad m] [LawfulMonad m]
    (q : Q α) (M : ModelM Q m Cost) :
    evalM (FreeM.lift q) M = M.evalQuery q := by
  simp [evalM]

@[simp] theorem evalM_bind [Monad m] [LawfulMonad m]
    (P : Prog Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    evalM (P >>= f) M = (evalM P M >>= fun a => evalM (f a) M) := by
  simp [evalM]

@[simp] theorem evalM_map [Monad m] [LawfulMonad m]
    (f : α → β) (P : Prog Q α) (M : ModelM Q m Cost) :
    evalM (f <$> P) M = f <$> evalM P M := by
  simp [evalM]

@[simp] theorem runM_pure [Monad m] [AddZero Cost]
    (a : α) (M : ModelM Q m Cost) :
    runM (pure a : Prog Q α) M = pure a := rfl

@[simp] theorem runM_liftBind [Monad m] [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    runM (FreeM.liftBind q f) M = (M.runQuery q >>= fun a => runM (f a) M) := rfl

@[simp] theorem runM_lift [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (M : ModelM Q m Cost) :
    runM (FreeM.lift q) M = M.runQuery q := by
  simp [runM]

@[simp] theorem runM_bind [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    runM (P >>= f) M = (runM P M >>= fun a => runM (f a) M) := by
  simp [runM]

@[simp] theorem runM_map [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (f : α → β) (P : Prog Q α) (M : ModelM Q m Cost) :
    runM (f <$> P) M = f <$> runM P M := by
  simp [runM]

/-- Forgetting the cost component of the joint semantics recovers `evalM`. -/
theorem runM_value [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) :
    (P.runM M).value = P.evalM M := by
  induction P with
  | pure a => simp
  | liftBind q f ih =>
      simp only [runM_liftBind, evalM_liftBind, AddWriterT.value_bind,
        ModelM.runQuery, AddWriterT.run_mk, ih, bind_map_left]

@[simp] theorem costM_pure [Monad m] [LawfulMonad m] [AddZero Cost]
    (a : α) (M : ModelM Q m Cost) :
    costM (pure a : Prog Q α) M = pure 0 := by
  simp [costM]

@[simp] theorem costM_liftBind [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    costM (FreeM.liftBind q f) M =
      (M.evalQuery q >>= fun a => (M.cost q + ·) <$> costM (f a) M) := by
  simp [costM, runM, ModelM.runQuery, AddWriterT.cost, AddWriterT.run_bind]

section OfModel

variable {Q : Type u → Type u} {Cost : Type u}

/-- `evalM` under `ofModel` agrees with the existing evaluator. -/
theorem evalM_ofModel (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.evalM (ModelM.ofModel M)) = P.eval M := by
  induction P with
  | pure a => rfl
  | liftBind q f ih => exact ih (M.evalQuery q)

/-- Under `ofModel`, one query contributes its cost and continues with its evaluated result. -/
@[simp] theorem costM_ofModel_liftBind [AddMonoid Cost]
    (q : Q α) (f : α → Prog Q β) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (Prog.costM (FreeM.liftBind q f) (ModelM.ofModel M)) =
      M.cost q + Id.run ((f (M.evalQuery q)).costM (ModelM.ofModel M)) := by
  rw [costM_liftBind]
  rfl

/-- `costM` under `ofModel` agrees with existing `Prog.time`. -/
theorem costM_ofModel [AddMonoid Cost]
    (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.costM (ModelM.ofModel M)) = P.time M := by
  induction P with
  | pure a => simp
  | liftBind q f ih =>
      rw [costM_ofModel_liftBind, Prog.time_liftBind, ih]

end OfModel

section Reduction

variable {Q₁ Q₂ : Type u → Type u}


/-- A reduction preserves effectful evaluation when it implements every source query
in the target model. The existing `Reduction` structure is sufficient; only its correctness
criterion changes for effectful models. -/
theorem reduceProg_evalM [Monad m] [LawfulMonad m]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelM Q₁ m Cost) (M₂ : ModelM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).evalM M₂ = M₁.evalQuery q) :
    (P.reduceProg red).evalM M₂ = P.evalM M₁ := by
  induction P with
  | pure a => rfl
  | liftBind q f ih =>
      simp only [Prog.reduceProg, evalM, FreeM.liftBind_eq, FreeM.bind_eq_bind,
        FreeM.liftM_bind, FreeM.liftM_lift]
      have hq : FreeM.liftM M₂.evalQuery (red.reduce q) = M₁.evalQuery q := by
        apply hCorrect
      rw [hq]
      apply congrArg (fun k : _ → m α => M₁.evalQuery q >>= k)
      funext a
      apply ih

/-- The stronger joint criterion preserves results and branch-correlated accumulated costs. -/
theorem reduceProg_runM [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelM Q₁ m Cost) (M₂ : ModelM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).runM M₂ = M₁.runQuery q) :
    (P.reduceProg red).runM M₂ = P.runM M₁ := by
  induction P with
  | pure a => rfl
  | liftBind q f ih =>
      simp only [Prog.reduceProg, runM, FreeM.liftBind_eq, FreeM.bind_eq_bind,
        FreeM.liftM_bind, FreeM.liftM_lift]
      have hq : FreeM.liftM M₂.runQuery (red.reduce q) = M₁.runQuery q := by
        apply hCorrect
      rw [hq]
      apply congrArg (fun k : _ → AddWriterT Cost m α => M₁.runQuery q >>= k)
      funext a
      apply ih

end Reduction

end Prog

section WeakestPrecondition

open Cslib.FreeM Std.Do

variable {ps : PostShape.{u}}

namespace ModelM

/-- The logical handler induced by the effectful evaluation semantics of `M`.

The cost field is intentionally absent: ordinary Hoare triples specify value correctness under
`evalM`. Cost-aware and quantitative probabilistic logics are separate analyses.
-/
def handler [WP m ps] (M : ModelM Q m Cost) : LHandler Q ps :=
  LHandler.ofInterp (m := m) (fun _ q => M.evalQuery q)

/-- Select `M` as the logical interpretation of `Prog Q` in a local or scoped context.

This is a value rather than a global instance because the same query syntax may have both a pure
`Model` and one or more effectful `ModelM` interpretations.
-/
@[reducible] def hasHandler [WP m ps] (M : ModelM Q m Cost) : HasHandler Q ps where
  handler := M.handler

/-- Weakest-precondition reasoning through `M.handler` agrees with executing the program using
`Prog.evalM M` whenever the semantic monad has a lawful weakest-precondition interpretation. -/
theorem wp_eq_wp_evalM [Monad m] [WPMonad m ps]
    (M : ModelM Q m Cost) (P : Prog Q α) :
    wpH M.handler P = wp (P.evalM M) := by
  unfold ModelM.handler Prog.evalM
  exact wpH_ofInterp_eq_wp_liftM (m := m) (fun _ q => M.evalQuery q) P

end ModelM

/-- Generic single-query rule for the currently selected logical handler.

When the selected handler is `M.hasHandler`, this precondition reduces to
`wp⟦M.evalQuery q⟧ Q'`. The rule lets `mvcgen` decompose effectful query programs without choosing a
global `ModelM` for the query language.
-/
@[spec]
theorem Spec.queryM [HasHandler Q ps] (q : Q α) {Q' : PostCond α ps} :
    Triple (FreeM.lift q : Prog Q α) ((HasHandler.handler q).apply Q') Q' := by
  apply Triple.of_entails_wp
  rw [show wp (FreeM.lift q : Prog Q α) =
    wpH HasHandler.handler (FreeM.lift q) from rfl, wpH_lift]

/-- The `ModelM` query rule stated directly through the semantic monad's weakest precondition. -/
theorem ModelM.query_spec [Monad m] [WPMonad m ps]
    (M : ModelM Q m Cost) (q : Q α) {Q' : PostCond α ps} :
    let _ : HasHandler Q ps := M.hasHandler
    Triple (FreeM.lift q : Prog Q α) (wp⟦M.evalQuery q⟧ Q') Q' := by
  letI := M.hasHandler
  exact Spec.queryM q

end WeakestPrecondition

end Algolean.Algorithms
