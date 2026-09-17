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

`ModelM` generalizes `Model` by allowing queries to be evaluated in any monad `m`.
`Prog.evalM` evaluates a program, `Prog.runM` records its result and accumulated query cost, and
`Prog.costM` returns the accumulated cost.

For a monad with a `Std.Do.WPMonad` instance, `ModelM.handler` and `ModelM.hasHandler` provide
weakest-precondition semantics for `mvcgen`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib

/-- A query model whose queries are evaluated in the monad `m`. -/
structure ModelM (Q : Type u → Type v) (m : Type u → Type w) (Cost : Type u) where
  /-- Evaluate a query in `m`. -/
  evalQuery : Q α → m α
  /-- The cost assigned to a query. -/
  cost : Q α → Cost

namespace ModelM

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Evaluate one query and record its cost. -/
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

/-- Regard a `Model` as a `ModelM` over `Id`. -/
def ofModel (M : Algolean.Algorithms.Model Q Cost) : ModelM Q Id Cost where
  evalQuery q := M.evalQuery q
  cost q := M.cost q

@[simp] theorem ofModel_evalQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).evalQuery q = M.evalQuery q := rfl

@[simp] theorem ofModel_cost (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).cost q = M.cost q := rfl

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

/-- Evaluate a query program while recording the accumulated query cost with each result. -/
def runM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) : AddWriterT Cost m α :=
  P.liftM M.runQuery

/-- The accumulated query cost of each execution of a program. -/
def costM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) : m Cost :=
  (P.runM M).cost

@[simp] theorem evalM_pure [Monad m] (a : α) (M : ModelM Q m Cost) :
    evalM (pure a : Prog Q α) M = pure a := rfl

@[simp] theorem evalM_liftBind [Monad m]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    evalM (FreeM.lift q >>= f) M = (M.evalQuery q >>= fun a => evalM (f a) M) := rfl

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
    runM (FreeM.lift q >>= f) M = (M.runQuery q >>= fun a => runM (f a) M) := rfl

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
@[simp] theorem runM_value [Monad m] [LawfulMonad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q m Cost) :
    (P.runM M).value = P.evalM M := by
  induction P with
  | pure a => simp
  | liftBind q f ih =>
      simp only [runM, evalM] at ih
      simp only [runM, evalM, FreeM.liftM, AddWriterT.value_bind,
        ModelM.runQuery, AddWriterT.run_mk, ih, bind_map_left]

@[simp] theorem costM_pure [Monad m] [LawfulMonad m] [AddZero Cost]
    (a : α) (M : ModelM Q m Cost) :
    costM (pure a : Prog Q α) M = pure 0 := by
  simp [costM]

@[simp] theorem costM_liftBind [Monad m] [LawfulMonad m] [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    costM (FreeM.lift q >>= f) M =
      (M.evalQuery q >>= fun a => (M.cost q + ·) <$> costM (f a) M) := by
  simp [costM, runM, ModelM.runQuery, AddWriterT.cost, AddWriterT.run_bind]

@[simp] theorem costM_lift [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (M : ModelM Q m Cost) :
    costM (FreeM.lift q) M = (fun _ => M.cost q) <$> M.evalQuery q := by
  simp [costM]

@[simp] theorem costM_map [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (f : α → β) (P : Prog Q α) (M : ModelM Q m Cost) :
    costM (f <$> P) M = costM P M := by
  simp [costM]

section OfModel

/-- Evaluating with `ofModel M` is the same as evaluating with `M`. -/
@[simp] theorem evalM_ofModel (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.evalM (ModelM.ofModel M)) = P.eval M := rfl

/-- The cost of a query followed by a program under `ofModel`. -/
@[simp] theorem costM_ofModel_liftBind [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (Prog.costM (FreeM.lift q >>= f) (ModelM.ofModel M)) =
      M.cost q + Id.run ((f (M.evalQuery q)).costM (ModelM.ofModel M)) := rfl

/-- Computing cost with `ofModel M` gives `Prog.time M`. -/
@[simp] theorem costM_ofModel [AddZero Cost]
    (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.costM (ModelM.ofModel M)) = P.time M := by
  induction P with
  | pure a => rfl
  | liftBind q f ih => exact congrArg (M.cost q + ·) (ih (M.evalQuery q))

end OfModel

section Reduction

variable {Q₁ Q₂ : Type u → Type u}

/-- A query reduction preserving each query also preserves program evaluation. -/
theorem reduceProg_evalM [Monad m] [LawfulMonad m]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelM Q₁ m Cost₁) (M₂ : ModelM Q₂ m Cost₂)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).evalM M₂ = M₁.evalQuery q) :
    (P.reduceProg red).evalM M₂ = P.evalM M₁ :=
  reduceProg_liftM P red M₁.evalQuery M₂.evalQuery hCorrect

/-- A query reduction preserving `runM` also preserves `runM` for every program. -/
theorem reduceProg_runM [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelM Q₁ m Cost) (M₂ : ModelM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).runM M₂ = M₁.runQuery q) :
    (P.reduceProg red).runM M₂ = P.runM M₁ :=
  reduceProg_liftM P red M₁.runQuery M₂.runQuery hCorrect

/-- A query reduction preserving `runM` also preserves accumulated program costs. -/
theorem reduceProg_costM [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelM Q₁ m Cost) (M₂ : ModelM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).runM M₂ = M₁.runQuery q) :
    (P.reduceProg red).costM M₂ = P.costM M₁ :=
  congrArg AddWriterT.cost (reduceProg_runM P red M₁ M₂ hCorrect)

end Reduction

end Prog

section WeakestPrecondition

open Cslib.FreeM Std.Do

variable {ps : PostShape.{u}}

namespace ModelM

/-- The logical handler induced by `M.evalQuery`. -/
def handler [WP m ps] (M : ModelM Q m Cost) : LHandler Q ps :=
  LHandler.ofInterp (m := m) (fun _ q => M.evalQuery q)

@[simp] theorem handler_sum [WP m ps] {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α ⊕ Q₂ α) :
    (M₁.sum M₂).handler q = LHandler.sum M₁.handler M₂.handler q := by
  cases q <;> rfl

/-- Use `M.handler` as the logical handler for `Prog Q`. -/
@[reducible] def hasHandler [WP m ps] (M : ModelM Q m Cost) : HasHandler Q ps where
  handler := M.handler

/-- The weakest precondition given by `M.handler` agrees with that of `Prog.evalM M`. -/
theorem wp_eq_wp_evalM [Monad m] [WPMonad m ps]
    (M : ModelM Q m Cost) (P : Prog Q α) :
    wpH M.handler P = wp (P.evalM M) :=
  wpH_ofInterp_eq_wp_liftM (m := m) (fun _ q => M.evalQuery q) P

end ModelM

/-- The `ModelM` query rule stated directly through the semantic monad's weakest precondition. -/
theorem ModelM.query_spec [Monad m] [WPMonad m ps]
    (M : ModelM Q m Cost) (q : Q α) {Q' : PostCond α ps} :
    let _ : HasHandler Q ps := M.hasHandler
    Triple (FreeM.lift q : Prog Q α) (wp⟦M.evalQuery q⟧ Q') Q' := by
  letI := M.hasHandler
  exact Cslib.FreeM.Spec.lift_FreeM q

end WeakestPrecondition

end Algolean.Algorithms
