/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.AddWriter.WP
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
  /-- Execute a query, retaining its result and cost in the same effect branch. -/
  runQuery : Q α → AddWriterT Cost m α

namespace ModelM

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Evaluate a query, forgetting its cost. -/
def evalQuery [Functor m] (M : ModelM Q m Cost) (q : Q α) : m α :=
  (M.runQuery q).value

/-- Construct a model whose query costs are independent of execution. -/
def ofCost [Functor m] (evalQuery : {α : Type u} → Q α → m α)
    (cost : {α : Type u} → Q α → Cost) : ModelM Q m Cost where
  runQuery q := AddWriterT.mk ((fun a => ⟨a, cost q⟩) <$> evalQuery q)

@[simp] theorem ofCost_evalQuery [Functor m] [LawfulFunctor m]
    (evalQuery : {α : Type u} → Q α → m α) (cost : {α : Type u} → Q α → Cost) (q : Q α) :
    (ofCost @evalQuery @cost).evalQuery q = evalQuery q := by
  simp [ofCost, ModelM.evalQuery, AddWriterT.value]

@[simp] theorem ofCost_runQuery [Functor m]
    (evalQuery : {α : Type u} → Q α → m α) (cost : {α : Type u} → Q α → Cost) (q : Q α) :
    ((ofCost @evalQuery @cost).runQuery q).run =
      (fun a => (⟨a, cost q⟩ : AddWriter Cost α)) <$> evalQuery q := rfl

/-- Fixed-cost query execution at a concrete state. -/
@[simp, grind =] theorem ofCost_runQuery_state
    (evalQuery : {α : Type u} → Q α → StateM σ α)
    (cost : {α : Type u} → Q α → Cost) (q : Q α) (s : σ) :
    ((ofCost @evalQuery @cost).runQuery q).run s =
      ((⟨(evalQuery q s).fst, cost q⟩ : AddWriter Cost α), (evalQuery q s).snd) := rfl

@[simp] theorem runQuery_value [Functor m] (M : ModelM Q m Cost) (q : Q α) :
    (M.runQuery q).value = M.evalQuery q := rfl

/-- Regard a `Model` as a `ModelM` over `Id`. -/
def ofModel (M : Algolean.Algorithms.Model Q Cost) : ModelM Q Id Cost :=
  ofCost (fun q => M.evalQuery q) M.cost

@[simp] theorem ofModel_evalQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).evalQuery q = M.evalQuery q := rfl

@[simp] theorem ofModel_runQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    ((ofModel M).runQuery q).run = ⟨M.evalQuery q, M.cost q⟩ := rfl

/-- Sum query languages, preserving each branch's joint interpretation. -/
def sum {Q₂ : Type u → Type x} (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) :
    ModelM (fun α => Sum (Q α) (Q₂ α)) m Cost where
  runQuery
    | .inl q => M₁.runQuery q
    | .inr q => M₂.runQuery q

@[simp] theorem sum_runQuery_inl {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).runQuery (.inl q) = M₁.runQuery q := rfl

@[simp] theorem sum_runQuery_inr {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).runQuery (.inr q) = M₂.runQuery q := rfl

@[simp] theorem sum_evalQuery_inl [Functor m] {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).evalQuery (.inl q) = M₁.evalQuery q := rfl

@[simp] theorem sum_evalQuery_inr [Functor m] {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).evalQuery (.inr q) = M₂.evalQuery q := rfl

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
    simp only [runM, evalM, FreeM.liftM, AddWriterT.value_bind] at ih ⊢
    simp only [AddWriterT.value] at ih
    simp only [ModelM.evalQuery, AddWriterT.value, bind_map_left, ih]

@[simp] theorem costM_pure [Monad m] [LawfulMonad m] [AddZero Cost]
    (a : α) (M : ModelM Q m Cost) :
    costM (pure a : Prog Q α) M = pure 0 := by
  simp [costM]

@[simp] theorem costM_liftBind [Monad m] [LawfulMonad m] [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelM Q m Cost) :
    costM (FreeM.lift q >>= f) M =
      ((M.runQuery q).run >>= fun a => (a.tell + ·) <$> costM (f a.ret) M) := by
  simp [costM, runM, AddWriterT.cost, AddWriterT.run_bind]

@[simp] theorem costM_lift [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (M : ModelM Q m Cost) :
    costM (FreeM.lift q) M = (M.runQuery q).cost := by
  simp [costM]

@[simp] theorem costM_map [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (f : α → β) (P : Prog Q α) (M : ModelM Q m Cost) :
    costM (f <$> P) M = costM P M := by
  simp [costM]

section State

/-- Joint execution of a pure program preserves the state and records zero cost. -/
@[simp, grind =] theorem runM_pure_state [AddZero Cost]
    (M : ModelM Q (StateM σ) Cost) (a : α) (s : σ) :
    ((pure a : Prog Q α).runM M).run s = ((⟨a, 0⟩ : AddWriter Cost α), s) := rfl

/-- Joint execution supplies the same query outcome to the continuation and the cost sum. -/
@[simp, grind =] theorem runM_liftBind_state [AddZero Cost]
    (M : ModelM Q (StateM σ) Cost) (q : Q α) (f : α → Prog Q β) (s : σ) :
    (runM (FreeM.liftBind q f) M).run s =
      let first := (M.runQuery q).run s
      let rest := ((f first.fst.ret).runM M).run first.snd
      ((⟨rest.fst.ret, first.fst.tell + rest.fst.tell⟩ : AddWriter Cost β), rest.snd) := rfl

/-- Joint execution rule for the lifted-query bind notation. -/
@[simp, grind =] theorem runM_lift_bind_state [AddZero Cost]
    (M : ModelM Q (StateM σ) Cost) (q : Q α) (f : α → Prog Q β) (s : σ) :
    (runM (FreeM.lift q >>= f) M).run s =
      let first := (M.runQuery q).run s
      let rest := ((f first.fst.ret).runM M).run first.snd
      ((⟨rest.fst.ret, first.fst.tell + rest.fst.tell⟩ : AddWriter Cost β), rest.snd) := rfl

/-- Execute the selected branch without hiding the conditional inside the interpreter. -/
@[simp] theorem runM_ite_state [AddZero Cost]
    (condition : Prop) [Decidable condition] (yes no : Prog Q α)
    (M : ModelM Q (StateM σ) Cost) (s : σ) :
    (runM (if condition then yes else no) M).run s =
      if condition then (yes.runM M).run s else (no.runM M).run s := by
  split <;> rfl

/-- Recover evaluation from joint execution at a concrete state. -/
@[simp, grind =] theorem evalM_eq_runM_state [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q (StateM σ) Cost) (s : σ) :
    P.evalM M s = (((P.runM M).run s).fst.ret, ((P.runM M).run s).snd) := by
  rw [← runM_value]
  rfl

/-- Recover cost from joint execution at a concrete state. -/
@[simp, grind =] theorem costM_eq_runM_state [AddZero Cost]
    (P : Prog Q α) (M : ModelM Q (StateM σ) Cost) (s : σ) :
    P.costM M s = (((P.runM M).run s).fst.tell, ((P.runM M).run s).snd) := rfl

/-- Cost accounting preserves the final state of ordinary evaluation. -/
@[simp] theorem costM_state [AddZero Cost] (P : Prog Q α)
    (M : ModelM Q (StateM σ) Cost) (s : σ) :
    (P.costM M s).snd = (P.evalM M s).snd := by
  simp

end State

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

/-- A handler exposing both query results and accumulated costs to postconditions. -/
def costHandler [Functor m] [Add Cost] [WP m ps] (M : ModelM Q m Cost) :
    LHandler Q (.arg Cost ps) :=
  LHandler.ofInterp (m := AddWriterT Cost m) (fun _ q => M.runQuery q)

/-- Evaluate a cost-aware state-model query's postcondition from its joint outcome. -/
@[simp] theorem costHandler_apply_state [Add Cost]
    (M : ModelM Q (StateM σ) Cost) (q : Q α)
    (post : PostCond α (.arg Cost (.arg σ .pure))) (initial : Cost) (s : σ) :
    (M.costHandler q).apply post initial s =
      post.fst ((M.runQuery q).run s).fst.ret
        (initial + ((M.runQuery q).run s).fst.tell) ((M.runQuery q).run s).snd := rfl

/-- Register joint execution for cost-aware `mvcgen` reasoning. -/
@[reducible] def hasCostHandler [Functor m] [Add Cost] [WP m ps]
    (M : ModelM Q m Cost) : HasHandler Q (.arg Cost ps) where
  handler := M.costHandler

/-- The cost-aware handler agrees with joint program execution. -/
theorem wp_eq_wp_runM [Monad m] [AddMonoid Cost] [WPMonad m ps]
    (M : ModelM Q m Cost) (P : Prog Q α) :
    wpH M.costHandler P = wp (P.runM M) :=
  wpH_ofInterp_eq_wp_liftM (m := AddWriterT Cost m) (fun _ q => M.runQuery q) P

/-- The logical handler induced by `M.evalQuery`. -/
def handler [Functor m] [WP m ps] (M : ModelM Q m Cost) : LHandler Q ps :=
  LHandler.ofInterp (m := m) (fun _ q => M.evalQuery q)

@[simp] theorem handler_sum [Functor m] [WP m ps] {Q₂ : Type u → Type x}
    (M₁ : ModelM Q m Cost) (M₂ : ModelM Q₂ m Cost) (q : Q α ⊕ Q₂ α) :
    (M₁.sum M₂).handler q = LHandler.sum M₁.handler M₂.handler q := by
  cases q <;> rfl

/-- Use `M.handler` as the logical handler for `Prog Q`. -/
@[reducible] def hasHandler [Functor m] [WP m ps] (M : ModelM Q m Cost) : HasHandler Q ps where
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
  let _inst := M.hasHandler
  exact Cslib.FreeM.Spec.lift_FreeM q

/-- The query rule for postconditions that also observe accumulated cost. -/
theorem ModelM.cost_query_spec [Monad m] [AddMonoid Cost] [WPMonad m ps]
    (M : ModelM Q m Cost) (q : Q α) {Q' : PostCond α (.arg Cost ps)} :
    let _ : HasHandler Q (.arg Cost ps) := M.hasCostHandler
    Triple (FreeM.lift q : Prog Q α) (wp⟦M.runQuery q⟧ Q') Q' := by
  let _inst := M.hasCostHandler
  exact Cslib.FreeM.Spec.lift_FreeM q

end WeakestPrecondition

end Algolean.Algorithms
