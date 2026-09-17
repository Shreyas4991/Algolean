/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.AddWriter.WP
public import Algolean.ModelM

/-!
# Monadic query models with joint state and cost semantics

`ModelStateM` interprets each query with its result and cost in the same monadic execution.
Unlike `ModelM`, costs may depend on the state or on the query outcome. The monad remains generic:
stateful and probabilistic interpretations both retain the correlation between results and costs.
`Prog.evalStateM` evaluates a program, `Prog.runStateM` records its result and accumulated cost,
and `Prog.costStateM` returns the accumulated cost.

`ModelStateM.handler` and `ModelStateM.hasHandler` provide weakest-precondition semantics
for `mvcgen` when the monad has a `Std.Do.WPMonad` instance.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib

/-- A query model whose queries are evaluated in the monad `m`. -/
structure ModelStateM (Q : Type u → Type v) (m : Type u → Type w) (Cost : Type u) where
  /-- Execute a query, retaining its result and cost in the same effect branch. -/
  runQuery : Q α → AddWriterT Cost m α

namespace ModelStateM

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Evaluate a query, forgetting its cost. -/
def evalQuery [Functor m] (M : ModelStateM Q m Cost) (q : Q α) : m α :=
  (M.runQuery q).value

/-- Construct a model whose query costs are independent of execution. -/
def ofCost [Functor m] (evalQuery : {α : Type u} → Q α → m α)
    (cost : {α : Type u} → Q α → Cost) : ModelStateM Q m Cost where
  runQuery q := AddWriterT.mk ((fun a => ⟨a, cost q⟩) <$> evalQuery q)

@[simp] theorem ofCost_evalQuery [Functor m] [LawfulFunctor m]
    (evalQuery : {α : Type u} → Q α → m α) (cost : {α : Type u} → Q α → Cost) (q : Q α) :
    (ofCost @evalQuery @cost).evalQuery q = evalQuery q := by
  simp [ofCost, ModelStateM.evalQuery, AddWriterT.value]

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

@[simp] theorem runQuery_value [Functor m] (M : ModelStateM Q m Cost) (q : Q α) :
    (M.runQuery q).value = M.evalQuery q := rfl

/-- Regard a `Model` as a `ModelStateM` over `Id`. -/
def ofModel (M : Algolean.Algorithms.Model Q Cost) : ModelStateM Q Id Cost :=
  ofCost (fun q => M.evalQuery q) M.cost

@[simp] theorem ofModel_evalQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    (ofModel M).evalQuery q = M.evalQuery q := rfl

@[simp] theorem ofModel_runQuery (M : Algolean.Algorithms.Model Q Cost) (q : Q α) :
    ((ofModel M).runQuery q).run = ⟨M.evalQuery q, M.cost q⟩ := rfl

/-- Sum query languages, preserving each branch's joint interpretation. -/
def sum {Q₂ : Type u → Type x} (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) :
    ModelStateM (fun α => Sum (Q α) (Q₂ α)) m Cost where
  runQuery
    | .inl q => M₁.runQuery q
    | .inr q => M₂.runQuery q

@[simp] theorem sum_runQuery_inl {Q₂ : Type u → Type x}
    (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).runQuery (.inl q) = M₁.runQuery q := rfl

@[simp] theorem sum_runQuery_inr {Q₂ : Type u → Type x}
    (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).runQuery (.inr q) = M₂.runQuery q := rfl

@[simp] theorem sum_evalQuery_inl [Functor m] {Q₂ : Type u → Type x}
    (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) (q : Q α) :
    (M₁.sum M₂).evalQuery (.inl q) = M₁.evalQuery q := rfl

@[simp] theorem sum_evalQuery_inr [Functor m] {Q₂ : Type u → Type x}
    (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) (q : Q₂ α) :
    (M₁.sum M₂).evalQuery (.inr q) = M₂.evalQuery q := rfl

end ModelStateM

namespace Prog

variable {Q : Type u → Type v} {m : Type u → Type w} {Cost : Type u}

/-- Evaluate a query program in the semantic monad of `M`. -/
def evalStateM [Monad m] (P : Prog Q α) (M : ModelStateM Q m Cost) : m α :=
  P.liftM M.evalQuery

/-- Evaluate a query program while recording the accumulated query cost with each result. -/
def runStateM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelStateM Q m Cost) : AddWriterT Cost m α :=
  P.liftM M.runQuery

/-- The accumulated query cost of each execution of a program. -/
def costStateM [Monad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelStateM Q m Cost) : m Cost :=
  (P.runStateM M).cost

@[simp] theorem evalStateM_pure [Monad m] (a : α) (M : ModelStateM Q m Cost) :
    evalStateM (pure a : Prog Q α) M = pure a := rfl

@[simp] theorem evalStateM_liftBind [Monad m]
    (q : Q α) (f : α → Prog Q β) (M : ModelStateM Q m Cost) :
    evalStateM (FreeM.lift q >>= f) M = (M.evalQuery q >>= fun a => evalStateM (f a) M) := rfl

@[simp] theorem evalStateM_lift [Monad m] [LawfulMonad m]
    (q : Q α) (M : ModelStateM Q m Cost) :
    evalStateM (FreeM.lift q) M = M.evalQuery q := by
  simp [evalStateM]

@[simp] theorem evalStateM_bind [Monad m] [LawfulMonad m]
    (P : Prog Q α) (f : α → Prog Q β) (M : ModelStateM Q m Cost) :
    evalStateM (P >>= f) M = (evalStateM P M >>= fun a => evalStateM (f a) M) := by
  simp [evalStateM]

@[simp] theorem evalStateM_map [Monad m] [LawfulMonad m]
    (f : α → β) (P : Prog Q α) (M : ModelStateM Q m Cost) :
    evalStateM (f <$> P) M = f <$> evalStateM P M := by
  simp [evalStateM]

@[simp] theorem runStateM_pure [Monad m] [AddZero Cost]
    (a : α) (M : ModelStateM Q m Cost) :
    runStateM (pure a : Prog Q α) M = pure a := rfl

@[simp] theorem runStateM_liftBind [Monad m] [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelStateM Q m Cost) :
    runStateM (FreeM.lift q >>= f) M = (M.runQuery q >>= fun a => runStateM (f a) M) := rfl

@[simp] theorem runStateM_lift [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (M : ModelStateM Q m Cost) :
    runStateM (FreeM.lift q) M = M.runQuery q := by
  simp [runStateM]

@[simp] theorem runStateM_bind [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q α) (f : α → Prog Q β) (M : ModelStateM Q m Cost) :
    runStateM (P >>= f) M = (runStateM P M >>= fun a => runStateM (f a) M) := by
  simp [runStateM]

@[simp] theorem runStateM_map [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (f : α → β) (P : Prog Q α) (M : ModelStateM Q m Cost) :
    runStateM (f <$> P) M = f <$> runStateM P M := by
  simp [runStateM]

/-- Forgetting the cost component of the joint semantics recovers `evalStateM`. -/
@[simp] theorem runStateM_value [Monad m] [LawfulMonad m] [AddZero Cost]
    (P : Prog Q α) (M : ModelStateM Q m Cost) :
    (P.runStateM M).value = P.evalStateM M := by
  induction P with
  | pure a => simp
  | liftBind q f ih =>
    simp only [runStateM, evalStateM, FreeM.liftM, AddWriterT.value_bind] at ih ⊢
    simp only [AddWriterT.value] at ih
    simp only [ModelStateM.evalQuery, AddWriterT.value, bind_map_left, ih]

@[simp] theorem costStateM_pure [Monad m] [LawfulMonad m] [AddZero Cost]
    (a : α) (M : ModelStateM Q m Cost) :
    costStateM (pure a : Prog Q α) M = pure 0 := by
  simp [costStateM]

@[simp] theorem costStateM_liftBind [Monad m] [LawfulMonad m] [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : ModelStateM Q m Cost) :
    costStateM (FreeM.lift q >>= f) M =
      ((M.runQuery q).run >>= fun a => (a.tell + ·) <$> costStateM (f a.ret) M) := by
  simp [costStateM, runStateM, AddWriterT.cost, AddWriterT.run_bind]

@[simp] theorem costStateM_lift [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (q : Q α) (M : ModelStateM Q m Cost) :
    costStateM (FreeM.lift q) M = (M.runQuery q).cost := by
  simp [costStateM]

@[simp] theorem costStateM_map [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (f : α → β) (P : Prog Q α) (M : ModelStateM Q m Cost) :
    costStateM (f <$> P) M = costStateM P M := by
  simp [costStateM]

section State

/-- Joint execution of a pure program preserves the state and records zero cost. -/
@[simp, grind =] theorem runStateM_pure_state [AddZero Cost]
    (M : ModelStateM Q (StateM σ) Cost) (a : α) (s : σ) :
    ((pure a : Prog Q α).runStateM M).run s = ((⟨a, 0⟩ : AddWriter Cost α), s) := rfl

/-- Joint execution supplies the same query outcome to the continuation and the cost sum. -/
@[simp, grind =] theorem runStateM_liftBind_state [AddZero Cost]
    (M : ModelStateM Q (StateM σ) Cost) (q : Q α) (f : α → Prog Q β) (s : σ) :
    (runStateM (FreeM.liftBind q f) M).run s =
      let first := (M.runQuery q).run s
      let rest := ((f first.fst.ret).runStateM M).run first.snd
      ((⟨rest.fst.ret, first.fst.tell + rest.fst.tell⟩ : AddWriter Cost β), rest.snd) := rfl

/-- Joint execution rule for the lifted-query bind notation. -/
@[simp, grind =] theorem runStateM_lift_bind_state [AddZero Cost]
    (M : ModelStateM Q (StateM σ) Cost) (q : Q α) (f : α → Prog Q β) (s : σ) :
    (runStateM (FreeM.lift q >>= f) M).run s =
      let first := (M.runQuery q).run s
      let rest := ((f first.fst.ret).runStateM M).run first.snd
      ((⟨rest.fst.ret, first.fst.tell + rest.fst.tell⟩ : AddWriter Cost β), rest.snd) := rfl

/-- Execute the selected branch without hiding the conditional inside the interpreter. -/
@[simp] theorem runStateM_ite_state [AddZero Cost]
    (condition : Prop) [Decidable condition] (yes no : Prog Q α)
    (M : ModelStateM Q (StateM σ) Cost) (s : σ) :
    (runStateM (if condition then yes else no) M).run s =
      if condition then (yes.runStateM M).run s else (no.runStateM M).run s := by
  split <;> rfl

/-- Recover evaluation from joint execution at a concrete state. -/
@[simp, grind =] theorem evalStateM_eq_runStateM_state [AddZero Cost]
    (P : Prog Q α) (M : ModelStateM Q (StateM σ) Cost) (s : σ) :
    P.evalStateM M s = (((P.runStateM M).run s).fst.ret, ((P.runStateM M).run s).snd) := by
  rw [← runStateM_value]
  rfl

/-- Recover cost from joint execution at a concrete state. -/
@[simp, grind =] theorem costStateM_eq_runStateM_state [AddZero Cost]
    (P : Prog Q α) (M : ModelStateM Q (StateM σ) Cost) (s : σ) :
    P.costStateM M s = (((P.runStateM M).run s).fst.tell, ((P.runStateM M).run s).snd) := rfl

/-- Cost accounting preserves the final state of ordinary evaluation. -/
@[simp] theorem costStateM_state [AddZero Cost] (P : Prog Q α)
    (M : ModelStateM Q (StateM σ) Cost) (s : σ) :
    (P.costStateM M s).snd = (P.evalStateM M s).snd := by
  simp

end State

section OfModel

/-- Evaluating with `ofModel M` is the same as evaluating with `M`. -/
@[simp] theorem evalStateM_ofModel (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.evalStateM (ModelStateM.ofModel M)) = P.eval M := rfl

/-- The cost of a query followed by a program under `ofModel`. -/
@[simp] theorem costStateM_ofModel_liftBind [AddZero Cost]
    (q : Q α) (f : α → Prog Q β) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (Prog.costStateM (FreeM.lift q >>= f) (ModelStateM.ofModel M)) =
      M.cost q + Id.run ((f (M.evalQuery q)).costStateM (ModelStateM.ofModel M)) := rfl

/-- Computing cost with `ofModel M` gives `Prog.time M`. -/
@[simp] theorem costStateM_ofModel [AddZero Cost]
    (P : Prog Q α) (M : Algolean.Algorithms.Model Q Cost) :
    Id.run (P.costStateM (ModelStateM.ofModel M)) = P.time M := by
  induction P with
  | pure a => rfl
  | liftBind q f ih => exact congrArg (M.cost q + ·) (ih (M.evalQuery q))

end OfModel

section Reduction

variable {Q₁ Q₂ : Type u → Type u}

/-- A query reduction preserving each query also preserves program evaluation. -/
theorem reduceProg_evalStateM [Monad m] [LawfulMonad m]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelStateM Q₁ m Cost₁) (M₂ : ModelStateM Q₂ m Cost₂)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).evalStateM M₂ = M₁.evalQuery q) :
    (P.reduceProg red).evalStateM M₂ = P.evalStateM M₁ :=
  reduceProg_liftM P red M₁.evalQuery M₂.evalQuery hCorrect

/-- A query reduction preserving `runStateM` also preserves `runStateM` for every program. -/
theorem reduceProg_runStateM [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelStateM Q₁ m Cost) (M₂ : ModelStateM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).runStateM M₂ = M₁.runQuery q) :
    (P.reduceProg red).runStateM M₂ = P.runStateM M₁ :=
  reduceProg_liftM P red M₁.runQuery M₂.runQuery hCorrect

/-- A query reduction preserving `runStateM` also preserves accumulated program costs. -/
theorem reduceProg_costStateM [Monad m] [LawfulMonad m] [AddMonoid Cost]
    (P : Prog Q₁ α) (red : Reduction Q₁ Q₂)
    (M₁ : ModelStateM Q₁ m Cost) (M₂ : ModelStateM Q₂ m Cost)
    (hCorrect : ∀ {ι} (q : Q₁ ι), (red.reduce q).runStateM M₂ = M₁.runQuery q) :
    (P.reduceProg red).costStateM M₂ = P.costStateM M₁ :=
  congrArg AddWriterT.cost (reduceProg_runStateM P red M₁ M₂ hCorrect)

end Reduction

end Prog

section WeakestPrecondition

open Cslib.FreeM Std.Do

variable {ps : PostShape.{u}}

namespace ModelStateM

/-- A handler exposing both query results and accumulated costs to postconditions. -/
def costHandler [Functor m] [Add Cost] [WP m ps] (M : ModelStateM Q m Cost) :
    LHandler Q (.arg Cost ps) :=
  LHandler.ofInterp (m := AddWriterT Cost m) (fun _ q => M.runQuery q)

/-- Evaluate a cost-aware state-model query's postcondition from its joint outcome. -/
@[simp] theorem costHandler_apply_state [Add Cost]
    (M : ModelStateM Q (StateM σ) Cost) (q : Q α)
    (post : PostCond α (.arg Cost (.arg σ .pure))) (initial : Cost) (s : σ) :
    (M.costHandler q).apply post initial s =
      post.fst ((M.runQuery q).run s).fst.ret
        (initial + ((M.runQuery q).run s).fst.tell) ((M.runQuery q).run s).snd := rfl

/-- Register joint execution for cost-aware `mvcgen` reasoning. -/
@[reducible] def hasCostHandler [Functor m] [Add Cost] [WP m ps]
    (M : ModelStateM Q m Cost) : HasHandler Q (.arg Cost ps) where
  handler := M.costHandler

/-- The cost-aware handler agrees with joint program execution. -/
theorem wp_eq_wp_runStateM [Monad m] [AddMonoid Cost] [WPMonad m ps]
    (M : ModelStateM Q m Cost) (P : Prog Q α) :
    wpH M.costHandler P = wp (P.runStateM M) :=
  wpH_ofInterp_eq_wp_liftM (m := AddWriterT Cost m) (fun _ q => M.runQuery q) P

/-- The logical handler induced by `M.evalQuery`. -/
def handler [Functor m] [WP m ps] (M : ModelStateM Q m Cost) : LHandler Q ps :=
  LHandler.ofInterp (m := m) (fun _ q => M.evalQuery q)

@[simp] theorem handler_sum [Functor m] [WP m ps] {Q₂ : Type u → Type x}
    (M₁ : ModelStateM Q m Cost) (M₂ : ModelStateM Q₂ m Cost) (q : Q α ⊕ Q₂ α) :
    (M₁.sum M₂).handler q = LHandler.sum M₁.handler M₂.handler q := by
  cases q <;> rfl

/-- Use `M.handler` as the logical handler for `Prog Q`. -/
@[reducible] def hasHandler [Functor m] [WP m ps] (M : ModelStateM Q m Cost) : HasHandler Q ps where
  handler := M.handler

/-- The weakest precondition given by `M.handler` agrees with that of `Prog.evalStateM M`. -/
theorem wp_eq_wp_evalStateM [Monad m] [WPMonad m ps]
    (M : ModelStateM Q m Cost) (P : Prog Q α) :
    wpH M.handler P = wp (P.evalStateM M) :=
  wpH_ofInterp_eq_wp_liftM (m := m) (fun _ q => M.evalQuery q) P

end ModelStateM

/-- The query rule stated directly through the semantic monad's weakest precondition. -/
theorem ModelStateM.query_spec [Monad m] [WPMonad m ps]
    (M : ModelStateM Q m Cost) (q : Q α) {Q' : PostCond α ps} :
    let _ : HasHandler Q ps := M.hasHandler
    Triple (FreeM.lift q : Prog Q α) (wp⟦M.evalQuery q⟧ Q') Q' := by
  let _inst := M.hasHandler
  exact Cslib.FreeM.Spec.lift_FreeM q

/-- The query rule for postconditions that also observe accumulated cost. -/
theorem ModelStateM.cost_query_spec [Monad m] [AddMonoid Cost] [WPMonad m ps]
    (M : ModelStateM Q m Cost) (q : Q α) {Q' : PostCond α (.arg Cost ps)} :
    let _ : HasHandler Q (.arg Cost ps) := M.hasCostHandler
    Triple (FreeM.lift q : Prog Q α) (wp⟦M.runQuery q⟧ Q') Q' := by
  let _inst := M.hasCostHandler
  exact Cslib.FreeM.Spec.lift_FreeM q

end WeakestPrecondition

end Algolean.Algorithms
