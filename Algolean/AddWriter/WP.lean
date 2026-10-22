/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.AddWriter.Transformer
public import Std.WP

/-!
# Weakest preconditions for additive writer computations

The extra postcondition argument is an accumulated cost. Starting it at zero gives the cost
reported by `run`; an arbitrary initial cost permits compositional reasoning across binds.
-/

@[expose] public section

namespace Algolean.AddWriterT

open Lean.Order Std.WP

variable {Cost : Type u} {m : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Assertion Pred] [Assertion EPred]

/-- Interpret the writer output as an increment to a logical cost accumulator. -/
def toStateT [Functor m] [Add Cost] (x : AddWriterT Cost m α) : StateT Cost m α :=
  fun initial => (fun a => (a.ret, initial + a.tell)) <$> x.run

/-- Expose the accumulated cost without unfolding the state transformer. -/
@[simp] theorem toStateT_run [Functor m] [Add Cost]
    (x : AddWriterT Cost m α) (initial : Cost) :
    x.toStateT.run initial = (fun a => (a.ret, initial + a.tell)) <$> x.run := rfl

@[simp] theorem toStateT_pure [Monad m] [LawfulMonad m] [AddZeroClass Cost] (a : α) :
    toStateT (pure a : AddWriterT Cost m α) = pure a := by
  funext initial
  simp [toStateT]
  rfl

@[simp] theorem toStateT_bind [Monad m] [LawfulMonad m] [AddSemigroup Cost]
    (x : AddWriterT Cost m α) (f : α → AddWriterT Cost m β) :
    toStateT (x >>= f) = (toStateT x >>= fun a => toStateT (f a)) := by
  apply StateT.ext
  intro initial
  rw [StateT.run_bind]
  simp [toStateT, StateT.run, bind_map_left, add_assoc]

/-- Writer weakest preconditions expose accumulated cost before the underlying assertions. -/
instance [Functor m] [Add Cost] [WP (m (α × Cost)) (α × Cost) Pred EPred] :
    WP (AddWriterT Cost m α) α (Cost → Pred) EPred where
  wpTrans x := WP.wpTrans x.toStateT
  wp_trans_monotone x := WP.wp_trans_monotone x.toStateT

/-- The cost-accumulator interpretation respects pure and bind. -/
instance [Monad m] [AddMonoid Cost] [WPMonad m Pred EPred] :
    WPMonad (AddWriterT Cost m) (Cost → Pred) EPred where
  toWP _ := inferInstance
  pure_le_wp_pure a Q E := by
    change Q a ⊑ wp (toStateT (pure a : AddWriterT Cost m _)) Q E
    rw [toStateT_pure]
    exact WPMonad.pure_le_wp_pure a Q E
  bind_le_wp_bind x f Q E := by
    change wp x.toStateT (fun a => wp (f a).toStateT Q E) E ⊑
      wp (toStateT (x >>= f)) Q E
    rw [toStateT_bind]
    exact WPMonad.bind_le_wp_bind x.toStateT (fun a => (f a).toStateT) Q E

/-- Expose the underlying state interpretation to verification condition generation. -/
theorem wp_eq_wp_toStateT [Functor m] [Add Cost] [WP (m (α × Cost)) (α × Cost) Pred EPred]
    (x : AddWriterT Cost m α) : wp x = wp x.toStateT := rfl

/-- A writer over state exposes its result, accumulated cost, and final physical state. -/
@[simp] theorem wp_apply_state [Add Cost] (x : AddWriterT Cost (StateM σ) α)
    (Q : α → Cost → σ → Prop) (E : EStack⟨⟩) (initial : Cost) (s : σ) :
    wp x Q E initial s =
      Q (x.run s).fst.ret (initial + (x.run s).fst.tell) (x.run s).snd := rfl

/-- Optional state execution exposes either the exact joint result or its failure postcondition. -/
@[simp] theorem wp_apply_state_option [Add Cost] (x : AddWriterT Cost (StateT σ Option) α)
    (Q : α → Cost → σ → Prop) (E : Unit → Prop) (initial : Cost) (s : σ) :
    wp x Q E initial s =
      match x.run s with
      | none => E ()
      | some (result, final) => Q result.ret (initial + result.tell) final := by
  dsimp [wp_eq_wp_toStateT, wp, WP.wpTrans, toStateT, PredTrans.pushArg]
  simp only [StateT.run_map]
  dsimp only [StateT.run]
  cases x.run s <;> rfl

end Algolean.AddWriterT
