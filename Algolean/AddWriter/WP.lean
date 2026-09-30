/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.AddWriter.Transformer
public import Std.Do

/-!
# Weakest preconditions for additive writer computations

The extra postcondition argument is an accumulated cost. Starting it at zero gives the cost
reported by `run`; an arbitrary initial cost permits compositional reasoning across binds.
-/

@[expose] public section

namespace Algolean.AddWriterT

open Std.Do Std.Do.WPMonad

variable {Cost : Type u} {m : Type u → Type v} {ps : PostShape.{u}}

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

/-- Writer weakest preconditions expose accumulated cost before the underlying post-shape. -/
instance [Functor m] [Add Cost] [WP m ps] : WP (AddWriterT Cost m) (.arg Cost ps) where
  wp x := wp x.toStateT

/-- The cost-accumulator interpretation respects pure and bind. -/
instance [Monad m] [AddMonoid Cost] [WPMonad m ps] :
    WPMonad (AddWriterT Cost m) (.arg Cost ps) where
  wp_pure a := by
    change wp (toStateT (pure a : AddWriterT Cost m _)) = _
    rw [toStateT_pure, wp_pure]
  wp_bind x f := by
    change wp (toStateT (x >>= f)) = _
    rw [toStateT_bind, wp_bind]
    rfl

/-- Expose the underlying state interpretation to verification condition generation. -/
theorem wp_eq_wp_toStateT [Functor m] [Add Cost] [WP m ps]
    (x : AddWriterT Cost m α) : wp x = wp x.toStateT := rfl

/-- A writer over state exposes its result, accumulated cost, and final physical state. -/
@[simp] theorem wp_apply_state [Add Cost] (x : AddWriterT Cost (StateM σ) α)
    (Q : PostCond α (.arg Cost (.arg σ .pure))) (initial : Cost) (s : σ) :
    (wp x).apply Q initial s =
      Q.fst (x.run s).fst.ret (initial + (x.run s).fst.tell) (x.run s).snd := rfl

/-- Optional state execution exposes either the exact joint result or its failure postcondition. -/
@[simp] theorem wp_apply_state_option [Add Cost] (x : AddWriterT Cost (StateT σ Option) α)
    (Q : PostCond α (.arg Cost (.arg σ (.except PUnit .pure)))) (initial : Cost) (s : σ) :
    (wp x).apply Q initial s =
      match x.run s with
      | none => Q.snd.fst PUnit.unit
      | some (result, final) => Q.fst result.ret (initial + result.tell) final := by
  dsimp [wp_eq_wp_toStateT, wp, toStateT, PredTrans.apply]
  simp only [StateT.run_map]
  dsimp only [StateT.run]
  cases x.run s <;> rfl

end Algolean.AddWriterT
