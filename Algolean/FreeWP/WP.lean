/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Std.WP

/-!
# Weakest preconditions for `FreeM` programs

Logical effect handlers interpret `FreeM` into `Lean.Order.PredTrans`. Monotone handlers
provide `Std.WP.WPMonad` instances and specifications for `vcgen`. Relational operation
contracts can supply handlers independently of an executable interpretation.
-/

@[expose] public section

namespace Cslib.FreeM

open Lean.Order Std.WP

universe u v w z r

variable {F G : Type u → Type v} {Pred : Type w} {EPred : Type z}
variable [Assertion Pred] [Assertion EPred] {α β : Type u}

/-- A monotone predicate transformer for every primitive operation. -/
structure LHandler (F : Type u → Type v) (Pred : Type w) (EPred : Type z)
    [Assertion Pred] [Assertion EPred] where
  /-- Interpret a primitive operation. -/
  trans {ι : Type u} : F ι → PredTrans Pred EPred ι
  /-- Weaker postconditions yield weaker preconditions. -/
  monotone {ι : Type u} (op : F ι) : (trans op).monotone

instance : CoeFun (LHandler F Pred EPred) (fun _ => {ι : Type u} → F ι → PredTrans Pred EPred ι) :=
  ⟨LHandler.trans⟩

/-- Independent preconditions and relational postconditions for primitive operations. -/
structure OperationSpec (F : Type u → Type v) : Type (max (u + 1) v) where
  /-- The operation is enabled. -/
  pre {ι : Type u} (op : F ι) : Prop
  /-- The operation permits this result. -/
  post {ι : Type u} (op : F ι) (out : ι) : Prop

namespace OperationSpec

/-- Require the operation to be enabled and every permitted result to satisfy the continuation. -/
def toHandler (S : OperationSpec F) : LHandler F Prop EStack⟨⟩ where
  trans op := ⟨fun Q _ => S.pre op ∧ ∀ out, S.post op out → Q out⟩
  monotone op := by
    intro Q Q' E E' _ hQ
    exact fun ⟨hp, h⟩ => ⟨hp, fun a ha => hQ a (h a ha)⟩

@[simp] theorem apply_toHandler (S : OperationSpec F) {ι : Type u} (op : F ι)
    (Q : ι → Prop) (E : EStack⟨⟩) :
    (S.toHandler op).apply Q E = (S.pre op ∧ ∀ out, S.post op out → Q out) := rfl

end OperationSpec

namespace LHandler

/-- Combine handlers for disjoint effect signatures. -/
def sum (H₁ : LHandler F Pred EPred) (H₂ : LHandler G Pred EPred) :
    LHandler (fun α => F α ⊕ G α) Pred EPred where
  trans op := Sum.elim H₁.trans H₂.trans op
  monotone op := by cases op with
    | inl op => exact H₁.monotone op
    | inr op => exact H₂.monotone op

@[simp] theorem sum_inl (H₁ : LHandler F Pred EPred) (H₂ : LHandler G Pred EPred)
    {ι : Type u} (x : F ι) :
    LHandler.sum H₁ H₂ (Sum.inl x : F ι ⊕ G ι) = H₁ x := rfl

@[simp] theorem sum_inr (H₁ : LHandler F Pred EPred) (H₂ : LHandler G Pred EPred)
    {ι : Type u} (y : G ι) :
    LHandler.sum H₁ H₂ (Sum.inr y : F ι ⊕ G ι) = H₂ y := rfl

/-- Derive a logical handler from an interpreter into a monad with weakest preconditions. -/
def ofInterp {m : Type u → Type r} [∀ ι, WP (m ι) ι Pred EPred]
    (interp : ∀ ι : Type u, F ι → m ι) : LHandler F Pred EPred where
  trans op := WP.wpTrans (interp _ op)
  monotone op := WP.wp_trans_monotone (interp _ op)

@[simp] theorem ofInterp_apply {m : Type u → Type r} [∀ ι, WP (m ι) ι Pred EPred]
    (interp : ∀ ι : Type u, F ι → m ι) {ι : Type u} (op : F ι) :
    LHandler.ofInterp interp op = WP.wpTrans (interp ι op) := rfl

end LHandler

/-- Extend a logical handler to a free program using the universal property of `FreeM`. -/
def wpH (H : LHandler F Pred EPred) (x : FreeM F α) : PredTrans Pred EPred α :=
  x.liftM H.trans

@[simp] theorem wpH_pure (H : LHandler F Pred EPred) (a : α) :
    wpH H (pure a : FreeM F α) = Pure.pure a := rfl

theorem wpH_liftBind (H : LHandler F Pred EPred) {ι : Type u}
    (op : F ι) (k : ι → FreeM F α) :
    wpH H ((lift op : FreeM F ι) >>= k) = H op >>= fun x => wpH H (k x) := rfl

@[simp] theorem wpH_lift (H : LHandler F Pred EPred) {ι : Type u} (op : F ι) :
    wpH H (lift op : FreeM F ι) = H op := liftM_lift _ op

@[simp] theorem wpH_bind (H : LHandler F Pred EPred) (x : FreeM F α) (f : α → FreeM F β) :
    wpH H (x >>= f) = wpH H x >>= fun a => wpH H (f a) := liftM_bind H.trans x f

/-- The free extension of monotone primitive transformers is monotone. -/
theorem wpH_monotone (H : LHandler F Pred EPred) (x : FreeM F α) : (wpH H x).monotone := by
  induction x with
  | pure a => exact fun _ _ _ _ _ hQ => hQ a
  | lift_bind op k ih =>
    intro Q Q' E E' hE hQ
    exact H.monotone op _ _ _ _ hE (fun a => ih a _ _ _ _ hE hQ)

/-- Interpreting the syntax through logical handlers is sound for any `Std.WP.WPMonad`.
The new API assumes only refinement for pure and bind, so generic adequacy is an entailment. -/
theorem wpH_ofInterp_le_wp_liftM
    {m : Type u → Type r} [Monad m] [WPMonad m Pred EPred]
    (interp : ∀ ι : Type u, F ι → m ι) (x : FreeM F α) (Q : α → Pred) (E : EPred) :
    (wpH (LHandler.ofInterp interp) x).apply Q E ⊑
      wp (x.liftM (fun {_} => interp _)) Q E := by
  induction x with
  | pure a => exact WPMonad.pure_le_wp_pure a Q E
  | lift_bind op k ih =>
    exact PartialOrder.rel_trans
      (WP.wp_consequence (interp _ op) _ _ E (fun a => ih a))
      (WPMonad.bind_le_wp_bind (interp _ op) _ Q E)

/-- Select the default logical handler for a free effect signature. -/
class HasHandler (F : Type u → Type v) (Pred : outParam (Type w)) (EPred : outParam (Type z))
    [Assertion Pred] [Assertion EPred] where
  /-- The selected logical handler. -/
  handler : LHandler F Pred EPred

instance instWPFreeM [HasHandler F Pred EPred] : WP (FreeM F α) α Pred EPred where
  wpTrans := wpH HasHandler.handler
  wp_trans_monotone := wpH_monotone _

instance instWPMonadFreeM [HasHandler F Pred EPred] : WPMonad (FreeM F) Pred EPred where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x f Q E := by
    change (wpH _ x).apply _ E ⊑ (wpH _ (x >>= f)).apply Q E
    rw [wpH_bind]
    exact PartialOrder.rel_refl

/-- The WP of a primitive query is the transformer selected by its logical handler. -/
@[simp] theorem wp_lift [HasHandler F Pred EPred] (op : F α) (Q : α → Pred) (E : EPred) :
    wp (lift op : FreeM F α) Q E = (HasHandler.handler op).apply Q E := by
  change (wpH _ (lift op)).apply Q E = _
  rw [wpH_lift]

/-- The generic primitive-operation rule, with lower priority than effect-specific rules. -/
@[spec low]
theorem Spec.lift_FreeM [HasHandler F Pred EPred] (op : F α) {Q : α → Pred} {E : EPred} :
    Triple (lift op : FreeM F α) ((HasHandler.handler op).apply Q E) Q E :=
  ⟨by rw [wp_lift]⟩

end Cslib.FreeM
