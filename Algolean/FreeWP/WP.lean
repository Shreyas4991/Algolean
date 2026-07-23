/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free
public import Std.Do.PredTrans
public import Std.Do.WP.Basic
public import Std.Do.WP.Monad
public import Std.Do.Triple

/-!
# Weakest preconditions for `FreeM` programs

Weakest-precondition interpretation of `FreeM F` programs through `Std.Do`'s
predicate-transformer monad `PredTrans ps`. The universal property of `FreeM` lifts any
effect handler `F ι → PredTrans ps ι` to a unique monad morphism `wpH H = liftM H`,
so weakest preconditions are compositional in `FreeM`'s monadic structure. A
`[HasHandler F ps]` instance plugs `FreeM F` into `Std.Do`'s `WP`/`WPMonad`/`Triple`
infrastructure.

The WP's structural rules (`wpH_pure`, `wpH_bind`, …) are immediate from `liftM` being a monad
morphism; the adequacy theorem `wpH_ofInterp_eq_wp_liftM` — that WP-via-handler agrees with
`Std.Do`'s WP of the `liftM` interpretation — is the same statement of uniqueness.

For pure specifications, an `OperationSpec F` assigns an arbitrary precondition and relational
postcondition to every operation in `F`. Its `toHandler` method compiles these contracts into
logical handlers. This is the free-monad construction from Maillard et al.,
[*Dijkstra Monads for All*][Maillard2019]: because `FreeM F` imposes no equations on operation
trees, the primitive contracts extend freely to a compositional weakest-precondition semantics.

The design follows [Vistrup, Sammler, Jung. *Program Logics à la Carte.* POPL 2025], adapted
from coinductive ITrees to inductive `FreeM` and from Iris to `Std.Do`.

[Maillard2019]: https://arxiv.org/abs/1903.01237
-/

@[expose] public section

set_option mvcgen.warning false

namespace Cslib

open Std.Do

namespace FreeM

universe u v w

variable {F G : Type u → Type v} {ps : PostShape.{u}} {α β : Type u}

/-- A logical handler: an effect handler from `F` into the predicate-transformer monad
`PredTrans ps`. -/
abbrev LHandler (F : Type u → Type v) (ps : PostShape.{u}) : Type (max (u + 1) v) :=
  ∀ {ι : Type u}, F ι → PredTrans ps ι

/-- A relational specification for every operation in an indexed signature `F`.

An operation `op : F ι` packages its operation name and input and returns a value of type `ι`.
`pre op` must hold before invoking it, while `post op out` characterizes the outputs that the
operation is allowed to return. Because `FreeM F` is free of equations, these contracts may be
chosen independently for each operation. -/
structure OperationSpec (F : Type u → Type v) : Type (max (u + 1) v) where
  /-- Preconditions for primitive operations. -/
  pre {ι : Type u} (op : F ι) : Prop
  /-- Relational postconditions for primitive operations and their outputs. -/
  post {ι : Type u} (op : F ι) (out : ι) : Prop

namespace OperationSpec

/-- Compile relational operation contracts into a pure logical handler.

For `op : F ι` and a continuation postcondition `Q`, the resulting weakest precondition is
`S.pre op ∧ ∀ out, S.post op out → Q out`: the operation must be enabled, and every output
permitted by its relational postcondition must make the continuation safe. -/
def toHandler (S : OperationSpec F) : LHandler F .pure :=
  fun op =>
    { trans := fun Q =>
        spred(⌜S.pre op ∧ ∀ out, S.post op out → (Q.1 out).down⌝)
      conjunctiveRaw := by
        intro Q₁ Q₂
        aesop }

@[simp]
theorem apply_toHandler (S : OperationSpec F) {ι : Type u} (op : F ι)
    (Q : PostCond ι .pure) :
    (S.toHandler op).apply Q =
      spred(⌜S.pre op ∧ ∀ out, S.post op out → (Q.1 out).down⌝) :=
  rfl

end OperationSpec

namespace LHandler

/-- Sum of handlers; the counterpart of the paper's `H₁ ⊕ H₂`. -/
def sum (H₁ : LHandler F ps) (H₂ : LHandler G ps) :
    LHandler (fun α => F α ⊕ G α) ps :=
  fun op => Sum.elim H₁ H₂ op

@[simp] theorem sum_inl (H₁ : LHandler F ps) (H₂ : LHandler G ps)
    {ι : Type u} (x : F ι) :
    LHandler.sum H₁ H₂ (Sum.inl x : F ι ⊕ G ι) = H₁ x := rfl

@[simp] theorem sum_inr (H₁ : LHandler F ps) (H₂ : LHandler G ps)
    {ι : Type u} (y : G ι) :
    LHandler.sum H₁ H₂ (Sum.inr y : F ι ⊕ G ι) = H₂ y := rfl

/-- Derive a logical handler from an effect handler into any `[WP m ps]` monad, by composing
with `m`'s WP. -/
def ofInterp {m : Type u → Type w} [WP m ps]
    (interp : ∀ ι : Type u, F ι → m ι) : LHandler F ps :=
  fun {ι} op => wp (interp ι op)

@[simp] theorem ofInterp_apply {m : Type u → Type w} [WP m ps]
    (interp : ∀ ι : Type u, F ι → m ι) {ι : Type u} (op : F ι) :
    LHandler.ofInterp interp op = wp (interp ι op) := rfl

end LHandler

/-- Weakest-precondition interpretation of a `FreeM F α` program against a logical handler `H`.
Defined as `FreeM.liftM` instantiated at `PredTrans ps`, the unique monad morphism
`FreeM F → PredTrans ps` extending `H` per the universal property of `FreeM`. -/
def wpH (H : LHandler F ps) (x : FreeM F α) : PredTrans ps α :=
  x.liftM H

@[simp] theorem wpH_pure (H : LHandler F ps) (a : α) :
    wpH H (pure a : FreeM F α) = Pure.pure a := rfl

theorem wpH_liftBind (H : LHandler F ps) {ι : Type u}
    (op : F ι) (k : ι → FreeM F α) :
    wpH H ((lift op : FreeM F ι) >>= k) = H op >>= fun x => wpH H (k x) := rfl

theorem wpH_lift (H : LHandler F ps) {ι : Type u} (op : F ι) :
    wpH H (lift op : FreeM F ι) = H op :=
  liftM_lift _ op

@[simp] theorem wpH_bind (H : LHandler F ps) (x : FreeM F α) (f : α → FreeM F β) :
    wpH H (x >>= f) = wpH H x >>= fun a => wpH H (f a) :=
  liftM_bind H x f

/-- Adequacy theorem: WP via `FreeM` against an `ofInterp`-derived handler agrees with
`Std.Do`'s WP of the `liftM` interpretation. Equivalently, two monad morphisms
`FreeM F → PredTrans ps` extending the same handler are equal. -/
theorem wpH_ofInterp_eq_wp_liftM
    {m : Type u → Type w} [Monad m] [WPMonad m ps]
    (interp : ∀ ι : Type u, F ι → m ι) (x : FreeM F α) :
    wpH (LHandler.ofInterp interp) x = wp (x.liftM (fun {_} => interp _)) := by
  induction x with
  | pure a => simp [wpH, WPMonad.wp_pure]
  | lift_bind op k ih =>
    simp only [wpH] at ih ⊢
    simp [WPMonad.wp_bind, ih]

/-- Records a default logical handler for `F` at shape `ps`, enabling the global
`WP (FreeM F) ps` instance and any `Triple`/`mvcgen` reasoning over `FreeM F`. -/
class HasHandler (F : Type u → Type v) (ps : outParam (PostShape.{u})) where
  /-- The default logical handler for `F`. -/
  handler {ι : Type u} : F ι → PredTrans ps ι

instance instWPFreeM [HasHandler F ps] : WP (FreeM F) ps where
  wp := wpH HasHandler.handler

instance instWPMonadFreeM [HasHandler F ps] : WPMonad (FreeM F) ps where
  wp_pure _ := rfl
  wp_bind x f := wpH_bind _ x f

/-- The generic Hoare rule for a primitive `FreeM` operation. Its precondition is exactly the
predicate transformer assigned by the selected logical handler. Its low `mvcgen` priority lets
effect-specific rules expose more useful preconditions when available. -/
@[spec low]
theorem Spec.lift_FreeM [HasHandler F ps] (op : F α) {Q : PostCond α ps} :
    Triple (lift op : FreeM F α) ((HasHandler.handler op).apply Q) Q :=
  Triple.iff.mpr SPred.entails.rfl

end FreeM

end Cslib
