/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Cslib.Foundations.Control.Monad.Free.Effects
public import Algolean.FreeWP.WP

/-!
# Logical handlers for the standard `FreeM` effects

Logical handlers and `HasHandler` instances for the state and reader effects from
`Cslib.Foundations.Control.Monad.Free.Effects`, each induced by the canonical interpreter
into the corresponding Lean monad (`StateM`, `ReaderM`) via `Std.WP`'s `WP` instances.
Adequacy theorems relate the `FreeM`-level WP to the WP of the interpretation, and `@[spec]`
Hoare triples for the primitive operations enable `vcgen` reasoning.
-/

@[expose] public section

set_option experimental.vcgen true

namespace Cslib

namespace FreeM

open Lean.Order Std.WP

universe u

/-! ### State -/

/-- Logical handler for the state effect, induced by `Std.WP`'s `WP (StateM σ)`. -/
def StateF.handler {σ : Type u} : LHandler (StateF σ) (σ → Prop) EStack⟨⟩ :=
  LHandler.ofInterp (m := StateM σ) (fun _ op => FreeState.stateInterp op)

instance StateF.instHasHandler {σ : Type u} :
    HasHandler (StateF σ) (σ → Prop) EStack⟨⟩ where
  handler := StateF.handler

/-- WP of a `FreeState` program matches WP of its `StateM` interpretation. -/
theorem StateF.wp_FreeState_eq_wp_toStateM {σ α : Type u} (comp : FreeState σ α) :
    wp comp = wp (FreeState.toStateM comp) :=
by
  funext Q E s
  induction comp using FreeM.induction generalizing s with
  | pure a => rfl
  | lift_bind op k ih => cases op <;> exact ih _ _

/-- Hoare spec for `get` on `FreeState`. -/
@[spec]
theorem Spec.get_FreeState {σ : Type u} {Q : σ → σ → Prop} :
    Triple (MonadStateOf.get : FreeState σ σ) (fun s => Q s s) Q () :=
  ⟨fun _ h => h⟩

/-- Hoare spec for `set` on `FreeState`. -/
@[spec]
theorem Spec.set_FreeState {σ : Type u} (s : σ) {Q : PUnit → σ → Prop} :
    Triple (MonadStateOf.set s : FreeState σ PUnit) (fun _ => Q ⟨⟩ s) Q () :=
  ⟨fun _ h => h⟩

/-! ### Reader -/

/-- Logical handler for the reader effect, induced by `Std.WP`'s `WP (ReaderM σ)`. -/
def ReaderF.handler {σ : Type u} : LHandler (ReaderF σ) (σ → Prop) EStack⟨⟩ :=
  LHandler.ofInterp (m := ReaderM σ) (fun _ op => FreeReader.readInterp op)

instance ReaderF.instHasHandler {σ : Type u} :
    HasHandler (ReaderF σ) (σ → Prop) EStack⟨⟩ where
  handler := ReaderF.handler

/-- WP of a `FreeReader` program matches WP of its `ReaderM` interpretation. -/
theorem ReaderF.wp_FreeReader_eq_wp_toReaderM {σ α : Type u} (comp : FreeReader σ α) :
    wp comp = wp (FreeReader.toReaderM comp) :=
by
  funext Q E s
  induction comp using FreeM.induction with
  | pure a => rfl
  | lift_bind op k ih => cases op; exact ih s

/-- Hoare spec for `read` on `FreeReader`. -/
@[spec]
theorem Spec.read_FreeReader {ρ : Type u} {Q : ρ → ρ → Prop} :
    Triple (MonadReaderOf.read : FreeReader ρ ρ) (fun r => Q r r) Q () :=
  ⟨fun _ h => h⟩

end FreeM

end Cslib
