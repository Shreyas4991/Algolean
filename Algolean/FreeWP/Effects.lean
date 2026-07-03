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
into the corresponding Lean monad (`StateM`, `ReaderM`) via `Std.Do`'s `WP` instances.
Adequacy theorems relate the `FreeM`-level WP to the WP of the interpretation, and `@[spec]`
Hoare triples for the primitive operations enable `mvcgen` reasoning.
-/

@[expose] public section

set_option mvcgen.warning false

namespace Cslib

namespace FreeM

open Std.Do

universe u

/-! ### State -/

/-- Logical handler for the state effect, induced by `Std.Do`'s `WP (StateM σ)`. -/
def StateF.handler {σ : Type u} : LHandler (StateF σ) (.arg σ .pure) :=
  LHandler.ofInterp (m := StateM σ) (fun _ op => FreeState.stateInterp op)

instance StateF.instHasHandler {σ : Type u} :
    HasHandler (StateF σ) (.arg σ .pure) where
  handler := StateF.handler

/-- WP of a `FreeState` program matches WP of its `StateM` interpretation. -/
theorem StateF.wp_FreeState_eq_wp_toStateM {σ α : Type u} (comp : FreeState σ α) :
    wp comp = wp (FreeState.toStateM comp) :=
  wpH_ofInterp_eq_wp_liftM (m := StateM σ)
    (fun _ op => FreeState.stateInterp op) comp

/-- Hoare spec for `get` on `FreeState`. -/
@[spec]
theorem Spec.get_FreeState {σ : Type u} {Q : PostCond σ (.arg σ .pure)} :
    Triple (MonadStateOf.get : FreeState σ σ) (spred(fun s => Q.1 s s)) Q := by
  mvcgen

/-- Hoare spec for `set` on `FreeState`. -/
@[spec]
theorem Spec.set_FreeState {σ : Type u} (s : σ) {Q : PostCond PUnit (.arg σ .pure)} :
    Triple (MonadStateOf.set s : FreeState σ PUnit) (spred(fun _ => Q.1 ⟨⟩ s)) Q := by
  mvcgen

/-! ### Reader -/

/-- Logical handler for the reader effect, induced by `Std.Do`'s `WP (ReaderM σ)`. -/
def ReaderF.handler {σ : Type u} : LHandler (ReaderF σ) (.arg σ .pure) :=
  LHandler.ofInterp (m := ReaderM σ) (fun _ op => FreeReader.readInterp op)

instance ReaderF.instHasHandler {σ : Type u} :
    HasHandler (ReaderF σ) (.arg σ .pure) where
  handler := ReaderF.handler

/-- WP of a `FreeReader` program matches WP of its `ReaderM` interpretation. -/
theorem ReaderF.wp_FreeReader_eq_wp_toReaderM {σ α : Type u} (comp : FreeReader σ α) :
    wp comp = wp (FreeReader.toReaderM comp) :=
  wpH_ofInterp_eq_wp_liftM (m := ReaderM σ)
    (fun _ op => FreeReader.readInterp op) comp

/-- Hoare spec for `read` on `FreeReader`. -/
@[spec]
theorem Spec.read_FreeReader {ρ : Type u} {Q : PostCond ρ (.arg ρ .pure)} :
    Triple (MonadReaderOf.read : FreeReader ρ ρ) (spred(fun r => Q.1 r r)) Q := by
  mvcgen

end FreeM

end Cslib
