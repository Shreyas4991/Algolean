/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.AddWriter.Basic

/-!
# Additive writer monad transformer

`AddWriterT Cost m α` is an `m` computation returning an `α` together with an accumulated cost.
Keeping `m` outside the pair preserves the correlation between effect branches, results, and costs.
-/

@[expose] public section

namespace Algolean

def AddWriterT (Cost : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (AddWriter Cost α)

namespace AddWriterT

variable {Cost : Type u} {m : Type u → Type v} {α β : Type u}

@[inline] def mk (x : m (AddWriter Cost α)) : AddWriterT Cost m α := x
@[inline] def run (x : AddWriterT Cost m α) : m (AddWriter Cost α) := x

@[simp] theorem run_mk (x : m (AddWriter Cost α)) : (mk x).run = x := rfl
@[simp] theorem mk_run (x : AddWriterT Cost m α) : mk x.run = x := rfl

def value [Functor m] (x : AddWriterT Cost m α) : m α :=
  (·.ret) <$> x.run

def cost [Functor m] (x : AddWriterT Cost m α) : m Cost :=
  (·.tell) <$> x.run

def lift [Functor m] [Zero Cost] (x : m α) : AddWriterT Cost m α :=
  mk ((⟨·, 0⟩) <$> x)

instance [Functor m] : Functor (AddWriterT Cost m) where
  map f x := mk ((fun a => ⟨f a.ret, a.tell⟩) <$> x.run)

instance [Monad m] [Zero Cost] : Pure (AddWriterT Cost m) where
  pure a := mk (pure (pure a))

instance [Monad m] [Add Cost] : Bind (AddWriterT Cost m) where
  bind x f := mk do
    let a ← x.run
    let b ← (f a.ret).run
    pure ⟨b.ret, a.tell + b.tell⟩

instance [Monad m] [AddZero Cost] : Monad (AddWriterT Cost m) where
  pure := Pure.pure
  bind := Bind.bind
  map := Functor.map

@[simp] theorem run_map [Functor m] (f : α → β) (x : AddWriterT Cost m α) :
    (f <$> x).run = ((fun a => (⟨f a.ret, a.tell⟩ : AddWriter Cost β)) <$> x.run) := rfl

@[simp] theorem run_pure [Monad m] [Zero Cost] (a : α) :
    (pure a : AddWriterT Cost m α).run = pure (pure a) := rfl

@[simp] theorem run_bind [Monad m] [Add Cost]
    (x : AddWriterT Cost m α) (f : α → AddWriterT Cost m β) :
    (x >>= f).run = (do
      let a ← x.run
      let b ← (f a.ret).run
      pure ⟨b.ret, a.tell + b.tell⟩) := rfl

@[simp] theorem value_pure [Monad m] [LawfulMonad m] [Zero Cost] (a : α) :
    (pure a : AddWriterT Cost m α).value = (pure a : m α) := by
  simp [value]

@[simp] theorem cost_pure [Monad m] [LawfulMonad m] [Zero Cost] (a : α) :
    (pure a : AddWriterT Cost m α).cost = (pure 0 : m Cost) := by
  simp [cost]

@[simp] theorem value_map [Functor m] [LawfulFunctor m]
    (f : α → β) (x : AddWriterT Cost m α) :
    (f <$> x).value = f <$> x.value := by
  simp [value]

@[simp] theorem cost_map [Functor m] [LawfulFunctor m]
    (f : α → β) (x : AddWriterT Cost m α) :
    (f <$> x).cost = x.cost := by
  simp [cost]

theorem value_bind [Monad m] [LawfulMonad m] [Add Cost]
    (x : AddWriterT Cost m α) (f : α → AddWriterT Cost m β) :
    (x >>= f).value = (do
      let a ← x.run
      (f a.ret).value) := by
  simp [value, run_bind]

theorem cost_bind [Monad m] [LawfulMonad m] [Add Cost]
    (x : AddWriterT Cost m α) (f : α → AddWriterT Cost m β) :
    (x >>= f).cost = (do
      let a ← x.run
      let b ← (f a.ret).run
      pure (a.tell + b.tell)) := by
  simp only [cost, run_bind, map_bind, map_pure]

theorem run_injective {x y : AddWriterT Cost m α} (h : x.run = y.run) : x = y := h

instance [Monad m] [LawfulMonad m] [AddMonoid Cost] : LawfulMonad (AddWriterT Cost m) :=
  LawfulMonad.mk'
    (id_map := fun x => run_injective (by simp))
    (pure_bind := fun a f => run_injective (by simp))
    (bind_assoc := fun x f g => run_injective (by simp [bind_assoc, add_assoc]))
    (bind_pure_comp := fun f x => run_injective (by simp [add_zero]))

end AddWriterT
end Algolean
