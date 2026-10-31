/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component

/-!
# Sequential composition of single-tape query procedures
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Compose two procedures without resetting any machine state or space history. -/
theorem Completes.seq {p q : Prog (TMQuery tm) Unit} {s t u : TMState tm} {a b : TMCost}
    (hp : Completes p s a t) (hq : Completes q t b u) : Completes (do p; q) s (a + b) u := by
  obtain ⟨fuel, hp⟩ := hp
  obtain ⟨extra, hq⟩ := hq
  refine ⟨fuel + extra, ?_⟩
  simp [execute_add_fuel fuel extra p s _ _ hp, hq]


/-- Compose contracts while retaining the intermediate execution state. -/
theorem Runs.seq {p q : Prog (TMQuery tm) Unit} {s : TMState tm}
    {first second : BiTape Symbol} {pos₁ pos₂ : ℤ} {time₁ time₂ : ℕ}
    (hp : Runs p s first pos₁ time₁)
    (hq : ∀ t : TMState tm, t.config = {s.config with BiTape := first} →
      t.headPos = pos₁ → Runs q t second pos₂ time₂) :
    Runs (do p; q) s second pos₂ (time₁ + time₂) := by
  obtain ⟨a, t, hp, ht, hpos, ha⟩ := hp
  obtain ⟨b, u, hq, hu, hup, hb⟩ := hq t ht hpos
  exact ⟨a + b, u, hp.seq hq, by simpa [ht] using hu, hup, by simp [ha, hb]⟩


end TMQuery

end Algolean.Algorithms

namespace Algolean.Algorithms.Component

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Compose general tape contracts, proving that the first postcondition enables the second.
The index map and compatibility proof are specification data; the second program stays fixed. -/
@[simps program]
def andThen {ι κ : Type} {pre : ι → TMState tm → Prop}
    {post : ι → TMState tm → TMCost → TMState tm → Prop}
    {nextPre : κ → TMState tm → Prop}
    {nextPost : κ → TMState tm → TMCost → TMState tm → Prop}
    (first : Component tm pre post) (second : Component tm nextPre nextPost) (index : ι → κ)
    (compatible : ∀ i s cost t, pre i s → post i s cost t → nextPre (index i) t) :
    Component tm pre (fun i s cost final => ∃ a middle b,
      cost = a + b ∧ post i s a middle ∧ nextPost (index i) middle b final) where
  program := do first.program; second.program
  correct i s hs := by
    obtain ⟨a, t, ha, hp⟩ := first.correct i s hs
    obtain ⟨b, u, hb, hq⟩ := second.correct (index i) t (compatible i s a t hs hp)
    exact ⟨a + b, u, ha.seq hb, a, t, b, rfl, hp, hq⟩

end Algolean.Algorithms.Component

namespace Algolean.Algorithms.EncodedComputer

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Compose compatible encoded interfaces without performing any encoding operation for free. -/
@[simps program]
def seq {α β γ : Type} {ea : α → List Symbol} {eb : β → List Symbol} {ec : γ → List Symbol}
    {f : α → β} {g : β → γ} {a : α → ℕ} {b : β → ℕ}
    {pa : α → ℤ → ℤ} {pb : β → ℤ → ℤ}
    (first : EncodedComputer tm ea eb f a pa) (second : EncodedComputer tm eb ec g b pb) :
    EncodedComputer tm ea ec (g ∘ f) (fun input => a input + b (f input))
      (fun input origin => pb (f input) (pa input origin)) where
  program := do first.program; second.program
  correct input s hs := by
    obtain ⟨ca, t, hp, ht, hpos, ha⟩ := first.correct input s hs
    obtain ⟨cb, u, hq, hu, hup, hb⟩ := second.correct (f input) t (by simp [ht])
    exact ⟨ca + cb, u, hp.seq hq, by simpa [ht] using hu, by simpa [hpos] using hup,
      by simpa using Nat.add_le_add ha hb⟩

end Algolean.Algorithms.EncodedComputer

namespace Algolean.Algorithms.Computer

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {f g : List Symbol → List Symbol} {a b : List Symbol → ℕ}

/-- The generic verified identity component, with zero head moves and unchanged history. -/
@[simps program]
def identity : Computer tm id (fun _ => 0) where
  program := pure ()
  correct _ s hs := by
    simp only [id_eq] at hs
    exact ⟨0, s, completes_pure s, by simp [← hs], rfl, le_rfl⟩

/-- Compose verified machines, adding phase bounds on the actual intermediate word. -/
@[simps program] def seq (first : Computer tm f a) (second : Computer tm g b) :
    Computer tm (g ∘ f) (fun input => a input + b (f input)) where
  program := do first.program; second.program
  correct input s hs := by
    obtain ⟨ca, t, hp, ht, hpos, ha⟩ := first.correct input s hs
    obtain ⟨cb, u, hq, hu, hup, hb⟩ := second.correct (f input) t (by simp [ht])
    exact ⟨ca + cb, u, hp.seq hq, by simpa [ht] using hu, by simpa [hpos] using hup,
      by simpa using Nat.add_le_add ha hb⟩

/-- Sequential composition of verified machines, read from left to right. -/
scoped infixr:55 " ≫ₜ " => Computer.seq

/-- Identity before a component preserves its executable program. -/
theorem identity_seq (machine : Computer tm f a) :
    (identity.seq machine).program = machine.program := by simp

/-- Identity after a component preserves its executable program. -/
theorem seq_identity (machine : Computer tm f a) :
    (machine.seq identity).program = machine.program := by simp

/-- Reassociating verified composition preserves the executable program. -/
theorem seq_assoc {h : List Symbol → List Symbol} {c : List Symbol → ℕ}
    (first : Computer tm f a) (second : Computer tm g b) (third : Computer tm h c) :
    ((first.seq second).seq third).program = (first.seq (second.seq third)).program := by
  simp [bind_assoc]

end Algolean.Algorithms.Computer
