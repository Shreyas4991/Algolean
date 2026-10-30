/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic

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
