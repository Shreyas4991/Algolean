/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Sequential
public import Algolean.Complexity.PolytimeBasicClasses

/-!
# Functional composition of reusable single-tape procedures

`Computes` requires the procedure to accept any existing control state and space history,
preserve its control state, and return the head to the first output cell. These contracts
compose on the actual intermediate machine state, without restarting or resetting the model.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A fixed procedure computes a function with an input-dependent logical time bound.
The input and bound are specification data, never arguments passed to the program. -/
def Computes (program : Prog (TMQuery tm) Unit) (f : List Symbol → List Symbol)
    (time : List Symbol → ℕ) : Prop :=
  ∀ input (s : TMState tm), s.config.BiTape = BiTape.mk₁ input →
    ∃ moves, Runs program s (BiTape.mk₁ (f input)) s.headPos moves ∧ moves ≤ time input

/-- Pointwise enlargement of a logical time bound preserves a computation contract. -/
theorem Computes.mono {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time time' : List Symbol → ℕ} (h : Computes p f time) (hle : ∀ x, time x ≤ time' x) :
    Computes p f time' := by
  intro input s hs
  obtain ⟨moves, hr, ht⟩ := h input s hs
  exact ⟨moves, hr, ht.trans (hle input)⟩

/-- A computation's time bound also bounds additional visited cells, retaining initial space. -/
theorem Computes.space {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time : List Symbol → ℕ} (h : Computes p f time) (input : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes p s cost final ∧ cost.steps ≤ time input ∧
      cost.cellsVisited ≤ time input ∧
      final.cellsVisited.card ≤ s.cellsVisited.card + time input := by
  obtain ⟨moves, hr, ht⟩ := h input s hs
  obtain ⟨cost, final, hc, hcsteps, hcspace, htotal⟩ := hr.space
  exact ⟨cost, final, hc, by lia, by lia, by lia⟩

/-- Functional composition has time `time₁ input + time₂ (f input)` and shares space history. -/
theorem Computes.comp {p q : Prog (TMQuery tm) Unit} {f g : List Symbol → List Symbol}
    {time₁ time₂ : List Symbol → ℕ} (hp : Computes p f time₁) (hq : Computes q g time₂) :
    Computes (do p; q) (g ∘ f) (fun input => time₁ input + time₂ (f input)) := by
  intro input s hs
  obtain ⟨a, ⟨ca, t, hp, ht, hpos, hca⟩, ha⟩ := hp input s hs
  obtain ⟨b, ⟨cb, u, hq, hu, hup, hcb⟩, hb⟩ := hq (f input) t (by simp [ht])
  refine ⟨a + b, ⟨ca + cb, u, hp.seq hq, ?_, ?_, ?_⟩, Nat.add_le_add ha hb⟩
  · simpa [ht] using hu
  · simpa [hpos] using hup
  · simp [hca, hcb]

/-- A reusable procedure contract gives a uniform time-computability witness. -/
def Computes.timeComputable {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {timeBound : ℕ → ℕ} (h : Computes p f (fun input => timeBound input.length)) :
    TimeComputable f where
  tm := tm
  program := p
  timeBound := timeBound
  outputsFunInTime input := by
    obtain ⟨moves, ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, hc⟩, ht⟩ :=
      h input (TMState.init tm input) rfl
    exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, hfuel, by simp [hcfg], by lia⟩

/-- A polynomially bounded reusable procedure computes a polynomial-time function. -/
def Computes.polyTimeComputable {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {poly : Polynomial ℕ} (h : Computes p f (fun input => poly.eval input.length)) :
    PolyTimeComputable f where
  toTimeComputable := h.timeComputable (timeBound := poly.eval)
  poly := poly
  bounds _ := le_rfl

/-- Polynomial-time composition when the intermediate output has a polynomial length bound. -/
theorem Computes.comp_polynomial {p q : Prog (TMQuery tm) Unit}
    {f g : List Symbol → List Symbol} {a b size : Polynomial ℕ}
    (hp : Computes p f (fun input => a.eval input.length))
    (hq : Computes q g (fun input => b.eval input.length))
    (hsize : ∀ input, (f input).length ≤ size.eval input.length) :
    Computes (do p; q) (g ∘ f) (fun input => (a + b.comp size).eval input.length) := by
  apply (hp.comp hq).mono
  intro input
  simpa using Nat.add_le_add_left (b.eval_mono (hsize input)) (a.eval input.length)

end Algolean.Algorithms.TMQuery
