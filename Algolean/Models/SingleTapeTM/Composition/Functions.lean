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

/-- A computation's time bound also bounds additional allocated cells, retaining initial space. -/
theorem Computes.space {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time : List Symbol → ℕ} (h : Computes p f time) (input : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes p s cost final ∧ cost.steps ≤ time input ∧
      cost.cellsAllocated ≤ time input ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + time input := by
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

/-- The occupied tape extent grows by at most one per head move.
This auxiliary output-size estimate does not redefine allocated tape space. -/
theorem step_tapeExtent_le (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (s : TMState tm) :
    (step q rest s).machine.config.BiTape.spaceUsed ≤
      s.config.BiTape.spaceUsed + (step q rest s).cost.steps := by
  cases q with
  | move direction =>
    cases direction with
    | Left => simpa [step, BiTape.move] using BiTape.spaceUsed_move s.config.BiTape .left
    | Right => simpa [step, BiTape.move] using BiTape.spaceUsed_move s.config.BiTape .right
    | Stop => simp [step]
  | _ => simp [step]

/-- Bound the occupied extent at the end of any successful execution. -/
theorem runCode_tapeExtent_le (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm)
    (result : AddWriter TMCost Unit) (final : ExecutionState tm)
    (h : runCode fuel code s = some (result, final)) :
    final.machine.config.BiTape.spaceUsed ≤ s.config.BiTape.spaceUsed + result.tell.steps := by
  induction fuel generalizing code s result final with
  | zero => cases code <;> grind [runCode]
  | succ fuel ih =>
    cases code with
    | nil => grind
    | cons q rest =>
      cases hr : runCode fuel (step q rest s).code (step q rest s).machine <;> simp_all [runCode]
      have := step_tapeExtent_le q rest s
      grind

/-- A uniform time bound also bounds the length of the intermediate output word. -/
theorem Computes.output_length_le {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time : List Symbol → ℕ} (h : Computes p f time) (input : List Symbol) :
    (f input).length ≤ 1 + input.length + time input := by
  obtain ⟨moves, ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, hc⟩, ht⟩ :=
    h input (TMState.init tm input) rfl
  rw [execute_eq_runCode] at hfuel
  have := runCode_tapeExtent_le fuel _ _ _ _ hfuel
  simp only [hcfg, TMState.init_config, SingleTapeTM.initCfg, BiTape.spaceUsed_mk₁] at this
  lia

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

namespace Algolean.Algorithms.Computer

open Cslib.Turing TMQuery Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {f : List Symbol → List Symbol} {time : List Symbol → ℕ}

/-- Package an existing uniform computation proof as a verified machine. -/
@[simps program]
def ofComputes {p : Prog (TMQuery tm) Unit} (h : Computes p f time) : Computer tm f time where
  program := p
  correct input s hs := by
    obtain ⟨moves, ⟨cost, final, hc, ht, hp, hm⟩, hbound⟩ := h input s hs
    exact ⟨cost, final, hc, ht, hp, by lia⟩

/-- Recover a machine's uniform computation contract without exposing input to its program. -/
theorem computes (machine : Computer tm f time) : Computes machine.program f time := by
  intro input s hs
  obtain ⟨cost, final, hc, ht, hp, hb⟩ := machine.correct input s hs
  exact ⟨cost.steps, ⟨cost, final, hc, ht, hp, rfl⟩, hb⟩

/-- Convert a polynomially bounded verified machine to the complexity-theory witness. -/
def polyTimeComputable {poly : Polynomial ℕ}
    (machine : Computer tm f (fun input => poly.eval input.length)) : PolyTimeComputable f :=
  machine.computes.polyTimeComputable

end Algolean.Algorithms.Computer

namespace Algolean.Algorithms.EncodedComputer

open Cslib.Turing TMQuery Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- Enlarge a verified bound without changing the program, encodings, or head-position contract. -/
@[simps program]
def mono {α β : Type} {ea : α → List Symbol} {eb : β → List Symbol} {f : α → β}
    {a b : α → ℕ} {position : α → ℤ → ℤ}
    (machine : EncodedComputer tm ea eb f a position) (bound : ∀ input, a input ≤ b input) :
    EncodedComputer tm ea eb f b position where
  program := machine.program
  correct input s hs := by
    obtain ⟨cost, final, hc, ht, hp, hb⟩ := machine.correct input s hs
    exact ⟨cost, final, hc, ht, hp, hb.trans (bound input)⟩

/-- An encoded output interface gives a uniform word function even when the output is relocated. -/
def timeComputable {β : Type} {outputEncoding : β → List Symbol} {f : List Symbol → β}
    {timeBound : ℕ → ℕ} {position : List Symbol → ℤ → ℤ}
    (machine : EncodedComputer tm id outputEncoding f (fun input => timeBound input.length)
      position) : TimeComputable (outputEncoding ∘ f) where
  tm := tm
  program := machine.program
  timeBound := timeBound
  outputsFunInTime input := by
    obtain ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, ht⟩ :=
      machine.correct input (TMState.init tm input) rfl
    exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, hfuel, by simp [hcfg], ht⟩

/-- A polynomially bounded encoded interface supplies the complexity-theory witness. -/
def polyTimeComputable {β : Type} {outputEncoding : β → List Symbol} {f : List Symbol → β}
    {poly : Polynomial ℕ} {position : List Symbol → ℤ → ℤ}
    (machine : EncodedComputer tm id outputEncoding f (fun input => poly.eval input.length)
      position) : PolyTimeComputable (outputEncoding ∘ f) where
  toTimeComputable := machine.timeComputable
  poly := poly
  bounds _ := le_rfl

end Algolean.Algorithms.EncodedComputer
