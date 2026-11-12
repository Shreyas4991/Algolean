/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Description
public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Algolean.Models.SingleTapeTM.Tape

/-!
# Bounded certificate verification

* `BoundedVerification` records a verifier, an input, an exact certificate length, and a time bound.
* `accepted` contains the records for which some certificate makes the verifier accept in time.
* `AcceptsWithin` uses CSLib's output convention. The verifier halts with the head on its only
  nonblank cell, which contains the chosen answer symbol.

The input and certificate use the same alphabet. One separate tape symbol marks their boundary.
The bound counts every transition, including transitions that leave the head in place.
-/

@[expose] public section

namespace Cslib.Turing.SingleTapeTM

/-- These data describe a verifier's bounded computation on an input and an unknown certificate. -/
structure BoundedVerification (Γ : Type) where
  /-- This finite description specifies the deterministic verifier. -/
  verifier : Description (Algolean.Algorithms.Alphabet.Extended Γ 1)
  /-- This is the input whose certificate the verifier checks. -/
  input : List Γ
  /-- The certificate must contain exactly this many symbols. -/
  certificateLength : ℕ
  /-- The verifier must accept within this many transitions. -/
  time : ℕ

namespace BoundedVerification

open Cslib.Turing Algolean.Algorithms.Alphabet Relation

/-- The tape alphabet adds one separator between the input and certificate. -/
abbrev TapeSymbol (Γ : Type) := Extended Γ 1

variable {Γ : Type} [Fintype Γ]

/-- The halted tape contains only the chosen accepting symbol, with the head on that symbol. -/
def accepting (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :
    Set verifier.machine.Cfg :=
  {configuration | configuration.state = none ∧
    configuration.BiTape = BiTape.mk₁ [.inl yes]}

/-- The machine reaches an accepting configuration after at most the specified transitions. -/
def AcceptsWithin (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) (time : ℕ) : Prop :=
  verifier.machine.OutputsWithinTime word [.inl yes] time

/-- The accepting configuration is exactly CSLib's halting configuration for `[yes]`. -/
theorem mem_accepting_iff (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (cfg : verifier.machine.Cfg) :
    cfg ∈ accepting yes verifier ↔ cfg = verifier.machine.haltCfg [.inl yes] := by
  cases cfg
  simp [accepting, SingleTapeTM.haltCfg]

/-- The standard output relation is equivalent to reaching an accepting configuration in time. -/
theorem acceptsWithin_iff_exists (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) (time : ℕ) :
    AcceptsWithin yes verifier word time ↔ ∃ final ∈ accepting yes verifier,
      RelatesWithinSteps verifier.machine.TransitionRelation
        (verifier.machine.initCfg word) final time := by
  simp [mem_accepting_iff, AcceptsWithin, SingleTapeTM.OutputsWithinTime]

/-- Some certificate of the specified length makes the verifier accept within the time bound. -/
def accepted (yes : Γ) : Set (BoundedVerification Γ) :=
  {problem | ∃ certificate : List Γ, certificate.length = problem.certificateLength ∧
    AcceptsWithin yes problem.verifier ((wordPair Γ).encode (problem.input, certificate))
      problem.time}

/-- An initial configuration cannot already be accepting because its state has not halted. -/
@[simp] theorem not_acceptsWithin_zero (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) : ¬AcceptsWithin yes verifier word 0 := by
  simp [AcceptsWithin, SingleTapeTM.OutputsWithinTime, SingleTapeTM.initCfg, SingleTapeTM.haltCfg]

/-- Acceptance within one transition requires that transition to halt with the clean answer. -/
theorem acceptsWithin_one_iff (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) : AcceptsWithin yes verifier word 1 ↔
      ∃ final ∈ accepting yes verifier, verifier.machine.step (verifier.machine.initCfg word) =
        some final := by
  rw [acceptsWithin_iff_exists]
  constructor
  · rintro ⟨final, hfinal, steps, hle, hrun⟩
    cases steps with
    | zero =>
      have heq := hrun.zero
      subst final
      simp [accepting, SingleTapeTM.initCfg] at hfinal
    | succ steps =>
      have hzero : steps = 0 := by lia
      subst steps
      exact ⟨final, hfinal, by
        simpa [RelatesInSteps.succ_iff, SingleTapeTM.TransitionRelation] using hrun⟩
  · rintro ⟨final, hfinal, hstep⟩
    exact ⟨final, hfinal, RelatesWithinSteps.single hstep⟩

/-- Allowing more transitions preserves acceptance. -/
theorem AcceptsWithin.mono {yes : Γ} {verifier : SingleTapeTM.Description (TapeSymbol Γ)}
    {word : List (TapeSymbol Γ)} {time time' : ℕ} (h : AcceptsWithin yes verifier word time)
    (hle : time ≤ time') : AcceptsWithin yes verifier word time' := by
  exact RelatesWithinSteps.mono hle h

/--
If the verifier produces a specified output within the bound, it accepts exactly when that
output is exactly the one-symbol acceptance word. Determinism prevents a different halting tape
from accepting.
-/
theorem acceptsWithin_iff_of_outputsWithinTime (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    {word output : List (TapeSymbol Γ)} {time : ℕ}
    (houtput : verifier.machine.OutputsWithinTime word output time) :
    AcceptsWithin yes verifier word time ↔ output = [.inl yes] := by
  rw [acceptsWithin_iff_exists]
  have hterminal {a b : verifier.machine.Cfg} (ha : a.state = none)
      (h : ReflTransGen verifier.machine.TransitionRelation a b) : a = b := by
    rcases h.cases_head with heq | ⟨next, hstep, _⟩
    · exact heq
    · cases a
      simp_all [SingleTapeTM.TransitionRelation]
  constructor
  · rintro ⟨final, hfinal, hrun⟩
    have hdet : Relator.RightUnique verifier.machine.TransitionRelation := by
      intro a b c hb hc
      exact Option.some.inj (hb.symm.trans hc)
    have hsame : final = verifier.machine.haltCfg output := by
      rcases ReflTransGen.total_of_right_unique hdet hrun.choose_spec.2.reflTransGen
          houtput.choose_spec.2.reflTransGen with h | h
      · exact hterminal hfinal.1 h
      · exact (hterminal rfl h).symm
    simpa only [hsame, SingleTapeTM.haltCfg, BiTape.mk₁_injective.eq_iff] using hfinal.2
  · intro h
    subst output
    exact ⟨verifier.machine.haltCfg [.inl yes], ⟨rfl, rfl⟩, houtput⟩

/-- Allowing more time preserves acceptance without changing the required certificate length. -/
theorem mem_accepted_mono {yes : Γ} {problem : BoundedVerification Γ}
    (h : problem ∈ accepted yes)
    {time : ℕ} (hle : problem.time ≤ time) : {problem with time} ∈ accepted yes := by
  obtain ⟨certificate, hlength, hrun⟩ := h
  exact ⟨certificate, hlength, hrun.mono hle⟩

/-- A certificate of length zero must be empty. -/
@[simp] theorem mem_accepted_zero_length (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (input : List Γ) (time : ℕ) :
    (⟨verifier, input, 0, time⟩ : BoundedVerification Γ) ∈ accepted yes ↔
      AcceptsWithin yes verifier ((wordPair Γ).encode (input, [])) time := by
  simp [accepted]

/-- The initial state is not a halting state, so no instance accepts in zero transitions. -/
@[simp] theorem not_mem_accepted_zero (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (input : List Γ) (certificateLength : ℕ) :
    (⟨verifier, input, certificateLength, 0⟩ : BoundedVerification Γ) ∉ accepted yes := by
  simp [accepted]


end BoundedVerification
end Cslib.Turing.SingleTapeTM
