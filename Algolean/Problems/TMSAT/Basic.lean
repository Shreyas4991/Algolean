/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Algolean.Models.SingleTapeTM.Description
public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Algolean.Models.SingleTapeTM.Tape

/-!
# Turing machine satisfiability

* An `Instance` contains a deterministic machine, an input, a certificate length, and a time bound.
* `satisfiable` contains the instances with a certificate accepted within that bound.
* The alphabet `Γ` is fixed for the whole problem. Inputs and certificates are words over `Γ`.
* Certificates have exactly the specified length, measured in symbols of `Γ`.

The machine receives the input, then one separate symbol, then the certificate. It accepts
by halting with exactly the one-symbol word `[yes]` on an otherwise blank tape, with the head
on that symbol. This is CSLib's clean-output convention. The final symbol need not occupy the
original input position. The alphabet and accepting symbol are fixed for the problem.
Every transition counts as one step, including stationary steps. The definitions also allow
alphabets containing just one symbol.

The separate certificate length and time bound follow Definition 2.7 in David Steurer's
[*P vs. NP and Diagonalization*, CS 6810, Lecture 2 (2012)][steurer2012].
The notes were recorded by Sin–Shuen Cheung.

[steurer2012]: https://www.dsteurer.org/complexity12/scribe/scribenote2.pdf#page=2
-/

@[expose] public section

namespace Algolean.Problems.TMSAT

open Cslib.Turing Algorithms.Alphabet Relation

/-- The tape stores symbols from `Γ` and one separate symbol between input and certificate. -/
abbrev TapeSymbol (Γ : Type) := Extended Γ 1

variable (Γ : Type) [Fintype Γ]

/-- An instance asks whether some certificate of the specified length makes the machine accept. -/
structure Instance where
  /-- This finite description specifies the deterministic verifier. -/
  verifier : SingleTapeTM.Description (TapeSymbol Γ)
  /-- This is the input whose certificate the verifier will check. -/
  input : List Γ
  /-- The certificate must contain exactly this many symbols of `Γ`. -/
  certificateLength : ℕ
  /-- The verifier must accept within this many machine transitions. -/
  time : ℕ

variable {Γ}

/-- The halted tape contains only the chosen accepting symbol, with the head on that symbol. -/
def accepting (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ)) :
    Set verifier.machine.Cfg :=
  {configuration | configuration.state = none ∧
    configuration.BiTape = BiTape.mk₁ [.inl yes]}

/-- The machine reaches an accepting configuration after at most the specified transitions. -/
def AcceptsWithin (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) (time : ℕ) : Prop :=
  verifier.machine.OutputsWithinTime word [.inl yes] time

/-- TMSAT's accepting configuration is exactly CSLib's halting configuration for `[yes]`. -/
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

/-- A yes instance has a certificate of the specified length that the verifier accepts in time. -/
def satisfiable (yes : Γ) : DecisionProblem (Instance Γ) :=
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
theorem mem_satisfiable_mono {yes : Γ} {problem : Instance Γ}
    (h : problem ∈ satisfiable yes)
    {time : ℕ} (hle : problem.time ≤ time) : {problem with time} ∈ satisfiable yes := by
  obtain ⟨certificate, hlength, hrun⟩ := h
  exact ⟨certificate, hlength, hrun.mono hle⟩

/-- A certificate of length zero must be empty. -/
@[simp] theorem mem_satisfiable_zero_length (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (input : List Γ) (time : ℕ) : (⟨verifier, input, 0, time⟩ : Instance Γ) ∈ satisfiable yes ↔
      AcceptsWithin yes verifier ((wordPair Γ).encode (input, [])) time := by
  simp [satisfiable]

/-- The initial state is not a halting state, so no instance accepts in zero transitions. -/
@[simp] theorem not_mem_satisfiable_zero (yes : Γ)
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (input : List Γ) (certificateLength : ℕ) :
    (⟨verifier, input, certificateLength, 0⟩ : Instance Γ) ∉ satisfiable yes := by
  simp [satisfiable]

end Algolean.Problems.TMSAT
