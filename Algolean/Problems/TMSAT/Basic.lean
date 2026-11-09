/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Algolean.Models.SingleTapeTM.Description
public import Algolean.Models.SingleTapeTM.Alphabet.Pair

/-!
# Turing machine satisfiability

* An `Instance` contains a deterministic machine, an input, a certificate length, and a time bound.
* `satisfiable` contains the instances with a certificate accepted within that bound.
* Certificates are Boolean words of exactly the specified length.

The machine receives the separator encoding of the input and certificate. It accepts by halting
with a true bit under the head. Every transition counts as one step, including stationary steps.

The separate certificate length and time bound follow Definition 2.7 in David Steurer's
[*P vs. NP and Diagonalization*, CS 6810, Lecture 2 (2012)][steurer2012].
The notes were recorded by Sin–Shuen Cheung.

[steurer2012]: https://www.dsteurer.org/complexity12/scribe/scribenote2.pdf#page=2
-/

@[expose] public section

namespace Algolean.Problems.TMSAT

open Cslib.Turing Algorithms.Alphabet Relation

/-- The tape stores Boolean bits and a separate symbol between the input and certificate. -/
abbrev TapeSymbol := Extended Bool 1

/-- An instance asks whether some certificate of the specified length makes the machine accept. -/
structure Instance where
  /-- This finite description specifies the deterministic verifier. -/
  verifier : SingleTapeTM.Description TapeSymbol
  /-- This is the input whose certificate the verifier will check. -/
  input : List Bool
  /-- The certificate must contain exactly this many Boolean bits. -/
  certificateLength : ℕ
  /-- The verifier must accept within this many machine transitions. -/
  time : ℕ

/-- A configuration accepts when the machine has halted with a true bit under its head. -/
def accepting (verifier : SingleTapeTM.Description TapeSymbol) : Set verifier.machine.Cfg :=
  {configuration | configuration.state = none ∧ configuration.BiTape.head = some (.inl true)}

/-- The machine reaches an accepting configuration after at most the specified transitions. -/
def AcceptsWithin (verifier : SingleTapeTM.Description TapeSymbol)
    (word : List TapeSymbol) (time : ℕ) : Prop :=
  ∃ final ∈ accepting verifier,
    RelatesWithinSteps verifier.machine.TransitionRelation
      (verifier.machine.initCfg word) final time

/-- A yes instance has a certificate of the specified length that the verifier accepts in time. -/
def satisfiable : DecisionProblem Instance :=
  {problem | ∃ certificate : List Bool, certificate.length = problem.certificateLength ∧
    AcceptsWithin problem.verifier ((wordPair Bool).encode (problem.input, certificate))
      problem.time}

/-- An initial configuration cannot already be accepting because its state has not halted. -/
@[simp] theorem not_acceptsWithin_zero (verifier : SingleTapeTM.Description TapeSymbol)
    (word : List TapeSymbol) : ¬AcceptsWithin verifier word 0 := by
  simp [AcceptsWithin, accepting, SingleTapeTM.initCfg]

/-- Acceptance within one transition requires that transition to halt with an accepting symbol. -/
theorem acceptsWithin_one_iff (verifier : SingleTapeTM.Description TapeSymbol)
    (word : List TapeSymbol) : AcceptsWithin verifier word 1 ↔
      ∃ final ∈ accepting verifier, verifier.machine.step (verifier.machine.initCfg word) =
        some final := by
  constructor
  · rintro ⟨final, hfinal, steps, hle, hrun⟩
    cases steps with
    | zero =>
      have heq := hrun.zero
      subst final
      simp [accepting, SingleTapeTM.initCfg] at hfinal
    | succ steps =>
      have hzero : steps = 0 := by omega
      subst steps
      exact ⟨final, hfinal, by
        simpa [RelatesInSteps.succ_iff, SingleTapeTM.TransitionRelation] using hrun⟩
  · rintro ⟨final, hfinal, hstep⟩
    exact ⟨final, hfinal, RelatesWithinSteps.single hstep⟩

/-- Allowing more transitions preserves acceptance. -/
theorem AcceptsWithin.mono {verifier : SingleTapeTM.Description TapeSymbol}
    {word : List TapeSymbol} {time time' : ℕ} (h : AcceptsWithin verifier word time)
    (hle : time ≤ time') : AcceptsWithin verifier word time' := by
  obtain ⟨final, hfinal, hrun⟩ := h
  exact ⟨final, hfinal, RelatesWithinSteps.mono hle hrun⟩

/-- Allowing more time preserves acceptance without changing the required certificate length. -/
theorem mem_satisfiable_mono {problem : Instance} (h : problem ∈ satisfiable)
    {time : ℕ} (hle : problem.time ≤ time) : {problem with time} ∈ satisfiable := by
  obtain ⟨certificate, hlength, hrun⟩ := h
  exact ⟨certificate, hlength, hrun.mono hle⟩

/-- A certificate of length zero must be empty. -/
@[simp] theorem mem_satisfiable_zero_length (verifier : SingleTapeTM.Description TapeSymbol)
    (input : List Bool) (time : ℕ) : (⟨verifier, input, 0, time⟩ : Instance) ∈ satisfiable ↔
      AcceptsWithin verifier ((wordPair Bool).encode (input, [])) time := by
  simp [satisfiable]

/-- The initial state is not a halting state, so no instance accepts in zero transitions. -/
@[simp] theorem not_mem_satisfiable_zero (verifier : SingleTapeTM.Description TapeSymbol)
    (input : List Bool) (certificateLength : ℕ) :
    (⟨verifier, input, certificateLength, 0⟩ : Instance) ∉ satisfiable := by
  simp [satisfiable, AcceptsWithin, accepting, SingleTapeTM.initCfg]

end Algolean.Problems.TMSAT
