/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Algolean.Models.SingleTapeTM.BoundedVerification

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

open Cslib.Turing

export SingleTapeTM.BoundedVerification
  (TapeSymbol accepting AcceptsWithin mem_accepting_iff acceptsWithin_iff_exists
    not_acceptsWithin_zero acceptsWithin_one_iff AcceptsWithin.mono
    acceptsWithin_iff_of_outputsWithinTime)

/-- A TMSAT instance specifies bounded certificate verification. -/
abbrev Instance (Γ : Type) := SingleTapeTM.BoundedVerification Γ

variable {Γ : Type} [Fintype Γ]

/-- A TMSAT instance is satisfiable when its verifier accepts some certificate within its bounds. -/
abbrev satisfiable (yes : Γ) : DecisionProblem (Instance Γ) :=
  SingleTapeTM.BoundedVerification.accepted yes

/-- Allowing more transitions preserves a satisfiable instance. -/
alias mem_satisfiable_mono := SingleTapeTM.BoundedVerification.mem_accepted_mono
/-- A certificate of length zero is empty. -/
alias mem_satisfiable_zero_length := SingleTapeTM.BoundedVerification.mem_accepted_zero_length
/-- The initial state has not halted, so zero transitions cannot accept. -/
alias not_mem_satisfiable_zero := SingleTapeTM.BoundedVerification.not_mem_accepted_zero

end Algolean.Problems.TMSAT
