/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Frame
public import Algolean.Models.SingleTapeTM.Solves
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Computing word functions with one fixed Query program

`TimeComputable` stores a program that computes a word-valued function on every input, with a
running-time bound depending on input length. `PolyTimeComputable` adds a bounding polynomial.
The final tape contains exactly the output word, with its first cell under the head. These
are the output and bound conventions of CSLib's transition-table computation records.

Time counts Query move instructions. Interpreter fuel also accounts for instructions and
loop tests that do not move the head, and sufficient fuel is required for a completed run.
The compiler connects these records to CSLib's records with an affine overhead in time.

The `computesWithin` field is the common `TMSolves` correctness and resource statement for
word computation. A time bound `T(n)` gives the total space bound `max 1 n + T(n)`.
`outputsFunInTime` derives the per-input execution statement when a compiler or composition
proof needs it.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

namespace TMQuery

/--
The program finishes with the specified output tape and uses at most the allowed number of head
moves. Some finite amount of execution fuel must let it finish; the amount of fuel is separate
from this time bound.
-/
def OutputsWithinTime {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
    (program : Prog (TMQuery tm) Unit) (input output : List Symbol) (time : ℕ) : Prop :=
  ∃ fuel result final,
    execute fuel program (TMState.init tm input) = some (result, final) ∧
    final.machine.config.BiTape = BiTape.mk₁ output ∧ result.tell.steps ≤ time

/--
A Turing machine program that completes on the initialized input tape with the required output
and at most `time` head moves satisfies `OutputsWithinTime`. The proof reuses the completed
execution's fuel and resource count; the final absolute head coordinate may differ from its
initial value, provided the head points to the first output cell.
-/
theorem Completes.outputsWithinTime {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State] {program : Prog (TMQuery tm) Unit}
    {input output : List Symbol} {cost : TMCost} {final : TMState tm} {time : ℕ}
    (h : Completes program (TMState.init tm input) cost final)
    (outputTape : final.config.BiTape = BiTape.mk₁ output) (bound : cost.steps ≤ time) :
    OutputsWithinTime program input output time := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, h, outputTape, bound⟩

/--
This record stores one program that computes the specified function on every input, together
with a bound on its time as a function of input length.
-/
structure TimeComputable (f : List Symbol → List Symbol) where
  /-- This machine specifies the tape symbols, the named states, and the initial state. -/
  tm : SingleTapeTM Symbol
  /-- This field defines a way to check whether two tape symbols are equal. -/
  [symbolDecidableEq : DecidableEq Symbol]
  /-- This field defines a way to check whether two machine states are equal. -/
  [stateDecidableEq : DecidableEq tm.State]
  /-- The same program runs for every input and receives the input through its initial tape. -/
  program : Prog (TMQuery tm) Unit
  /-- This function gives the allowed number of head moves for each input length. -/
  timeBound : ℕ → ℕ
  /--
  The same program computes the required output on every input within the time bound. Total
  space is bounded by the initial input space plus that time bound.
  -/
  computesWithin : ComputesWithin program f timeBound (fun n => max 1 n + timeBound n)

/--
This record adds a polynomial time bound to a
[TimeComputable](##Algolean.Algorithms.TMQuery.TimeComputable) program.
-/
structure PolyTimeComputable (f : List Symbol → List Symbol) extends TimeComputable f where
  /-- This polynomial bounds the time as a function of input length. -/
  poly : Polynomial ℕ
  /-- The allowed time is at most the polynomial's value at every input length. -/
  bounds : ∀ n, timeBound n ≤ poly.eval n

/-- A completed execution also satisfies any larger time bound. -/
theorem OutputsWithinTime.mono {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State] {program : Prog (TMQuery tm) Unit}
    {input output : List Symbol} {time time' : ℕ}
    (h : OutputsWithinTime program input output time) (hle : time ≤ time') :
    OutputsWithinTime program input output time' := by
  grind [OutputsWithinTime]

section FixedProgram

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {program : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
variable {time space : ℕ → ℕ}

/--
The initialized-output predicate describes the same completed executions as `Completes`.
Unused interpreter fuel can be removed without changing the output or resource count.
-/
theorem OutputsWithinTime.iff_completes {input output : List Symbol} {bound : ℕ} :
    OutputsWithinTime program input output bound ↔
      ∃ cost final, Completes program (TMState.init tm input) cost final ∧
        final.config.BiTape = BiTape.mk₁ output ∧ cost.steps ≤ bound := by
  constructor
  · rintro ⟨fuel, result, final, hr, ht, hb⟩
    exact ⟨result.tell, final.machine, completes_of_execute hr, ht, hb⟩
  · rintro ⟨cost, final, hc, ht, hb⟩
    exact hc.outputsWithinTime ht hb

/-- Forgetting the space bound recovers the existing per-input output and time predicate. -/
theorem ComputesWithin.outputsWithinTime (h : ComputesWithin program f time space)
    (input : List Symbol) : OutputsWithinTime program input (f input) (time input.length) := by
  obtain ⟨cost, final, hc, ht, hb, _⟩ := h input
  exact hc.outputsWithinTime ht hb

end FixedProgram

/-- The stored common correctness statement gives the output and time bound on each input. -/
theorem TimeComputable.outputsFunInTime {f : List Symbol → List Symbol}
    (computer : TimeComputable f) (input : List Symbol) :
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    OutputsWithinTime computer.program input (f input) (computer.timeBound input.length) := by
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  exact computer.computesWithin.outputsWithinTime input

section FixedProgram

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {program : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
variable {time space : ℕ → ℕ}

/--
Computing the required output within a time bound gives a `TMSolves` statement with total
space bounded by the initial input space plus that time bound.
-/
theorem ComputesWithin.of_outputsWithinTime
    (h : ∀ input, OutputsWithinTime program input (f input) (time input.length)) :
    ComputesWithin program f time (fun n => max 1 n + time n) :=
  TMSolves.of_time_bound (fun input => OutputsWithinTime.iff_completes.mp (h input))

/-- The same program and time bound give a record with the automatic space bound from time. -/
def ComputesWithin.timeComputable (h : ComputesWithin program f time space) :
    TimeComputable f where
  tm := tm
  program := program
  timeBound := time
  computesWithin := ComputesWithin.of_outputsWithinTime h.outputsWithinTime

/-- A polynomial bound packages the same program as a polynomial-time computation record. -/
def ComputesWithin.polyTimeComputable (h : ComputesWithin program f time space)
    (poly : Polynomial ℕ) (bound : ∀ n, time n ≤ poly.eval n) : PolyTimeComputable f where
  toTimeComputable := h.timeComputable
  poly := poly
  bounds := bound

end FixedProgram

/--
The stored polynomial bounds both time and additional tape space for the same fixed program.
Total space also includes `max 1 n` cells for the initial input.
-/
theorem PolyTimeComputable.computesWithin_poly {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) :
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    ComputesWithin computer.program f computer.poly.eval
      (fun n => max 1 n + computer.poly.eval n) := by
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  exact ComputesWithin.of_outputsWithinTime
    (fun input => (computer.outputsFunInTime input).mono (computer.bounds input.length))

/--
This program computes the identity function by leaving every input unchanged and making no head
moves.
-/
noncomputable def TimeComputable.id : TimeComputable (Symbol := Symbol) id := by
  classical
  exact {
    tm := SingleTapeTM.idComputer
    program := pure ()
    timeBound := fun _ => 0
    computesWithin := ComputesWithin.of_outputsWithinTime (fun input =>
      ⟨0, ⟨(), 0⟩, ⟨TMState.init _ input, 0⟩, rfl, rfl, le_rfl⟩) }

/-- The program that leaves its input unchanged has a polynomial time bound of zero. -/
noncomputable def PolyTimeComputable.id : PolyTimeComputable (Symbol := Symbol) id where
  toTimeComputable := TimeComputable.id
  poly := 0
  bounds _ := by simp [TimeComputable.id]

end TMQuery

end Algolean.Algorithms
