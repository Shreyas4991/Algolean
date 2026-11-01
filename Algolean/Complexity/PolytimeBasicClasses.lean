/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Programs with polynomial time bounds

This file defines programs that compute functions within a time bound and uses them to describe
yes/no problems. One fixed program must work on every input. It receives the input on the tape
and leaves the output with the head at its first symbol.

Time counts tape-head move instructions. Fuel separately limits execution: every instruction and
loop test uses fuel, even if it has no time cost. Running out of fuel does not count as
producing an answer.

## Main definitions and results

* [OutputsWithinTime](##Algolean.Algorithms.TMQuery.OutputsWithinTime) requires a program to
  finish with the specified output within the allowed time.
* [TimeComputable](##Algolean.Algorithms.TMQuery.TimeComputable) stores one program and a time
  bound for every input.
* [PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable) adds a polynomial bound
  on that time.
* [P](##Algolean.Algorithms.P) describes problems answered by programs with polynomial time
  bounds.
* [NP](##Algolean.Algorithms.NP) describes problems whose yes answers have certificates, or
  extra lists of symbols, that such programs can check.
* [NP.ofP](##Algolean.Algorithms.NP.ofP) shows that every problem in the first class belongs to
  the second by using an empty certificate.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A language specifies a yes/no problem about lists of symbols: it holds for exactly the inputs
whose answer is yes.
-/
abbrev Language (Symbol : Type) := List Symbol → Prop

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
This record stores one program that computes the specified function on every input, together
with a bound on its time as a function of input length.
-/
structure TimeComputable (f : List Symbol → List Symbol) where
  /-- This machine supplies the tape symbols, the named states, and the initial state. -/
  tm : SingleTapeTM Symbol
  /-- This field supplies a way to check whether two tape symbols are equal. -/
  [symbolDecidableEq : DecidableEq Symbol]
  /-- This field supplies a way to check whether two machine states are equal. -/
  [stateDecidableEq : DecidableEq tm.State]
  /-- The same program runs for every input and receives the input through its initial tape. -/
  program : Prog (TMQuery tm) Unit
  /-- This function gives the allowed number of head moves for each input length. -/
  timeBound : ℕ → ℕ
  /-- The program finishes with the required output within the allowed time on every input. -/
  outputsFunInTime (input : List Symbol) :
    OutputsWithinTime program input (f input) (timeBound input.length)

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
    outputsFunInTime := fun input => ⟨0, ⟨(), 0⟩, ⟨TMState.init _ input, 0⟩, rfl, rfl, le_rfl⟩ }

/-- The program that leaves its input unchanged has a polynomial time bound of zero. -/
noncomputable def PolyTimeComputable.id : PolyTimeComputable (Symbol := Symbol) id where
  toTimeComputable := TimeComputable.id
  poly := 0
  bounds _ := by simp [TimeComputable.id]

end TMQuery

/--
A problem belongs to this class when one fixed program computes a function in polynomial time
and produces a chosen acceptance word exactly on inputs whose answer is yes. Polynomial time is
specified by [PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable).
-/
def P (L : Language Symbol) : Prop :=
  ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    Nonempty (TMQuery.PolyTimeComputable f) ∧ ∀ x, f x = yes ↔ L x

/--
A problem belongs to this class when a program can check certificates in polynomial time. A
polynomial in the input length bounds the permitted certificate length. An input has answer yes
exactly when some permitted certificate makes the program accept.

The checking program receives the input followed immediately by the certificate on one tape. The
checking procedure must handle the boundary between them. Its time bound, specified by
[PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable), uses the length of that
combined input.
-/
def NP (L : Language Symbol) : Prop :=
  ∃ (V : List Symbol → List Symbol) (yes : List Symbol) (q : Polynomial ℕ),
    Nonempty (TMQuery.PolyTimeComputable V) ∧
    ∀ x, L x ↔ ∃ c : List Symbol,
      c.length ≤ q.eval x.length ∧ V (x ++ c) = yes

/--
Every problem in [P](##Algolean.Algorithms.P) belongs to [NP](##Algolean.Algorithms.NP). The
same program checks the input with an empty certificate.
-/
theorem NP.ofP {L : Language Symbol} (hP : P L) : NP L := by
  obtain ⟨f, yes, hPTC, hEq⟩ := hP
  refine ⟨f, yes, 0, hPTC, ?_⟩
  intro x
  refine ⟨fun hL => ⟨[], by simp, ?_⟩, ?_⟩
  · simpa using (hEq x).mpr hL
  · rintro ⟨c, hlen, hV⟩
    have hc : c = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp (by simpa using hlen))
    subst hc
    exact (hEq x).mp (by simpa using hV)

end Algorithms

end Algolean
