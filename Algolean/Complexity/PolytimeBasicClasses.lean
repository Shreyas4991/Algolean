/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Basic Complexity Classes on Single Tape Turing Machines

We define `P` and `NP` using deeply embedded `TMQuery` programs interpreted by `TMModel`.
`TMQuery.TimeComputable` bundles one fixed `Prog (TMQuery tm) Unit`, a time bound, and a proof
that it computes the specified function on every input. `TMQuery.PolyTimeComputable` supplies
a polynomial bound. The program is chosen before quantifying over inputs: neither the input
nor its length is an argument to the program.

Inputs enter only through `TMState.init`. Successful program completion is halting, and output
is read from the final tape, with the head at the first output symbol, as represented by
`BiTape.mk₁`. The control-state label at completion is unrestricted. Interpreter fuel witnesses
termination and is separate from the model's time cost, which counts head-move queries.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A language over alphabet `Symbol`. -/
abbrev Language (Symbol : Type) := List Symbol → Prop

namespace TMQuery

/-- A completed query execution produces `output` on its final tape within a head-move bound.
The existential fuel is an interpreter budget, supplied separately from the fixed program. -/
def OutputsWithinTime {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
    (program : Prog (TMQuery tm) Unit) (input output : List Symbol) (time : ℕ) : Prop :=
  ∃ fuel result final,
    execute fuel program (TMState.init tm input) = some (result, final) ∧
    final.machine.config.BiTape = BiTape.mk₁ output ∧ result.tell.steps ≤ time

/-- A fixed deeply embedded program computing `f` on every input with a uniform time bound. -/
structure TimeComputable (f : List Symbol → List Symbol) where
  /-- Finite alphabet and control-state data for the query model. -/
  tm : SingleTapeTM Symbol
  /-- Executable equality on tape symbols. -/
  [symbolDecidableEq : DecidableEq Symbol]
  /-- Executable equality on control-state labels. -/
  [stateDecidableEq : DecidableEq tm.State]
  /-- One program, independent of the input and its length. -/
  program : Prog (TMQuery tm) Unit
  /-- Time bound as a function of input length. -/
  timeBound : ℕ → ℕ
  /-- The same program completes correctly within the bound on every input. -/
  outputsFunInTime (input : List Symbol) :
    OutputsWithinTime program input (f input) (timeBound input.length)

/-- A polynomial-time function computed by one deeply embedded TM query program. -/
structure PolyTimeComputable (f : List Symbol → List Symbol) extends TimeComputable f where
  /-- Polynomial bounding the head-move cost. -/
  poly : Polynomial ℕ
  /-- The time bound is polynomial in input length. -/
  bounds : ∀ n, timeBound n ≤ poly.eval n

/-- Enlarging a time bound preserves a completed execution witness. -/
theorem OutputsWithinTime.mono {tm : SingleTapeTM Symbol}
    [DecidableEq Symbol] [DecidableEq tm.State] {program : Prog (TMQuery tm) Unit}
    {input output : List Symbol} {time time' : ℕ}
    (h : OutputsWithinTime program input output time) (hle : time ≤ time') :
    OutputsWithinTime program input output time' := by
  grind [OutputsWithinTime]

/-- Leaving the initial tape untouched computes the identity function in zero head moves. -/
noncomputable def TimeComputable.id : TimeComputable (Symbol := Symbol) id := by
  classical
  exact {
    tm := SingleTapeTM.idComputer
    program := pure ()
    timeBound := fun _ => 0
    outputsFunInTime := fun input => ⟨0, ⟨(), 0⟩, ⟨TMState.init _ input, 0⟩, rfl, rfl, le_rfl⟩ }

/-- The identity query program is polynomial-time computable. -/
noncomputable def PolyTimeComputable.id : PolyTimeComputable (Symbol := Symbol) id where
  toTimeComputable := TimeComputable.id
  poly := 0
  bounds _ := by simp [TimeComputable.id]

end TMQuery

/-- A language `L` is in `P` if one fixed TM query program computes a function
`f : List Symbol → List Symbol` in polynomial time, and a fixed accept string
`yes` satisfies `f x = yes` exactly when `L x` holds. -/
def P (L : Language Symbol) : Prop :=
  ∃ (f : List Symbol → List Symbol) (yes : List Symbol),
    Nonempty (TMQuery.PolyTimeComputable f) ∧ ∀ x, f x = yes ↔ L x

/-- A language `L` is in `NP` if one fixed polynomial-time TM query program computes
a verifier `V : List Symbol → List Symbol`, with a fixed accept string `yes`,
and a polynomial certificate-length bound `q` such that `L x` iff some
certificate `c` of length at most `q(|x|)` makes `V (x ++ c) = yes`.
The verifier receives input and certificate concatenated on a single
tape; the boundary is handled per-language by the verifier. -/
def NP (L : Language Symbol) : Prop :=
  ∃ (V : List Symbol → List Symbol) (yes : List Symbol) (q : Polynomial ℕ),
    Nonempty (TMQuery.PolyTimeComputable V) ∧
    ∀ x, L x ↔ ∃ c : List Symbol,
      c.length ≤ q.eval x.length ∧ V (x ++ c) = yes

/-- `P ⊆ NP`: every language in `P` is in `NP` with the empty certificate. -/
theorem NP.ofP {L : Language Symbol} (hP : P L) : NP L := by
  obtain ⟨f, yes, hPTC, hEq⟩ := hP
  refine ⟨f, yes, 0, hPTC, ?_⟩
  simpa using fun x => (hEq x).symm

end Algorithms

end Algolean
