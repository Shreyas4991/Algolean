/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Size
public import Algolean.Models.SingleTapeTM.Computability
public import Algolean.Models.SingleTapeTM.Description

import Algolean.Models.SingleTapeTM.Compiler.Internal.Correctness
import Algolean.Models.SingleTapeTM.Compiler.Internal.Description

/-!
# Compiling query programs to transition-table machines

This file proves that compilation preserves outputs and gives an affine bound on transition counts.

* `Compiler.compile` constructs a finite transition table over the same tape alphabet.
* `Compiler.correct` states that the compiled machine produces exactly the query program's outputs.
* `Compiler.time_bound` bounds the compiled transitions by `C * time + C` for a fixed constant `C`.
* `Compiler.transitionFactor_eq` gives `C = (K + 1) * (A + 1)`, where `K` is the number of
  compiled control states and `A` is the number of tape symbols, excluding blank.
* `Compiler.compiled_state_count_le` bounds `K` by `(L + 1) * (Q + 1)`, where `L` counts source
  instructions and `Q` counts logical labels. Each compiled state stores a program position and a
  logical label, which can also be `none`. The source type `tm.State` supplies the logical labels.
* `Compiler.transitionFactor_le` bounds `C` using only source instruction and logical label counts.
* `TimeComputable.toTransitionTable` and `PolyTimeComputable.toTransitionTable` preserve the
  computed function and its time guarantee.

Branch alternatives and loop bodies contribute their instructions once to `L`.
For a fixed query program and source machine, `C` is independent of input length.
A source time bound `T(n)` therefore becomes `C * T(n) + C`, which is affine in source running time.
The state and constant bounds also describe dependence on the source program's size.
No bound on interpreter fuel is assumed.
-/

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

namespace Compiler

variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- This compiler constructs a finite transition table that executes the supplied query program. -/
public noncomputable def compile (program : Prog (TMQuery tm) Unit) :
    SingleTapeTM.Description Symbol :=
  Internal.describe (Internal.machine program)

/--
This constant is both the coefficient and the additive term in the compiled time bound.
For `K` compiled control states and `A` tape symbols other than blank, it is `(K + 1) * (A + 1)`.
The extra choices account for the halting state and the blank symbol.
For a fixed query program and source machine, it is independent of input length.
-/
public noncomputable def transitionFactor (program : Prog (TMQuery tm) Unit) : ℕ :=
  Internal.stationaryBound (Internal.machine program)

theorem compiled_state_count_eq_impl (program : Prog (TMQuery tm) Unit) :
    (compile program).states + 1 = Fintype.card (Internal.machine program).State := by
  change Fintype.card (Internal.machine program).State - 1 + 1 = _
  have hpos : 0 < Fintype.card (Internal.machine program).State :=
    Fintype.card_pos_iff.mpr ⟨(Internal.machine program).q₀⟩
  lia

theorem transitionFactor_eq_impl (program : Prog (TMQuery tm) Unit) :
    transitionFactor program =
      ((compile program).states + 2) * (Fintype.card Symbol + 1) := by
  simp only [transitionFactor, Internal.stationaryBound, Fintype.card_prod,
    Fintype.card_option]
  rw [← compiled_state_count_eq_impl program]

/--
Both constants in the time bound are `(K + 1) * (A + 1)`, where `K` is the number of compiled
control states and `A` counts tape symbols other than blank. A description numbers its states
from zero through `states`, so `K = states + 1`.
For a fixed query program and source machine, both constants are the same for every input.
-/
public theorem transitionFactor_eq (program : Prog (TMQuery tm) Unit) :
    let K := (compile program).states + 1
    let A := Fintype.card Symbol
    transitionFactor program = (K + 1) * (A + 1) :=
  transitionFactor_eq_impl program

theorem compiled_state_count_le_impl (program : Prog (TMQuery tm) Unit) :
    let L := instructionCount program
    let Q := Fintype.card tm.State
    let K := (compile program).states + 1
    K ≤ (L + 1) * (Q + 1) := by
  dsimp only
  rw [compiled_state_count_eq_impl]
  change Fintype.card (Internal.CompiledState program) ≤ _
  simp only [Internal.CompiledState, Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
  exact Nat.mul_le_mul_right _
    (Internal.card_residuals_le (Internal.instructions program) (pure ()))

/--
The compiled machine has at most `(L + 1) * (Q + 1)` control states. Here `L` counts source
instructions and `Q` counts logical labels in `tm.State`. There is at most one program position
per instruction, plus completion. Each compiled state pairs a position with a logical label,
which can also be `none`.
For a fixed logical label count `Q`, this bound is linear in program size `L`.
-/
public theorem compiled_state_count_le (program : Prog (TMQuery tm) Unit) :
    let L := instructionCount program
    let Q := Fintype.card tm.State
    let K := (compile program).states + 1
    K ≤ (L + 1) * (Q + 1) :=
  compiled_state_count_le_impl program

theorem transitionFactor_le_impl (program : Prog (TMQuery tm) Unit) :
    transitionFactor program ≤
      ((instructionCount program + 1) * (Fintype.card tm.State + 1) + 1) *
        (Fintype.card Symbol + 1) := by
  rw [transitionFactor_eq_impl]
  apply Nat.mul_le_mul_right
  have hstates := compiled_state_count_le_impl program
  lia

/--
Both constants in the time bound are at most `((L + 1) * (Q + 1) + 1) * (A + 1)`.
Here `L` counts source instructions, `Q` counts logical labels, and `A` counts tape symbols
other than blank. These counts are independent of the input and the number of loop iterations.
-/
public theorem transitionFactor_le (program : Prog (TMQuery tm) Unit) :
    let L := instructionCount program
    let Q := Fintype.card tm.State
    let A := Fintype.card Symbol
    transitionFactor program ≤ ((L + 1) * (Q + 1) + 1) * (A + 1) :=
  transitionFactor_le_impl program

theorem correct_impl (program : Prog (TMQuery tm) Unit) (input output : List Symbol) :
    (compile program).machine.Outputs input output ↔
      ∃ time, OutputsWithinTime program input output time := by
  constructor
  · intro h
    obtain ⟨steps, hsteps⟩ := h.relatesInSteps
    have hraw := (Internal.describe_outputsWithinTime_iff (Internal.machine program)
      input output steps).mp ⟨steps, le_rfl, hsteps⟩
    exact (Internal.outputs_iff program input output).mp hraw.choose_spec.2.reflTransGen
  · rintro ⟨time, h⟩
    have hcompiled := (Internal.describe_outputsWithinTime_iff (Internal.machine program)
      input output _).mpr (Internal.outputsWithinTime program h)
    exact hcompiled.choose_spec.2.reflTransGen

/-- The compiled machine produces an output exactly when the query program produces that output. -/
public theorem correct (program : Prog (TMQuery tm) Unit) (input output : List Symbol) :
    (compile program).machine.Outputs input output ↔
      ∃ time, OutputsWithinTime program input output time :=
  correct_impl program input output

theorem time_bound_impl (program : Prog (TMQuery tm) Unit) {input output : List Symbol} {time : ℕ}
    (h : OutputsWithinTime program input output time) :
    let C := transitionFactor program
    (compile program).machine.OutputsWithinTime input output (C * time + C) := by
  dsimp only
  apply (Internal.describe_outputsWithinTime_iff (Internal.machine program) input output _).mpr
  simpa only [transitionFactor, Nat.mul_add, Nat.mul_one] using
    Internal.outputsWithinTime program h

/--
Compilation preserves a time bound with a constant factor and a constant term. Both constants
depend only on the query program and source machine. A source time bound `T(n)` becomes
`C * T(n) + C`, with `C` independent of input length `n` and the allowed time.
Thus the compiled time bound is affine in the source time bound.
For `K` compiled control states and `A` tape symbols other than blank, each constant is
`(K + 1) * (A + 1)`, as stated in `transitionFactor_eq`.
-/
public theorem time_bound (program : Prog (TMQuery tm) Unit)
    {input output : List Symbol} {time : ℕ} (h : OutputsWithinTime program input output time) :
    let C := transitionFactor program
    (compile program).machine.OutputsWithinTime input output (C * time + C) :=
  time_bound_impl program h

end Compiler

noncomputable def timeComputableImpl {f : List Symbol → List Symbol} (computer : TimeComputable f) :
    SingleTapeTM.TimeComputable f := by
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  exact {
    tm := (Compiler.compile computer.program).machine
    timeBound n := Compiler.transitionFactor computer.program * computer.timeBound n +
      Compiler.transitionFactor computer.program
    outputsFunInTime input :=
      Compiler.time_bound computer.program (computer.outputsFunInTime input) }

/--
This conversion supplies an ordinary transition-table machine for the same function. Its time
bound is `C * T(n) + C` for a source bound `T(n)`. The query program and source machine fix `C`,
independently of input length. Thus the overhead is affine in source running time.
-/
public noncomputable def TimeComputable.toTransitionTable {f : List Symbol → List Symbol}
    (computer : TimeComputable f) : SingleTapeTM.TimeComputable f := timeComputableImpl computer

noncomputable def polyTimeComputableImpl {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) : SingleTapeTM.PolyTimeComputable f := by
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  let factor := Compiler.transitionFactor computer.program
  exact {
    toTimeComputable := computer.toTimeComputable.toTransitionTable
    poly := Polynomial.C factor * computer.poly + Polynomial.C factor
    bounds n := by
      change factor * computer.timeBound n + factor ≤
        (Polynomial.C factor * computer.poly + Polynomial.C factor).eval n
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left factor (computer.bounds n)) factor }

/--
This conversion preserves polynomial-time computability. The polynomial is multiplied by the
fixed compilation factor, and the same constant is added to account for finishing the program.
The factor is independent of input length, so the resulting time bound remains polynomial.
-/
public noncomputable def PolyTimeComputable.toTransitionTable {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) : SingleTapeTM.PolyTimeComputable f :=
  polyTimeComputableImpl computer

end Algolean.Algorithms.TMQuery
