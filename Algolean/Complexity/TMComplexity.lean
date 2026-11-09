/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Transformations
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Computability results for appending and complementing Boolean words

This file derives `TMQuery.Computes` proofs for the Turing machine programs `appendBit` and
`complementBlock` from their execution theorems in `Transformations`. The first program appends a
chosen bit, and the second negates every bit of the input. Both restore the starting head
coordinate, preserve the control state, and use exactly `2 * input.length + 2` head moves.

The proofs apply to every Boolean input word and any starting control state, head coordinate,
and recorded tape history satisfying the input-tape assumption. The `Computer` definitions bundle
the programs with these proofs so that they can run in sequence on the tape left by an earlier
computation.

The `PolyTimeComputable` definitions use the conversions in
[Functions.lean](Algolean/Models/SingleTapeTM/Composition/Functions.html) to produce witnesses for
the complexity definitions in
[PolytimeBasicClasses.lean](Algolean/Complexity/PolytimeBasicClasses.html). Time here counts head
moves; tests and writes also consume interpreter fuel.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
The append program computes `input ++ [bit]` for every input and returns the head to the starting
coordinate. Its correctness proof bounds the cost by `2 * input.length + 2` head moves;
`appendBit_correct` proves that this count is exact.
-/
theorem appendBit_computes (bit : Bool) :
    Computes (appendBit tm bit) (fun bits => bits ++ [bit]) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [cursor_start] using appendBit_correct input bit s (by simpa [cursor_start] using hs)

/--
The block-complementing program negates every input bit and returns the head to the starting
coordinate. Its time bound allows `2 * input.length + 2` head moves, which the exact correctness
theorem shows it uses regardless of the bit values.
-/
theorem complementBlock_computes :
    Computes (complementBlock tm) (List.map Bool.not) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [cursor_start] using complementBlock_correct input s (by simpa [cursor_start] using hs)

/--
This value contains a verified Turing machine program that appends `bit` to the input and restores
the head to the first output cell. It packages the append program with a bound of `2 * input.length
+ 2` head moves so that another word transformation can run on the result.
-/
def appendBitComputer (bit : Bool) :
    Computer tm (fun bits => bits ++ [bit]) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (appendBit_computes (tm := tm) bit)

/--
This value contains a verified Turing machine program that negates every input bit and restores the
original head coordinate. It packages the complementing program with its correctness proof and the
bound of `2 * input.length + 2` head moves.
-/
def complementBlockComputer :
    Computer tm (List.map Bool.not) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (complementBlock_computes (tm := tm))

/--
This value proves polynomial-time computability of appending the fixed bit `bit`. It uses the actual
append program and its linear bound of `2 * input.length + 2` head moves.
-/
noncomputable def appendBitPolyTimeComputable (bit : Bool) :
    TMQuery.PolyTimeComputable (fun bits => bits ++ [bit]) :=
  Computer.polyTimeComputable (tm := tm) (poly := 2 * X + 2)
    (EncodedComputer.mono (appendBitComputer (tm := tm) bit) (by intro input; simp))

/--
This value proves polynomial-time computability of negating every bit in a word. It uses the
block-complementing program and its linear bound of `2 * input.length + 2` head moves.
-/
noncomputable def complementBlockPolyTimeComputable :
    TMQuery.PolyTimeComputable (List.map Bool.not) :=
  Computer.polyTimeComputable (tm := tm) (poly := 2 * X + 2)
    (EncodedComputer.mono (complementBlockComputer (tm := tm)) (by intro input; simp))

end Algolean.Algorithms.SingleTapeTuringMachines
