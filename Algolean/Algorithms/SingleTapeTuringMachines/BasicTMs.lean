/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Erasing
public import Algolean.Algorithms.SingleTapeTuringMachines.Increment
public import Algolean.Algorithms.SingleTapeTuringMachines.Transformations
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Six basic Boolean Turing machine programs

This file packages correctness proofs and time bounds for six Turing machine programs.

* `writeBit` replaces the first bit, or writes one bit when the input is empty.
* `flipBit` negates the first bit and leaves empty input empty.
* `appendBit` appends a chosen bit to the input word.
* `complementBlock` negates every input bit.
* `eraseBlock` erases the entire input word.
* `increment` adds one to a binary number stored with its least significant bit first.

Each program preserves the control state and restores the starting head coordinate. Writing and
flipping use zero head moves; the other four use at most `2 * input.length + 2`. The `Computer`
values carry these proofs so the programs can run in sequence. The `PolyTimeComputable` values
prove polynomial-time computability of the other four programs, counting head moves as time.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Writing `bit` replaces the first input bit, or creates a one-bit word on empty input. -/
theorem writeBit_computes (bit : Bool) :
    Computes (writeBit tm bit) (fun bits => bit :: bits.tail) (fun _ => 0) := by
  intro input s hs
  refine ⟨0, ?_, le_rfl⟩
  cases input <;> simpa [hs, BiTape.mk₁, BiTape.nil, BiTape.write] using writeBit_correct s bit

/-- This Lean function negates the first bit and preserves the rest. Empty input stays empty. -/
def flipFirst : List Bool → List Bool
  | [] => []
  | bit :: bits => bit.not :: bits

/-- Flipping the first bit computes `flipFirst` without moving the head. -/
theorem flipBit_computes : Computes (flipBit tm) flipFirst (fun _ => 0) := by
  intro input s hs
  refine ⟨0, ?_, le_rfl⟩
  cases input <;>
    simpa [flipFirst, hs, BiTape.mk₁, BiTape.nil, BiTape.write] using flipBit_correct s

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
The erasing program computes the empty output word on every input and returns the head to its
starting coordinate. Its time bound allows `2 * input.length + 2` head moves, matching the exact
cost proved by `eraseBlock_correct`.
-/
theorem eraseBlock_computes :
    Computes (eraseBlock tm) (fun _ => []) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [BiTape.mk₁] using eraseBlock_correct input s (by simpa [cursor_start] using hs)

/--
The increment program adds one to the input interpreted with its least significant bit first and
returns the head to the starting coordinate. The correctness proof bounds carry propagation and the
return trip by `2 * input.length + 2` head moves, including overflow.
-/
theorem increment_computes :
    Computes (increment tm) incrementBits (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * carryCount input + 2, ?_, ?_⟩
  · simpa [cursor_start] using increment_correct input s (by simpa [cursor_start] using hs)
  · have := carryCount_le_length input
    lia

/-- This value pairs the bit-writing program with its correctness proof and zero head-move bound. -/
def writeBitComputer (bit : Bool) : Computer tm (fun bits => bit :: bits.tail) (fun _ => 0) :=
  Computer.ofComputes (writeBit_computes (tm := tm) bit)

/-- This value pairs the bit-flipping program with its output proof and zero head-move bound. -/
def flipBitComputer : Computer tm flipFirst (fun _ => 0) :=
  Computer.ofComputes (flipBit_computes (tm := tm))

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
This value contains a verified Turing machine program that erases the entire input and leaves the
head at its original coordinate on a blank tape. It packages the erasing program with its
correctness proof and the bound of `2 * input.length + 2` head moves.
-/
def eraseBlockComputer : Computer tm (fun _ => []) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (eraseBlock_computes (tm := tm))

/--
This value contains a verified Turing machine program that adds one to a binary word stored with its
least significant bit first and restores the original head coordinate. Its correctness proof covers
overflow and bounds the cost by `2 * input.length + 2` head moves.
-/
def incrementComputer : Computer tm incrementBits (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (increment_computes (tm := tm))

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

/--
This value proves polynomial-time computability of replacing every input word with the empty word.
It uses the tape-erasing program and its linear bound of `2 * input.length + 2` head moves.
-/
noncomputable def eraseBlockPolyTimeComputable :
    TMQuery.PolyTimeComputable (fun _ : List Bool => []) :=
  Computer.polyTimeComputable (tm := tm) (poly := 2 * X + 2)
    (EncodedComputer.mono (eraseBlockComputer (tm := tm)) (by intro input; simp))

/--
This value proves polynomial-time computability of binary increment with the least significant bit
first. It uses the increment program, including its carry and head-restoration phases, with a linear
bound of `2 * input.length + 2` head moves.
-/
noncomputable def incrementPolyTimeComputable : TMQuery.PolyTimeComputable incrementBits :=
  Computer.polyTimeComputable (tm := tm) (poly := 2 * X + 2)
    (EncodedComputer.mono (incrementComputer (tm := tm)) (by intro input; simp))

end Algolean.Algorithms.SingleTapeTuringMachines
