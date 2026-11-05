/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Transformations
public import Algolean.Algorithms.SingleTapeTuringMachines.Erasing
public import Algolean.Algorithms.SingleTapeTuringMachines.Increment
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Computability results for seven Boolean-tape programs

This file uses the execution theorems proved in `Basic`, `BitOperations`, `Transformations`,
`Erasing`, and `Increment` to derive `TMQuery.Computes` proofs for seven specific Turing machine
programs. Their tape symbols are Boolean values, and their input and output words are lists of
those values.

The program `identity` preserves the input, `writeBit` replaces its first bit, and `flipBit` negates
its first bit. These three programs use zero head moves. The program `appendBit` appends a chosen
bit, `complementBlock` negates every bit, and `eraseBlock` erases the word. The program `increment`
adds one to a binary word stored with its least significant bit first. Each of these four programs
has the derived bound `2 * input.length + 2` head moves. For increment, the proof bounds the carry
length by the input length; the other three reuse their exact head-move counts.

Each `Computes` proof applies to every input word and any starting control state, head coordinate,
and recorded tape history satisfying the input-tape assumption. It states the output word,
preserves the control state, restores the head coordinate, and bounds the number of head moves.
The `Computer` definitions bundle each of the seven programs with its proof. The four
`PolyTimeComputable` definitions additionally provide polynomial-time witnesses for appending,
complementing, erasing, and incrementing. Time here counts head moves; tests and writes also
consume interpreter fuel.

These witnesses use `TMQuery.PolyTimeComputable` from
[PolytimeBasicClasses.lean](Algolean/Complexity/PolytimeBasicClasses.html). The conversions in
[Functions.lean](Algolean/Models/SingleTapeTM/Composition/Functions.html) connect the reusable
program proofs here to that definition. A witness can therefore be used directly in proofs
about the language classes `P` and `NP` defined in `PolytimeBasicClasses.lean`.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
The identity program computes the unchanged input word for every initial state. It preserves the
head coordinate and control state and uses zero head moves.
-/
theorem identity_computes : Computes (identity tm) id (fun _ => 0) := by
  intro input s hs
  exact ⟨0, by simpa [hs] using identity_correct s, le_rfl⟩

/--
Writing `bit` at the beginning of an input produces `bit :: input.tail`, replacing the first bit or
creating a one-bit output when the input is empty. The head and control state are preserved, and the
program uses zero head moves.
-/
theorem writeBit_computes (bit : Bool) :
    Computes (writeBit tm bit) (fun bits => bit :: bits.tail) (fun _ => 0) := by
  intro input s hs
  refine ⟨0, ?_, le_rfl⟩
  have htape : s.config.BiTape = cursor [] input := by simpa [cursor_start] using hs
  have hr : Runs (writeBit tm bit) s (cursor [] (bit :: input.tail)) s.headPos 0 := by
    simpa [htape, cursor_write_any] using writeBit_correct s bit
  simpa only [cursor_start] using hr

/--
`flipFirst bits` is a pure Lean function that describes the result of negating just the first input
bit and keeping the remaining bits unchanged. It returns the empty word when the input is empty.
-/
def flipFirst : List Bool → List Bool
  | [] => []
  | bit :: bits => bit.not :: bits

/--
The single-cell flipping program computes `flipFirst` on every input word. It leaves an empty input
empty, preserves the head coordinate and control state, and uses zero head moves.
-/
theorem flipBit_computes : Computes (flipBit tm) flipFirst (fun _ => 0) := by
  intro input s hs
  refine ⟨0, ?_, le_rfl⟩
  cases input with
  | nil => simpa [hs, flipFirst, BiTape.mk₁, BiTape.nil, BiTape.write] using flipBit_correct s
  | cons bit bits =>
    have htape : s.config.BiTape = cursor [] (bit :: bits) := by simpa [cursor_start] using hs
    have hr : Runs (flipBit tm) s (cursor [] (bit.not :: bits)) s.headPos 0 := by
      simpa [htape] using flipBit_correct s
    simpa [flipFirst, cursor_start] using hr

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

/--
This value contains a verified Turing machine program that leaves the entire input word unchanged
and keeps the head at its starting coordinate. It packages the identity program with its proof that
no head moves are needed.
-/
def identityComputer : Computer tm id (fun _ => 0) :=
  Computer.ofComputes (identity_computes (tm := tm))

/--
This value contains a verified Turing machine program that replaces the first input bit with `bit`,
or writes `bit` as a one-symbol output on empty input. It packages the write program with a proof
that it preserves the head coordinate and control state and uses zero head moves.
-/
def writeBitComputer (bit : Bool) :
    Computer tm (fun bits => bit :: bits.tail) (fun _ => 0) :=
  Computer.ofComputes (writeBit_computes (tm := tm) bit)

/--
This value contains a verified Turing machine program that negates the first input bit and preserves
the remaining word. It leaves empty input empty and packages the flipping program with its proof
that no head moves are needed.
-/
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
