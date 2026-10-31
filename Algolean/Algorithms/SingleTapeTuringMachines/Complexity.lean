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
# Uniform computation and complexity bounds for Boolean tape procedures

The same programs work on all inputs and on arbitrary initial control states, head origins,
and allocated tape histories. `Computes.space` derives the corresponding additional-space bound;
the initially allocated tape is retained. The polynomial witnesses use the deeply embedded model.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Identity is a reusable zero-move computation. -/
theorem identity_computes : Computes (identity tm) id (fun _ => 0) := by
  intro input s hs
  exact ⟨0, by simpa [hs] using identity_correct s, le_rfl⟩

/-- A fixed bit write replaces the first cell, including when the input is empty. -/
theorem writeBit_computes (bit : Bool) :
    Computes (writeBit tm bit) (fun bits => bit :: bits.tail) (fun _ => 0) := by
  intro input s hs
  refine ⟨0, ?_, le_rfl⟩
  have htape : s.config.BiTape = cursor [] input := by simpa [cursor_start] using hs
  have hr : Runs (writeBit tm bit) s (cursor [] (bit :: input.tail)) s.headPos 0 := by
    simpa [htape, cursor_write_any] using writeBit_correct s bit
  simpa only [cursor_start] using hr

/-- Specification of negating only the first bit, leaving an empty input empty. -/
def flipFirst : List Bool → List Bool
  | [] => []
  | bit :: bits => bit.not :: bits

/-- Single-cell complementation is a reusable zero-move computation. -/
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

/-- Appending a constant bit has exact time `2n + 2` on every input. -/
theorem appendBit_computes (bit : Bool) :
    Computes (appendBit tm bit) (fun bits => bits ++ [bit]) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [cursor_start] using appendBit_correct input bit s (by simpa [cursor_start] using hs)

/-- Complementing a block has exact time `2n + 2`, independently of its bit values. -/
theorem complementBlock_computes :
    Computes (complementBlock tm) (List.map Bool.not) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [cursor_start] using complementBlock_correct input s (by simpa [cursor_start] using hs)

/-- Erasing a block has exact time `2n + 2` and produces the empty word. -/
theorem eraseBlock_computes :
    Computes (eraseBlock tm) (fun _ => []) (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * input.length + 2, ?_, le_rfl⟩
  simpa [BiTape.mk₁] using eraseBlock_correct input s (by simpa [cursor_start] using hs)

/-- Binary increment is bounded by `2n + 2`, including carry propagation and head restoration. -/
theorem increment_computes :
    Computes (increment tm) incrementBits (fun bits => 2 * bits.length + 2) := by
  intro input s hs
  refine ⟨2 * carryCount input + 2, ?_, ?_⟩
  · simpa [cursor_start] using increment_correct input s (by simpa [cursor_start] using hs)
  · have := carryCount_le_length input
    lia

/-- Verified identity machine, with no head moves. -/
def identityComputer : Computer tm id (fun _ => 0) :=
  Computer.ofComputes (identity_computes (tm := tm))

/-- Verified fixed-bit write machine. -/
def writeBitComputer (bit : Bool) :
    Computer tm (fun bits => bit :: bits.tail) (fun _ => 0) :=
  Computer.ofComputes (writeBit_computes (tm := tm) bit)

/-- Verified first-bit complementation machine. -/
def flipBitComputer : Computer tm flipFirst (fun _ => 0) :=
  Computer.ofComputes (flipBit_computes (tm := tm))

/-- Verified append machine, ready for composition with other word transformations. -/
def appendBitComputer (bit : Bool) :
    Computer tm (fun bits => bits ++ [bit]) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (appendBit_computes (tm := tm) bit)

/-- Verified block complementation machine. -/
def complementBlockComputer :
    Computer tm (List.map Bool.not) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (complementBlock_computes (tm := tm))

/-- Verified erasing machine. -/
def eraseBlockComputer : Computer tm (fun _ => []) (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (eraseBlock_computes (tm := tm))

/-- Verified binary successor machine, including carry overflow. -/
def incrementComputer : Computer tm incrementBits (fun bits => 2 * bits.length + 2) :=
  Computer.ofComputes (increment_computes (tm := tm))

/-- A polynomial-time witness for appending a fixed bit, using exactly the proved query program. -/
noncomputable def appendBitPolyTimeComputable (bit : Bool) :
    TMQuery.PolyTimeComputable (fun bits => bits ++ [bit]) :=
  Computes.polyTimeComputable (p := appendBit tm bit) (poly := 2 * X + 2)
    (by simpa using appendBit_computes (tm := tm) bit)

/-- A polynomial-time witness for Boolean block complementation. -/
noncomputable def complementBlockPolyTimeComputable :
    TMQuery.PolyTimeComputable (List.map Bool.not) :=
  Computes.polyTimeComputable (p := complementBlock tm) (poly := 2 * X + 2)
    (by simpa using complementBlock_computes (tm := tm))

/-- A polynomial-time witness for erasing a Boolean block. -/
noncomputable def eraseBlockPolyTimeComputable :
    TMQuery.PolyTimeComputable (fun _ : List Bool => []) :=
  Computes.polyTimeComputable (p := eraseBlock tm) (poly := 2 * X + 2)
    (by simpa using eraseBlock_computes (tm := tm))

/-- A polynomial-time witness for binary successor on the Boolean tape alphabet. -/
noncomputable def incrementPolyTimeComputable : TMQuery.PolyTimeComputable incrementBits :=
  Computes.polyTimeComputable (p := increment tm) (poly := 2 * X + 2)
    (by simpa using increment_computes (tm := tm))

end Algolean.Algorithms.SingleTapeTuringMachines
