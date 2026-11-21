/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Classes.DSPACE

/-!
# Boundary cases for single-tape resource classes

Leaving the input unchanged takes zero Query moves and decides equality with a fixed acceptance
word. In contrast, even a program that never moves must account for the entire input in space.
Thus `DTIME 0` contains singleton languages while `DSPACE 0` is empty under total-space accounting.
-/

@[expose] public section

namespace AlgoleanTests.ResourceBounds

open Algolean.Algorithms TMQuery

/-- The existing identity program decides any singleton with no charged head moves. -/
theorem singleton_mem_DTIME_zero (word : List Bool) :
    {word} ∈ DTIME (fun _ => 0) := by
  refine ⟨id, word, ⟨TimeComputable.id, 0, ?_⟩, fun _ => Iff.rfl⟩
  intro n
  simp [TimeComputable.id]

/-- No fixed constant bounds the total input-bearing tape over all input lengths. -/
theorem DSPACE_zero_eq_empty : DSPACE (Symbol := Bool) (fun _ => 0) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro _ ⟨_, _, ⟨computer, C, hbound⟩, _⟩
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  have hinput := computer.computesWithinSpace.space_lower_bound (List.replicate (C + 1) true)
  simp only [List.length_replicate] at hinput
  have hspace := hbound (C + 1)
  simp only [Nat.mul_zero, zero_add] at hspace
  have := (Nat.le_max_right 1 (C + 1)).trans (hinput.trans hspace)
  lia

end AlgoleanTests.ResourceBounds
