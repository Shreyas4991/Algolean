/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-! # Array layout and address lemmas for word-RAM algorithms -/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Lay out an array in consecutive RAM cells starting at address zero, with zero elsewhere.
This specifies the initial memory supplied to the interpreter; it is not part of the search cost. -/
def arrayMemory (input : Array (BitVec w)) : Memory w :=
  fun addr => input[addr.toNat]?.getD 0

/-- An index within the address space survives conversion to a word without wrapping. -/
@[grind =]
theorem wordAddress_toNat (i : Nat) (hi : i < 2 ^ w) :
    (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt hi

@[simp, grind =]
theorem arrayMemory_ofNat (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w)
    (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

@[simp, grind =]
theorem wordAddress_succ (i : Nat) :
    BitVec.ofNat w i + 1#w = BitVec.ofNat w (i + 1) := by
  simp [BitVec.ofNat_add]

/-- Addresses occupied by the input array, including cells not visited by an early return. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

/-- Every valid array index belongs to the input's memory region. -/
@[simp, grind ←]
theorem ofNat_mem_inputRegion (input : Array (BitVec w)) (i : Nat) (hi : i < input.size) :
    BitVec.ofNat w i ∈ inputRegion input :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- Under the size bound, the input occupies exactly one cell per array element. -/
theorem inputRegion_card (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w) :
    (inputRegion input).card = input.size := by
  unfold inputRegion
  rw [Finset.card_image_of_injOn (by
    intro i hi j hj heq
    have := congrArg BitVec.toNat heq
    grind), Finset.card_range]

end Algolean.Algorithms.WordRAM
