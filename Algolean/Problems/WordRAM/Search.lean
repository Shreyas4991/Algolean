/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Search
public import Algolean.Problems.WordRAM.Solves

/-!
# WordRAM search representations

Cell zero holds the array length; cells one through that length hold its elements. A designated
register holds the key. Scratch registers, flags, and all other memory cells are unconstrained.
The header and payload fit precisely when the length is strictly less than `2 ^ w`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- A size-prefixed array and its key in physical machine state. -/
structure RepresentsSizedSearchInput (input : Search.Input (Word w)) (key : Register k)
    (s : RAMState w k) : Prop where
  fits : input.data.size < 2 ^ w
  header : s.Memory 0 = BitVec.ofNat w input.data.size
  read : ∀ i (hi : i < input.data.size), s.Memory (BitVec.ofNat w (i + 1)) = input.data[i]
  key_eq : s.Registers key = input.key

/-- Canonical memory for a size-prefixed array; background memory is zero. -/
def sizedArrayMemory (input : Array (Word w)) : Memory w := fun addr =>
  if addr = 0 then BitVec.ofNat w input.size else input[addr.toNat - 1]?.getD 0

/-- Initialize a represented search input. The program initializes its own scratch registers. -/
def linearSearchState (input : Array (Word w)) (target : Word w) (key : Register k) :
    RAMState w k :=
  ⟨sizedArrayMemory input, fun r => if r = key then target else 0, fun _ => false⟩

theorem linearSearchState_represents (input : Array (Word w)) (target : Word w)
    (key : Register k) (hfits : input.size < 2 ^ w) :
    RepresentsSizedSearchInput ⟨input, target⟩ key (linearSearchState input target key) := by
  refine ⟨hfits, by simp [linearSearchState, sizedArrayMemory], ?_, ?_⟩
  · intro i hi
    change i < input.size at hi
    have hiw : i + 1 < 2 ^ w := by lia
    have ha : (BitVec.ofNat w (i + 1)).toNat = i + 1 := Nat.mod_eq_of_lt hiw
    have hz : BitVec.ofNat w (i + 1) ≠ 0 := by grind
    simp only [linearSearchState, sizedArrayMemory, hz, ↓reduceIte, ha, Nat.add_sub_cancel,
      Array.getElem?_eq_getElem hi, Option.getD_some]
  · simp [linearSearchState]

/-- Decode the flag and zero-based index outside the running program. -/
def searchOutput (index : Register k) (s : RAMState w k) : Option Nat :=
  if s.Flags .eq then some (s.Registers index).toNat else none

/-- The external decoder observes the specified output. -/
def RepresentsSearchOutput (index : Register k) (output : Option Nat) (s : RAMState w k) : Prop :=
  searchOutput index s = output

/-- All input cells, including the size header and any unread payload cells. -/
def sizedInputRegion (input : Array (Word w)) : Finset (Word w) :=
  (Finset.range (input.size + 1)).image (BitVec.ofNat w)

/-- The size header always belongs to the input region. -/
@[simp, grind .] theorem zero_mem_sizedInputRegion (input : Array (Word w)) :
    BitVec.ofNat w 0 ∈ sizedInputRegion input :=
  Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos _), rfl⟩

theorem sizedInputRegion_card (input : Array (Word w)) (hfits : input.size < 2 ^ w) :
    (sizedInputRegion input).card = input.size + 1 := by
  rw [sizedInputRegion, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < 2 ^ w := by simp only [Finset.mem_coe, Finset.mem_range] at ha; lia
  have hb' : b < 2 ^ w := by simp only [Finset.mem_coe, Finset.mem_range] at hb; lia
  have := congrArg BitVec.toNat hab
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] using this

end Algolean.Algorithms.WordRAM
