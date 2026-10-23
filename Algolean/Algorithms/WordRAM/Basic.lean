/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM
public import Algolean.Problems.Search

/-!
# Supporting definitions for WordRAM search algorithms

Search representations, the linear-search input layout and state constructor, output decoding,
and input memory regions are defined together in `Algolean.Problems.Search`.

This file supplies the bounds and initial memory layout used by binary search, word-address
arithmetic, sorted-array lemmas, and `Executes`, the completed-execution relation used by
both algorithms' correctness and complexity proofs.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- The abstract sortedness relation instantiated with unsigned word order. -/
abbrev SortedWords (input : Array (Word w)) : Prop :=
  Search.SortedBy (fun a b => a.toNat ≤ b.toNat) input

/-- Search inputs constrain the array and key register, not scratch registers or flags. -/
structure RepresentsSearchInput (input : Search.Input (Word w)) (key : Register k)
    (s : RAMState w k) : Prop extends RepresentsArray input.data s.Memory where
  /-- The designated register contains the abstract key. -/
  key_eq : s.Registers key = input.key

/-- Runtime bounds for a search: an inclusive last address and a nonempty flag.
This represents empty arrays and all `2^w` cells, even when `w = 0`. -/
structure RepresentsBoundedSearchInput (input : Search.Input (Word w))
    (key last : Register k) (s : RAMState w k) : Prop
    extends RepresentsSearchInput input key s where
  /-- Last input address; ignored for an empty input. -/
  last_eq : s.Registers last = BitVec.ofNat w (input.data.size - 1)
  /-- The initial less-than flag indicates whether there is an interval to search. -/
  nonempty_eq : s.Flags .ult = decide (input.data.size ≠ 0)

/-- Array layout used by the initial machine state. -/
def arrayMemory (input : Array (BitVec w)) : Memory w :=
  fun addr => input[addr.toNat]?.getD 0

@[grind =] theorem wordAddress_toNat (i : Nat) (hi : i < 2 ^ w) :
    (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt hi

@[simp, grind =] theorem arrayMemory_ofNat (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

/-- If the array fits in memory, `arrayMemory` stores each element at its index. -/
@[simp] theorem arrayMemory_represents (input : Array (Word w)) (hfits : input.size ≤ 2 ^ w) :
    RepresentsArray input (arrayMemory input) :=
  ⟨hfits, fun i hi => arrayMemory_ofNat input hfits i hi⟩

@[grind =] theorem wordAddress_succ (i : Nat) :
    BitVec.ofNat w i + 1 = BitVec.ofNat w (i + 1) := (BitVec.ofNat_add i 1).symm

/-- In a sorted word array, words at or before a value below the key cannot match it. -/
@[grind →] theorem SortedWords.exclude_left {input : Array (Word w)} (h : SortedWords input)
    {target : Word w} {pivot : Nat} (hp : pivot < input.size)
    (hlt : input[pivot].toNat < target.toNat) (i : Nat) (hi : i ≤ pivot) :
    input[i]? ≠ some target := by
  have hib : i < input.size := by lia
  have hs := h i pivot hib hp hi
  intro heq
  have heq' : input[i] = target := by simpa [hib] using heq
  rw [heq'] at hs
  lia

/-- In a sorted word array, words at or after a value above the key cannot match it. -/
@[grind →] theorem SortedWords.exclude_right {input : Array (Word w)} (h : SortedWords input)
    {target : Word w} {pivot : Nat} (hp : pivot < input.size)
    (hlt : target.toNat < input[pivot].toNat) (i : Nat) (hi : pivot ≤ i)
    (hib : i < input.size) : input[i]? ≠ some target := by
  have hs := h pivot i hp hib hi
  intro heq
  have heq' : input[i] = target := by simpa [hib] using heq
  rw [heq'] at hs
  lia

/-- Subtracting one converts a positive address to the preceding index without wrapping. -/
theorem word_pred_toNat (x : BitVec w) (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have h := BitVec.ofNat_sub_ofNat_of_le (w := w) x.toNat 1 (by have := x.isLt; lia) hx
  have h' := congrArg BitVec.toNat h
  simpa [Nat.mod_eq_of_lt (show x.toNat - 1 < 2 ^ w by have := x.isLt; lia)] using h'

/-- Completed execution in the time-and-space model, hiding interpreter fuel.
Unused fuel is allowed and is not charged as time. -/
def Executes (program : Prog (WordRAM w k) Unit) (s : RAMState w k)
    (cost : RAMCost w k) (t : RAMState w k) : Prop :=
  ∃ fuel remaining, execute fuel program s = some (⟨(), cost⟩, ⟨t, remaining⟩)

/-- If a program's instructions finish with the stated cost and final state,
the program satisfies `Executes` with that same cost and state. -/
theorem Completes.executes {program : Prog (WordRAM w k) Unit}
    (h : Completes (instructions program) s cost t) : Executes program s cost t := by
  obtain ⟨fuel, hr⟩ := h.execute
  exact ⟨fuel, 0, hr⟩

end Algolean.Algorithms.WordRAM
