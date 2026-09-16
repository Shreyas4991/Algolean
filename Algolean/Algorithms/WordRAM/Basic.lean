/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM
public import Algolean.Problems.Search

/-!
# Arrays and search results in word-RAM states

- `RepresentsArray`: the array fits in memory and occupies consecutive cells starting at zero.
- `RepresentsSearchInput`: also specifies the register holding the search key.
- `RepresentsBoundedSearchInput`: also specifies the last array address and a flag
  indicating whether the array is nonempty.
- `RepresentsSizedSearchInput`: stores the size in cell zero, the array after it,
  and the key in a register. Other registers and flags are unconstrained.
- `sizedArrayMemory` and `sizedInputRegion`: memory and input cells for this layout.
- `searchOutput`: reads an optional result index from a register and the equality flag.
- `RepresentsSearchOutput`: specifies how an optional result index is stored.
- `arrayMemory`: stores the array in memory and fills the remaining cells with zero.
- `inputRegion`: the set of cells occupied by the array.
- `Executes`: the program finishes with the stated cost and final state for some fuel amount.

The lemmas show how to read array elements through word addresses, count input cells,
and rule out parts of a sorted array during binary search.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- The abstract sortedness relation instantiated with unsigned word order. -/
abbrev SortedWords (input : Array (Word w)) : Prop :=
  Search.SortedBy (fun a b => a.toNat ≤ b.toNat) input

/-- An array occupies cells `0` through `size - 1`. Other cells are unconstrained. -/
structure RepresentsArray (input : Array (Word w)) (memory : Memory w) : Prop where
  /-- Every element has a distinct representable address, including a full address space. -/
  fits : input.size ≤ 2 ^ w
  /-- Only input cells have prescribed contents. -/
  read : ∀ i (hi : i < input.size), memory (BitVec.ofNat w i) = input[i]

attribute [grind →] RepresentsArray.read

/-- Reading an input cell from any representing RAM state returns the corresponding element. -/
theorem RepresentsArray.read_state {s : RAMState w k}
    (h : RepresentsArray input s.Memory)
    (i : Nat) (hi : i < input.size) : s.Memory (BitVec.ofNat w i) = input[i] := h.read i hi

/-- Every input index fits in a machine word. -/
@[grind →] theorem RepresentsArray.index_lt (h : RepresentsArray input (w := w) memory)
    (hi : i < input.size) : i < 2 ^ w := lt_of_lt_of_le hi h.fits

/-- Converting a valid input index to a word and back preserves it.
Use this lemma with a representation argument; `simp` cannot infer that argument from the LHS. -/
@[grind →] theorem RepresentsArray.address_toNat (h : RepresentsArray input (w := w) memory)
    (hi : i < input.size) : (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt (h.index_lt hi)

/-- Decode a word known to address an input element, without repeating the range proof. -/
theorem RepresentsArray.toNat_of_eq (h : RepresentsArray input (w := w) memory)
    (hi : i < input.size) {addr : Word w} (ha : addr = BitVec.ofNat w i) : addr.toNat = i :=
  ha ▸ h.address_toNat hi

/-- Read an input element through any word known to contain its index.
This is an explicit rewrite helper: `grind` uses `RepresentsArray.read` and congruence instead. -/
theorem RepresentsArray.read_of_eq (h : RepresentsArray input (w := w) memory)
    (hi : i < input.size) {addr : Word w} (ha : addr = BitVec.ofNat w i) : memory addr = input[i] :=
  ha ▸ h.read i hi

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

/-- Read the search result outside the program, for specifications and tests. -/
def searchOutput (index : Register k) (s : RAMState w k) : Option Nat :=
  if s.Flags .eq then some (s.Registers index).toNat else none

@[simp] theorem searchOutput_of_found (index : Register k) (s : RAMState w k)
    (h : s.Flags .eq = true) : searchOutput index s = some (s.Registers index).toNat := by
  simp [searchOutput, h]

@[simp] theorem searchOutput_of_not_found (index : Register k) (s : RAMState w k)
    (h : s.Flags .eq = false) : searchOutput index s = none := by
  simp [searchOutput, h]

/-- The result flag represents absence or a successful address. An absent result places no
constraint on the address register. -/
def RepresentsSearchOutput (index : Register k) (output : Option Nat) (s : RAMState w k) : Prop :=
  match output with
  | none => s.Flags .eq = false
  | some i => s.Flags .eq = true ∧ (s.Registers index).toNat = i

@[simp, grind =] theorem representsSearchOutput_iff (index : Register k)
    (output : Option Nat) (s : RAMState w k) :
    RepresentsSearchOutput index output s ↔ searchOutput index s = output := by
  cases output <;> simp [RepresentsSearchOutput, searchOutput]

/-- The external decoder always supplies a represented output. -/
theorem representsSearchOutput_searchOutput (index : Register k) (s : RAMState w k) :
    RepresentsSearchOutput index (searchOutput index s) s := by simp

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

/-- Memory cells occupied by the input array. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

@[simp, grind ←] theorem ofNat_mem_inputRegion (input : Array (BitVec w))
    (i : Nat) (hi : i < input.size) : BitVec.ofNat w i ∈ inputRegion input :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- A fitting array occupies exactly one distinct cell per element. -/
theorem inputRegion_card (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w) :
    (inputRegion input).card = input.size := by
  unfold inputRegion
  rw [Finset.card_image_of_injOn (by
    intro i hi j hj heq
    have := congrArg BitVec.toNat heq
    grind), Finset.card_range]

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

section SizedInput

/-- The size in cell zero, followed by the array elements. -/
def withSize (input : Array (Word w)) : Array (Word w) :=
  #[BitVec.ofNat w input.size] ++ input

@[simp] theorem withSize_size (input : Array (Word w)) :
    (withSize input).size = input.size + 1 := by
  simp [withSize, Nat.add_comm]

@[simp] theorem withSize_getElem_zero (input : Array (Word w)) :
    (withSize input)[0] = BitVec.ofNat w input.size := by simp [withSize]

@[simp] theorem withSize_getElem_succ (input : Array (Word w)) (i : Nat) (hi : i < input.size) :
    (withSize input)[i + 1]' (by simp; lia) = input[i] := by simp [withSize]

@[simp] theorem withSize_getElem?_succ (input : Array (Word w)) (i : Nat) :
    (withSize input)[i + 1]? = input[i]? := by
  simp [withSize, Array.getElem?_append]

/-- The input size and elements are in memory; the key is in its register.
Other registers and flags may initially contain any values. -/
structure RepresentsSizedSearchInput (input : Search.Input (Word w)) (key : Register k)
    (s : RAMState w k) : Prop extends RepresentsArray (withSize input.data) s.Memory where
  key_eq : s.Registers key = input.key

variable {input : Search.Input (Word w)} {key : Register k} {s : RAMState w k}

theorem RepresentsSizedSearchInput.header
    (h : RepresentsSizedSearchInput input key s) :
    s.Memory (BitVec.ofNat w 0) = BitVec.ofNat w input.data.size := by
  simpa using h.read 0 (by simp)

@[grind →] theorem RepresentsSizedSearchInput.size_lt
    (h : RepresentsSizedSearchInput input key s) : input.data.size < 2 ^ w := by
  have := h.fits
  simpa using this

theorem RepresentsSizedSearchInput.header_toNat
    (h : RepresentsSizedSearchInput input key s) :
    (s.Memory (BitVec.ofNat w 0)).toNat = input.data.size := by
  simpa [Word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.size_lt] using
    congrArg BitVec.toNat h.header

/-- Array layout used by the initial machine state. -/
def sizedArrayMemory (input : Array (BitVec w)) : Memory w :=
  fun addr => (withSize input)[addr.toNat]?.getD 0

@[grind =] theorem sizedArrayMemory_ofNat (input : Array (Word w))
    (hfits : input.size < 2 ^ w) (i : Nat) (hi : i < (withSize input).size) :
    sizedArrayMemory input (BitVec.ofNat w i) = (withSize input)[i] := by
  have h : i < 2 ^ w := by simp only [withSize_size] at hi; lia
  simp [sizedArrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Array.getElem?_eq_getElem hi]

/-- The memory builder stores the size header followed by every array element. -/
@[simp] theorem sizedArrayMemory_represents (input : Array (Word w)) (hfits : input.size < 2 ^ w) :
    RepresentsArray (withSize input) (sizedArrayMemory input) :=
  ⟨by simpa using hfits, fun i hi => sizedArrayMemory_ofNat input hfits i hi⟩

/-- All input cells, including the size header. -/
def sizedInputRegion (input : Array (Word w)) : Finset (Word w) := inputRegion (withSize input)

@[simp] theorem zero_mem_sizedInputRegion (input : Array (Word w)) :
    BitVec.ofNat w 0 ∈ sizedInputRegion input := by
  simp only [sizedInputRegion, inputRegion, Finset.mem_image]
  exact ⟨0, by simp, rfl⟩

@[simp] theorem sizedInputRegion_card (input : Array (Word w)) (hfits : input.size < 2 ^ w) :
    (sizedInputRegion input).card = input.size + 1 := by
  simpa [sizedInputRegion] using inputRegion_card (withSize input) (by simpa using hfits)

/-- Subtracting one converts a positive address to the preceding index without wrapping. -/
theorem word_pred_toNat (x : BitVec w) (hx : 0 < x.toNat) :
    (x - 1).toNat = x.toNat - 1 := by
  have h := BitVec.ofNat_sub_ofNat_of_le (w := w) x.toNat 1 (by have := x.isLt; lia) hx
  have h' := congrArg BitVec.toNat h
  simpa [Nat.mod_eq_of_lt (show x.toNat - 1 < 2 ^ w by have := x.isLt; lia)] using h'

end SizedInput

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
