/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Algolean.Models.WordRAM

/-!
# Array search problems

The input is an array and a key. The output is `some i` for a matching index,
or `none` when the key is absent.

- `search`: accepts any matching index.
- `linearSearch`: requires the first matching index.
- `binarySearch`: requires an array sorted by the supplied relation and accepts
  any matching index.
- `RunsWithin`: requires termination and a cost bound for every input state
  storing the array and key as specified, including unsorted arrays.

The `WordRAMLinearSearch` section collects the concrete input layout, representation
predicates, initial-state constructor and its proof, output decoding, and memory footprint.

The main lemmas describe correct answers:

- `IsFirstMatch.unique`: two first matches have the same index.
- `linearSearch_spec_search`: a correct first-match answer is a correct search answer.
- `search_none_iff`: a correct answer is `none` exactly when the key is absent.
- `linearSearch_some_iff`: a correct first-match answer is `some i` exactly when
  `i` is the first matching index.
-/

@[expose] public section

namespace Algolean.Search

/-- The data and key supplied to a search problem. -/
structure Input (α : Type u) where
  /-- Array to search. -/
  data : Array α
  /-- Value to find. -/
  key : α

/-- An in-bounds index containing the search key. -/
def IsMatch (data : Array α) (key : α) (i : Nat) : Prop :=
  i < data.size ∧ data[i]? = some key

/-- A matching index with no earlier occurrence of the key. -/
def IsFirstMatch (data : Array α) (key : α) (i : Nat) : Prop :=
  i < data.size ∧ data[i]? = some key ∧ ∀ j, j < i → data[j]? ≠ some key

/-- Nondecreasing array order for the supplied relation, allowing duplicate elements. -/
def SortedBy (le : α → α → Prop) (data : Array α) : Prop :=
  ∀ i j, (hi : i < data.size) → (hj : j < data.size) → i ≤ j → le data[i] data[j]

/-- An arbitrary matching index, or an absence certificate. -/
def search : Problem (Input α) (Option Nat) where
  admissible _ := True
  spec input
    | none => input.key ∉ input.data
    | some i => IsMatch input.data input.key i

/-- The first matching index, or an absence certificate. -/
def linearSearch : Problem (Input α) (Option Nat) where
  admissible _ := True
  spec input
    | none => input.key ∉ input.data
    | some i => IsFirstMatch input.data input.key i

/-- Search in a sorted array; any matching index is acceptable. -/
def binarySearch (le : α → α → Prop) : Problem (Input α) (Option Nat) :=
  search.restrict (fun input => SortedBy le input.data)

/-- Resource guarantees for search on all represented arrays, including unsorted arrays.
Correctness can separately use the more restrictive binary-search problem. -/
abbrev RunsWithin (program : Program) (run : Program → State → Cost → State → Prop)
    (repInput : Input α → State → Prop) (bound : Input α → Cost → Prop) : Prop :=
  search.RunsWithin program run repInput bound

@[simp] theorem search_admissible (input : Input α) : search.admissible input := trivial

@[simp] theorem linearSearch_admissible (input : Input α) :
    linearSearch.admissible input := trivial

@[simp, grind =] theorem binarySearch_admissible (le : α → α → Prop) (input : Input α) :
    (binarySearch le).admissible input ↔ SortedBy le input.data := by
  simp [binarySearch]

@[simp, grind =] theorem search_spec_none (input : Input α) :
    search.spec input none ↔ input.key ∉ input.data := Iff.rfl

@[simp, grind =] theorem search_spec_some (input : Input α) (i : Nat) :
    search.spec input (some i) ↔ IsMatch input.data input.key i := Iff.rfl

@[simp, grind =] theorem linearSearch_spec_none (input : Input α) :
    linearSearch.spec input none ↔ input.key ∉ input.data := Iff.rfl

@[simp, grind =] theorem linearSearch_spec_some (input : Input α) (i : Nat) :
    linearSearch.spec input (some i) ↔ IsFirstMatch input.data input.key i := Iff.rfl

@[simp, grind =] theorem binarySearch_spec (le : α → α → Prop) (input : Input α)
    (output : Option Nat) :
    (binarySearch le).spec input output ↔ search.spec input output := Iff.rfl

/-- First-match search refines ordinary search. -/
theorem IsFirstMatch.isMatch (h : IsFirstMatch data key i) : IsMatch data key i :=
  ⟨h.left, h.right.left⟩

/-- A successful match is a membership witness, independently of how it was found. -/
theorem IsMatch.mem (h : IsMatch data key i) : key ∈ data :=
  Array.mem_iff_getElem?.mpr ⟨i, h.right⟩

/-- Two first-match witnesses for the same input must identify the same index. -/
theorem IsFirstMatch.unique (hi : IsFirstMatch data key i) (hj : IsFirstMatch data key j) :
    i = j := by
  rcases hi with ⟨_, hi, hbeforeI⟩
  rcases hj with ⟨_, hj, hbeforeJ⟩
  rcases Nat.lt_trichotomy i j with hlt | heq | hgt
  · exact (hbeforeJ i hlt hi).elim
  · exact heq
  · exact (hbeforeI j hgt hj).elim

/-- Every answer satisfying first-match search also satisfies ordinary search. -/
theorem linearSearch_spec_search (input : Input α) (output : Option Nat)
    (h : linearSearch.spec input output) : search.spec input output := by
  cases output with
  | none => exact h
  | some i => exact IsFirstMatch.isMatch h

/-- For a correct search answer, `none` is equivalent to absence of the key. -/
theorem search_none_iff (h : search.spec input output) :
    output = none ↔ input.key ∉ input.data := by
  cases output with
  | none => exact ⟨fun _ => h, fun _ => rfl⟩
  | some i =>
    constructor
    · intro h; cases h
    · intro hnot
      exact (hnot (IsMatch.mem h)).elim

/-- A correct first-match answer identifies precisely the unique first matching index. -/
theorem linearSearch_some_iff (h : linearSearch.spec input output) (i : Nat) :
    output = some i ↔ IsFirstMatch input.data input.key i := by
  cases output with
  | none =>
    constructor
    · intro h; cases h
    · intro hfirst
      exact (h hfirst.isMatch.mem).elim
  | some j =>
    constructor
    · intro heq
      cases heq
      exact h
    · intro hfirst
      exact congrArg some (IsFirstMatch.unique h hfirst)

end Algolean.Search

namespace Algolean.Algorithms.WordRAM

section WordRAMLinearSearch

/-!
## WordRAM linear-search representation

The abstract problem above accepts any array and key. Its WordRAM representation stores
`input.data.size` in cell `0` and `input.data[i]` in cell `i + 1`. The header and payload
must fit in memory, so `input.data.size < 2 ^ w`. The key register is a parameter of the
representation and initial-state constructor, independent of the algorithm's register choices.

`RepresentsArray` describes a generic array starting at zero. Applying it to `withSize`
represents the complete header-plus-payload layout. The array and output predicates are
also used by other WordRAM search algorithms.
-/

/-- An array occupies cells `0` through `size - 1`. Other cells are unconstrained. -/
structure RepresentsArray (input : Array (Word w)) (memory : Memory w) : Prop where
  /-- Every element has a distinct representable address, including a full address space. -/
  fits : input.size ≤ 2 ^ w
  /-- Only input cells have prescribed contents. -/
  read : ∀ i (hi : i < input.size), memory (BitVec.ofNat w i) = input[i]

attribute [grind →] RepresentsArray.read

/-- The size in cell zero, followed by the array elements. -/
def withSize (input : Array (Word w)) : Array (Word w) :=
  #[BitVec.ofNat w input.size] ++ input

/-- The input size and elements are in memory; the key is in its register.
Other registers and flags may initially contain any values. -/
structure RepresentsSizedSearchInput (input : Search.Input (Word w)) (key : Register k)
    (s : RAMState w k) : Prop extends RepresentsArray (withSize input.data) s.Memory where
  key_eq : s.Registers key = input.key

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

/-- Store the size header, array, and search key in the designated register.
Other registers and flags start at zero; the algorithm initializes its working state. -/
def linearSearchState (input : Array (Word w)) (target : Word w)
    (key : Register k) : RAMState w k :=
  ⟨sizedArrayMemory input, fun r => if r = key then target else 0, fun _ => false⟩

/-- The constructed state represents the input whenever the header and payload fit in memory. -/
@[simp] theorem linearSearchState_represents (input : Array (Word w)) (target : Word w)
    (key : Register k) (hfits : input.size < 2 ^ w) :
    RepresentsSizedSearchInput ⟨input, target⟩ key (linearSearchState input target key) :=
  ⟨sizedArrayMemory_represents input hfits, by simp [linearSearchState]⟩

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

/-- All input cells, including the size header. -/
def sizedInputRegion (input : Array (Word w)) : Finset (Word w) := inputRegion (withSize input)

@[simp] theorem zero_mem_sizedInputRegion (input : Array (Word w)) :
    BitVec.ofNat w 0 ∈ sizedInputRegion input := by
  simp only [sizedInputRegion, inputRegion, Finset.mem_image]
  exact ⟨0, by simp, rfl⟩

@[simp] theorem sizedInputRegion_card (input : Array (Word w)) (hfits : input.size < 2 ^ w) :
    (sizedInputRegion input).card = input.size + 1 := by
  simpa [sizedInputRegion] using inputRegion_card (withSize input) (by simpa using hfits)

end WordRAMLinearSearch

end Algolean.Algorithms.WordRAM
