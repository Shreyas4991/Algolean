/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic

/-!
# Abstract array search problems

Search inputs pair an array with a key. Outputs are natural indices, or `none` for absence.
`linearSearch` requires the first match; `binarySearch` requires sorted input and permits any
match. These specifications do not mention word widths, registers, memory, or programs.
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
