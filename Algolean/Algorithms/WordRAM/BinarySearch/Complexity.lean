/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.BinarySearch.Common
import all Algolean.Algorithms.WordRAM.BinarySearch.Common

/-!
# Time and space used by binary search

The execution bounds assume that the initial state satisfies
`RepresentsBoundedSearchInput` and execution finishes. The array need not be sorted.
Let `n` be the input size. Time counts charged operations.
Space counts memory cells, excluding registers.

- `binarySearch_time_le`: time is at most `binarySearchTime n`, which is
  `2` for empty input and `8 * n.log2 + 11` otherwise.
- `binarySearch_addresses_subset`: every accessed cell belongs to the input array.
- `binarySearch_auxiliarySpace`: no memory outside the input array is used.
- `binarySearch_totalSpace`: total space is `n`, including unread input cells.
- `binarySearch_runsWithin`: the program terminates on every valid input state,
  and every completed execution meets the time bound and uses no auxiliary memory.
- `binarySearch_worstCase`: for `0 < w` and `n ≤ 2 ^ w`, searching for `1` in
  an array of `n` zeros takes exactly `binarySearchTime n`.
- `binarySearch_exists_worstCase`: for `0 < w` and `n ≤ 2 ^ w`, there is a sorted
  array of size `n` and an absent key for which execution takes exactly
  `binarySearchTime n`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

open BinarySearch

attribute [local simp] lower upper middle value key one CmpOp.eval BinOp.eval wordAddress_toNat

/-- The logarithmic time bound does not require sortedness. -/
theorem binarySearch_time_le (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.time ≤ binarySearchTime input.data.size :=
  (binarySearch_run_spec input s hinput hrun).right.right.right

/-- All memory probes belong to the input array. -/
theorem binarySearch_addresses_subset (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.addresses ⊆ inputRegion input.data :=
  (binarySearch_run_spec input s hinput hrun).right.right.left

/-- The six registers use no auxiliary memory cells. -/
theorem binarySearch_auxiliarySpace (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.auxiliarySpace (inputRegion input.data) = 0 := by
  simp only [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr
    (binarySearch_addresses_subset input s hinput hrun), Finset.card_empty]

/-- The total footprint equals the input size, including unread input cells. -/
theorem binarySearch_totalSpace (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.totalSpace (inputRegion input.data) = input.data.size := by
  simp only [RAMCost.totalSpace, Finset.union_eq_right.mpr
    (binarySearch_addresses_subset input s hinput hrun), inputRegion_card input.data hinput.fits]

/-- Termination, the worst-case time bound, and zero auxiliary memory for every represented
input. Resource guarantees do not require sortedness. -/
theorem binarySearch_runsWithin (w : Nat) :
    let repInput := fun input => RepresentsBoundedSearchInput input key upper
    let bound := fun (input : Search.Input (Word w)) (cost : RAMCost w 6) =>
      cost.time ≤ binarySearchTime input.data.size ∧
        cost.auxiliarySpace (inputRegion input.data) = 0
    Search.RunsWithin (binarySearch w) Executes repInput bound := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s _ hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨binarySearch_time_le input s hi hr, binarySearch_auxiliarySpace input s hi hr⟩

/-- Zeros searched for one attain the time bound at every fitting length and positive width. -/
theorem binarySearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    let input := Array.replicate n (0 : Word w)
    let s := binarySearchState input 1
    ∃ fuel cost t, execute fuel (binarySearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) ∧
      cost.time = binarySearchTime n := by
  let input := Array.replicate n (0 : Word w)
  have hrep := binarySearchState_represents input 1 (by simpa [input] using hn)
  obtain ⟨cost, t, hc, hs⟩ := search_spec ⟨input, 1⟩ _ hrep
  obtain ⟨fuel, hf⟩ := hc.execute
  refine ⟨fuel, cost, t, hf, ?_⟩
  simpa [input] using hs.worst hw (arrayMemory_replicate_zero n)
    (by simp [binarySearchState])

/-- Every fitting length has a sorted worst-case input for this same uniform program. -/
theorem binarySearch_exists_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ∃ (input : Array (Word w)) (target : Word w),
      input.size = n ∧ input.size ≤ 2 ^ w ∧ SortedWords input ∧ target ∉ input ∧
      ∃ fuel cost t,
        execute fuel (binarySearch w) (binarySearchState input target) =
          some (⟨(), cost⟩, ⟨t, 0⟩) ∧ cost.time = binarySearchTime n := by
  refine ⟨Array.replicate n 0, 1, by simp, by simpa using hn, ?_, ?_, ?_⟩
  · simp [SortedWords, Search.SortedBy]
  · simp [ne_of_gt hw]
  · exact binarySearch_worstCase w n hw hn

end Algolean.Algorithms.WordRAM
