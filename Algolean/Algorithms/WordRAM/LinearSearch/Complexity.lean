/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Common
import all Algolean.Algorithms.WordRAM.LinearSearch.Common
public import Algolean.Algorithms.WordRAM.LinearSearch.Correctness

/-!
# Time and space used by linear search

The execution bounds assume that the initial state satisfies
`RepresentsBoundedSearchInput` and execution finishes. Let `n` be the input size.
Time counts charged operations. Space counts memory cells, excluding registers.

- `linearSearch_time`: the exact time is `linearSearchCost n` applied to the
  decoded output.
- `linearSearch_time_le`: time is at most `linearSearchTime n`, which is
  `3` for empty input and `4 * n + 3` otherwise.
- `linearSearch_time_of_not_mem`: an absent key takes exactly `linearSearchTime n`.
- `linearSearch_time_of_some`: finding the first match at index `i` takes
  exactly `4 * i + 6` operations.
- `linearSearch_addresses_subset`: every accessed cell belongs to the input array.
- `linearSearch_auxiliarySpace`: no memory outside the input array is used.
- `linearSearch_totalSpace`: total space is `n`, including unread input cells.
- `linearSearch_runsWithin`: the program terminates on every valid input state,
  and every completed execution meets the time bound and uses no auxiliary memory.
- `linearSearch_worstCase`: for `0 < w` and `n ≤ 2 ^ w`, searching for `1` in
  an array of `n` zeros takes exactly `linearSearchTime n`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

open LinearSearch

attribute [local simp] index key value one last CmpOp.eval BinOp.eval wordAddress_toNat

/-- The exact time depends on the first match, or on the length when the key is absent. -/
theorem linearSearch_time (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time = linearSearchCost input.data.size (searchOutput index final.ram) :=
  (linearSearch_run_spec input s hinput hrun).right.right.right

/-- At most four primitive operations per unsuccessful cell, plus setup and exit costs. -/
theorem linearSearch_time_le (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time ≤ linearSearchTime input.data.size := by
  have hs := linearSearch_correct_of_execute input s hinput hrun
  rw [linearSearch_time input s hinput hrun]
  cases ho : searchOutput index final.ram with
  | none => exact Nat.le_refl _
  | some i =>
    simp only [ho, Search.linearSearch_spec_some, Search.IsFirstMatch] at hs
    simp only [linearSearchCost, linearSearchTime, if_neg (by lia : input.data.size ≠ 0)]
    lia

/-- An absent key attains the length-dependent upper bound. -/
theorem linearSearch_time_of_not_mem (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s) (hnot : input.key ∉ input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time = linearSearchTime input.data.size := by
  have hf := (linearSearch_none_iff input s hinput hrun).mpr hnot
  simpa [hf, linearSearchCost] using linearSearch_time input s hinput hrun

/-- A first match at index `i` costs exactly `4 * i + 6`. -/
theorem linearSearch_time_of_some (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final))
    (hfound : final.ram.Flags .eq = true) :
    result.tell.time = 4 * (final.ram.Registers index).toNat + 6 := by
  simpa [hfound, linearSearchCost] using linearSearch_time input s hinput hrun

/-- Every probed address belongs to the input array. -/
theorem linearSearch_addresses_subset (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.addresses ⊆ inputRegion input.data :=
  (linearSearch_run_spec input s hinput hrun).right.right.left

/-- Only input memory is probed; registers do not count as auxiliary memory. -/
theorem linearSearch_auxiliarySpace (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.auxiliarySpace (inputRegion input.data) = 0 := by
  simp only [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr
    (linearSearch_addresses_subset input s hinput hrun), Finset.card_empty]

/-- Total memory is exactly the input footprint, including any unread input cells. -/
theorem linearSearch_totalSpace (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.totalSpace (inputRegion input.data) = input.data.size := by
  simp only [RAMCost.totalSpace, Finset.union_eq_right.mpr
    (linearSearch_addresses_subset input s hinput hrun), inputRegion_card input.data hinput.fits]

/-- Termination, the worst-case time bound, and zero auxiliary memory for every represented
input. Resource guarantees do not require sortedness. -/
theorem linearSearch_runsWithin (w : Nat) :
    let repInput := fun input => RepresentsBoundedSearchInput input key last
    let bound := fun (input : Search.Input (Word w)) (cost : RAMCost w 5) =>
      cost.time ≤ linearSearchTime input.data.size ∧
        cost.auxiliarySpace (inputRegion input.data) = 0
    Search.RunsWithin (linearSearch w) Executes repInput bound := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s _ hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨linearSearch_time_le input s hi hr, linearSearch_auxiliarySpace input s hi hr⟩

/-- Every fitting length has a worst-case instance at positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    let input := Array.replicate n (0 : Word w)
    let s := linearSearchState input 1
    ∃ fuel cost t, execute fuel (linearSearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) ∧
      cost.time = linearSearchTime n := by
  let input := Array.replicate n (0 : Word w)
  have hrep := linearSearchState_represents input 1 (by simpa [input] using hn)
  obtain ⟨fuel, cost, t, hr⟩ := linearSearch_terminates ⟨input, 1⟩ _ hrep
  refine ⟨fuel, cost, t, hr, ?_⟩
  simpa [input] using linearSearch_time_of_not_mem ⟨input, 1⟩ _ hrep
    (by simp [input, ne_of_gt hw]) hr

end Algolean.Algorithms.WordRAM
