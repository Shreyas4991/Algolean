/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Common
import all Algolean.Algorithms.WordRAM.LinearSearch.Common

/-!
# Correctness for word-RAM linear search
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

open LinearSearch

attribute [local simp] index key value one last CmpOp.eval BinOp.eval wordAddress_toNat

/-- Every representing input state has sufficient interpreter fuel for termination. -/
theorem linearSearch_terminates (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s) :
    ∃ fuel cost t, execute fuel (linearSearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) := by
  obtain ⟨cost, t, hc, _⟩ := search_spec input s hinput
  obtain ⟨fuel, hf⟩ := hc.execute
  exact ⟨fuel, cost, t, hf⟩

/-- Uniform linear search returns the first match, or certifies absence. -/
theorem linearSearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    Search.linearSearch.spec input (searchOutput index final.ram) :=
  (linearSearch_run_spec input s hinput hrun).left

/-- The equality flag is clear exactly when the key is absent. -/
theorem linearSearch_none_iff (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Flags .eq = false ↔ input.key ∉ input.data := by
  have h := linearSearch_correct_of_execute input s hinput hrun
  simpa [searchOutput] using Search.search_none_iff (Search.linearSearch_spec_search _ _ h)

/-- A set equality flag identifies the first matching address. -/
theorem linearSearch_some_iff (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Flags .eq = true ↔
      Search.IsFirstMatch input.data input.key (final.ram.Registers index).toNat := by
  simpa [searchOutput] using Search.linearSearch_some_iff
    (linearSearch_correct_of_execute input s hinput hrun) (final.ram.Registers index).toNat

/-- Loads and register operations preserve the entire input and background memory. -/
theorem linearSearch_memory (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Memory = s.Memory := (linearSearch_run_spec input s hinput hrun).right.left

/-- Total correctness of this fixed, runtime-size-independent program on every representing
state. The output remains in the machine's registers and flags. -/
theorem linearSearch_correct (w : Nat) :
    let problem := Search.linearSearch
    let repInput := fun input => RepresentsBoundedSearchInput input key last
    problem.Solves (linearSearch w) Executes repInput (RepresentsSearchOutput index) := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s ha hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨searchOutput index t, representsSearchOutput_searchOutput index t,
      linearSearch_correct_of_execute input s hi hr⟩

end Algolean.Algorithms.WordRAM
