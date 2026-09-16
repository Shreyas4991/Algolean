/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.BinarySearch.Common
import all Algolean.Algorithms.WordRAM.BinarySearch.Common

/-!
# Correctness for word-RAM binary search
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

open BinarySearch

attribute [local simp] lower upper middle value key one CmpOp.eval BinOp.eval wordAddress_toNat

/-- Binary search terminates on every representing state, even without sortedness. -/
theorem binarySearch_terminates (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) :
    ∃ fuel cost t, execute fuel (binarySearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) := by
  obtain ⟨cost, t, hc, _⟩ := search_spec input s hinput
  obtain ⟨fuel, hf⟩ := hc.execute
  exact ⟨fuel, cost, t, hf⟩

/-- On sorted input, binary search implements the abstract search problem. -/
theorem binarySearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    let problem := Search.binarySearch (fun a b : Word w => a.toNat ≤ b.toNat)
    problem.admissible input → problem.spec input (searchOutput middle final.ram) := by
  simpa using (binarySearch_run_spec input s hinput hrun).left

/-- A cleared equality flag characterizes absence on sorted input. -/
theorem binarySearch_none_iff (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) (hsorted : SortedWords input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    final.ram.Flags .eq = false ↔ input.key ∉ input.data := by
  simpa [searchOutput] using Search.search_none_iff
    (binarySearch_correct_of_execute input s hinput hrun (by simpa using hsorted))

/-- The middle register holds an in-bounds matching address when equality is set. -/
theorem binarySearch_of_some (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) (hsorted : SortedWords input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final))
    (hfound : final.ram.Flags .eq = true) :
    let i := (final.ram.Registers middle).toNat
    i < input.data.size ∧ input.data[i]? = some input.key := by
  simpa only [Search.binarySearch_spec, searchOutput_of_found middle _ hfound,
    Search.search_spec_some, Search.IsMatch] using
    binarySearch_correct_of_execute input s hinput hrun (by simpa using hsorted)

/-- Binary search preserves every memory cell. -/
theorem binarySearch_memory (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    final.ram.Memory = s.Memory := (binarySearch_run_spec input s hinput hrun).right.left

/-- Total correctness of this fixed, runtime-size-independent program on every representing
state. The output remains in the machine's registers and flags. -/
theorem binarySearch_correct (w : Nat) :
    let problem := (Search.binarySearch (fun a b : Word w => a.toNat ≤ b.toNat))
    let repInput := fun input => RepresentsBoundedSearchInput input key upper
    problem.Solves (binarySearch w) Executes repInput (RepresentsSearchOutput middle) := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s ha hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨searchOutput middle t, representsSearchOutput_searchOutput middle t,
      binarySearch_correct_of_execute input s hi hr ha⟩

end Algolean.Algorithms.WordRAM
