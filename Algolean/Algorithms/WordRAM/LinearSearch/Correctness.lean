/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Common

/-!
# Total correctness of WordRAM linear search

The fixed program handles every state representing the input, including arbitrary scratch
registers, stale flags, and background memory. It returns the first matching index and preserves
all memory. The correctness and resource guarantees refer to the same completed execution.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open Cslib LinearSearch

/-- A successful execution, its first-match answer, exact time, and input-only footprint. -/
theorem linearSearch_run (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) :
    ∃ output cost final, Completes (linearSearch w) s cost final ∧
      RepresentsSearchOutput index output final ∧ output ∈ Search.linearSearch input ∧
      final.Memory = s.Memory ∧
      cost.time = (match output with
        | none => 4 * input.data.size + 7
        | some i => 4 * i + 10) ∧ cost.addresses ⊆ sizedInputRegion input.data := by
  obtain ⟨t, hs, hcursor, heq, hult, hm⟩ := setup_run input s h
  have loop : ∃ output cost u, Completes (whileLoop .ult (body w)) t cost u ∧
      output ∈ Search.linearSearch input ∧ AtResult output u ∧ u.Memory = t.Memory ∧
      u.Registers one = 1 ∧
      cost.time = (match output with
        | none => 4 * input.data.size
        | some i => 4 * i + 3) ∧ cost.addresses ⊆ sizedInputRegion input.data := by
    by_cases hn : input.data.size = 0
    · have absent : input.key ∉ input.data := by
        intro hmem
        obtain ⟨j, hj, _⟩ := Array.mem_iff_getElem.mp hmem
        lia
      refine ⟨none, 0, t, completes_while_false .ult (body w) t (by simpa [hn] using hult),
        absent, heq, rfl, hcursor.2.2.1, ?_, Finset.empty_subset _⟩
      simp [hn]
    · have hpos : 0 < input.data.size := by lia
      obtain ⟨output, cost, u, hc, ho, hr, hm, hone, ht, ha⟩ :=
        loop_run input 0 t hcursor hpos (by simpa [hpos] using hult) (by simp)
      refine ⟨output, cost, u, hc, ho, hr, hm, hone, ?_, ha⟩
      cases output <;> simpa using ht
  obtain ⟨output, cost, u, hl, ho, hr, hm', hone, htime, hspace⟩ := loop
  obtain ⟨final, hf, hout, hmf⟩ := finish_run input output u h.fits ho hr hone
  have hzero : {(0 : Word w)} ⊆ sizedInputRegion input.data := by
    simp only [Finset.singleton_subset_iff, sizedInputRegion, Finset.mem_image]
    exact ⟨0, Finset.mem_range.mpr (by lia), rfl⟩
  refine ⟨output, ⟨6, {0}⟩ + cost + ⟨1, ∅⟩, final, ?_, hout, ho,
    hmf.trans (hm'.trans hm), ?_, ?_⟩
  · simpa [linearSearch, add_assoc] using hs.seq (hl.seq hf)
  · cases output <;> simp_all only [RAMCost.add_time] <;> lia
  · simpa only [RAMCost.add_addresses, Finset.union_empty] using
      Finset.union_subset hzero hspace

/-- Total first-match search, with exact time and a footprint confined to the input region. -/
theorem linearSearch_correct (w : Nat) :
    SolvesIn (linearSearch w) Search.linearSearch
      (fun input s => RepresentsSizedSearchInput input key s) (RepresentsSearchOutput index)
      (fun input cost final =>
        cost.time = (match searchOutput index final with
          | none => 4 * input.data.size + 7
          | some i => 4 * i + 10) ∧ cost.addresses ⊆ sizedInputRegion input.data) := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, _, ht, ha⟩ := linearSearch_run input s hi
  exact ⟨output, cost, final, hc, ho, hs, by simpa only [show searchOutput index final = output
    from ho] using ht, ha⟩

/-- Every completed execution returns the specified first match or absence certificate. -/
theorem linearSearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s)
    {fuel : Nat} {result : AddWriter (RAMCost w) Unit} {final : ExecutionState w 5}
    (hr : execute fuel (linearSearch w) s = some (result, final)) :
    searchOutput index final.machine ∈ Search.linearSearch input := by
  obtain ⟨output, ho, hs⟩ := (linearSearch_correct w).correct hi (completes_of_execute hr)
  have ho : searchOutput index final.machine = output := ho
  rwa [ho]

/-- Search does not change input cells or unrelated background memory. -/
theorem linearSearch_memory (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s) {cost : RAMCost w} {final : RAMState w 5}
    (hc : Completes (linearSearch w) s cost final) : final.Memory = s.Memory := by
  obtain ⟨_, _, _, hc', _, _, hm, _⟩ := linearSearch_run input s hi
  obtain ⟨rfl, rfl⟩ := hc'.unique hc
  exact hm

end Algolean.Algorithms.WordRAM
