/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Correctness

/-!
# Linear-search complexity

Search takes at most `4 * n + 7` primitive operations and attains this bound on absent keys.
All accessed cells belong to the input, so auxiliary memory is zero. Total space is `n + 1`,
including the size header and unread cells. These statements hold for every completed execution,
independently of unused interpreter fuel.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open LinearSearch

/-- Linear worst-case time, zero auxiliary memory, and exact total input space. -/
theorem linearSearch_complexity (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s) {cost : RAMCost w} {final : RAMState w 5}
    (hc : Completes (linearSearch w) s cost final) :
    cost.time ≤ 4 * input.data.size + 7 ∧
      cost.auxiliarySpace (sizedInputRegion input.data) = 0 ∧
      cost.totalSpace (sizedInputRegion input.data) = input.data.size + 1 := by
  obtain ⟨output, ho, hs⟩ := (linearSearch_correct w).correct hi hc
  obtain ⟨ht, ha⟩ := (linearSearch_correct w).bounded hi hc
  have hout : searchOutput index final = output := ho
  rw [hout] at ht
  refine ⟨?_, ?_, ?_⟩
  · cases output with
    | none => exact ht.le
    | some i =>
      have hib : i < input.data.size := hs.1
      change cost.time = 4 * i + 10 at ht
      lia
  · simp [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr ha]
  · simp [RAMCost.totalSpace, Finset.union_eq_right.mpr ha,
      sizedInputRegion_card input.data hi.fits]

/-- An absent key scans the whole array and attains the upper time bound. -/
theorem linearSearch_time_of_not_mem (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s) (habsent : input.key ∉ input.data)
    {cost : RAMCost w} {final : RAMState w 5} (hc : Completes (linearSearch w) s cost final) :
    cost.time = 4 * input.data.size + 7 := by
  obtain ⟨output, ho, hs⟩ := (linearSearch_correct w).correct hi hc
  have hout : searchOutput index final = output := ho
  have ht := ((linearSearch_correct w).bounded hi hc).1
  rw [hout] at ht
  cases output with
  | none => exact ht
  | some i => exact (habsent (Array.mem_of_getElem? hs.2.1)).elim

/-- The fixed program meets the standard time-and-total-space contract. -/
theorem linearSearch_runsWithin (w : Nat) :
    SolvesIn (linearSearch w) Search.linearSearch
      (fun input s => RepresentsSizedSearchInput input key s) (RepresentsSearchOutput index)
      (timeSpaceBound (fun input => sizedInputRegion input.data)
        (fun input => 4 * input.data.size + 7) (fun input => input.data.size + 1)) := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, _⟩ := linearSearch_correct w input s hi
  obtain ⟨ht, _, hspace⟩ := linearSearch_complexity input s hi hc
  exact ⟨output, cost, final, hc, ho, hs, ht, hspace.le⟩

/-- Every fitting length has an instance attaining the linear bound at positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n < 2 ^ w) :
    ∃ input : Search.Input (Word w), input.data.size = n ∧ ∃ cost final,
      Completes (linearSearch w) (linearSearchState input.data input.key key) cost final ∧
        cost.time = 4 * n + 7 := by
  let input : Search.Input (Word w) := ⟨Array.replicate n 0, 1⟩
  let s := linearSearchState input.data input.key key
  have hi : RepresentsSizedSearchInput input key s :=
    linearSearchState_represents input.data input.key key (by simpa [input] using hn)
  have habsent : input.key ∉ input.data := by
    simp [input, ← BitVec.toNat_inj, Nat.ne_of_gt hw]
  obtain ⟨_, cost, final, hc, _⟩ := linearSearch_correct w input s hi
  exact ⟨input, by simp [input], cost, final, hc,
    by simpa [input] using linearSearch_time_of_not_mem input s hi habsent hc⟩

end Algolean.Algorithms.WordRAM
