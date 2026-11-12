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
including the header and unread input cells. Interpreter fuel is accounted for separately.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open Std.WP LinearSearch
open scoped WordRAM.Spec

set_option experimental.vcgen true

private theorem finished_bound (input : Search.Input (Word w)) (memory : Memory w)
    (hfits : input.data.size < 2 ^ w) (cost : RAMCost w) (current : ExecutionState w 5)
    (h : FinishedPost input 0 memory ⟨6, {0}⟩ cost current) :
    ComplexityBound input cost current.machine := by
  obtain ⟨output, ho, hout, _, ht, ha⟩ := h
  change searchOutput index current.machine = output at hout
  have hspace : cost.addresses ⊆ sizedInputRegion input.data := by simpa using ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases output <;> simp_all [searchTime, loopTime] <;> lia
  · cases output <;> simp_all [loopTime, Search.linearSearch, Search.IsFirstMatch] <;> lia
  · simp [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr hspace]
  · simp [RAMCost.totalSpace, Finset.union_eq_right.mpr hspace,
      sizedInputRegion_card input.data hfits]

/-- Exact and worst-case time, zero auxiliary memory, and exact total input space. -/
theorem linearSearch_complexity (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) (spare : Nat) :
    ⦃ SearchPre input s spare ⦄ (linearSearch w)
      ⦃ fun _ cost final => ComplexityBound input cost final.machine; fun _ => False ⦄ := by
  have hs := setup_loop_spec input s h spare
  have hl := loop_spec input 0 s.Memory ⟨6, {0}⟩ (2 + spare)
  have hf := finish_spec input 0 s.Memory ⟨6, {0}⟩ spare h.fits
  vcgen [linearSearch, hs, hl, hf]
  all_goals first
    | grind only
    | rename_i cost current hp
      exact finished_bound input s.Memory h.fits cost current hp.1

/-- The same represented computation with the named resource bound. -/
def SearchRunsWithin (w : Nat) : Prop :=
  SolvesIn (linearSearch w) Search.linearSearch
    (fun input s => RepresentsSizedSearchInput input key s) (RepresentsSearchOutput index)
    (ComplexityBound · · ·)

/-- Correctness and resource verification describe the same completed execution. -/
theorem linearSearch_runsWithin (w : Nat) : SearchRunsWithin w := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, _⟩ := linearSearch_solves w input s hi
  obtain ⟨_, _, hb, hbound⟩ :=
    WordRAM.Spec.completes (linearSearch_complexity input s hi 0) ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hb.unique hc
  exact ⟨output, _, _, hc, ho, hs, by simpa only [zero_add] using hbound⟩

/-- Every fitting length has a worst-case instance at positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n < 2 ^ w) :
    ∃ input : Search.Input (Word w), input.data.size = n ∧ ∃ cost final,
      Completes (linearSearch w) (linearSearchState input.data input.key key) cost final ∧
        cost.time = 4 * n + 7 := by
  let input : Search.Input (Word w) := ⟨Array.replicate n 0, 1⟩
  have hi := linearSearchState_represents input.data input.key key (by simpa [input] using hn)
  obtain ⟨output, cost, final, hc, ho, hs, hb⟩ := linearSearch_runsWithin w input _ hi
  have habsent : input.key ∉ input.data := by
    simp [input, ← BitVec.toNat_inj, Nat.ne_of_gt hw]
  have hout : searchOutput index final = none := by
    cases output with
    | none => exact ho
    | some i => exact (habsent (Array.mem_of_getElem? hs.2.1)).elim
  exact ⟨input, by simp [input], cost, final, hc,
    by simpa [hout, searchTime, input] using hb.1⟩

end Algolean.Algorithms.WordRAM
