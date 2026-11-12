/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Common

/-!
# Total correctness of WordRAM linear search

The public Hoare specification states first-match correctness and memory preservation separately
from resource bounds. It handles arbitrary representing states within an explicit fuel budget.
The existing soundness bridge then supplies the machine-independent `Solves` interface.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open Cslib Std.WP LinearSearch
open scoped WordRAM.Spec

set_option experimental.vcgen true

/-- First-match correctness and preservation of all input and background memory. -/
theorem linearSearch_correct (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) (spare : Nat) :
    ⦃ SearchPre input s spare ⦄ (linearSearch w)
      ⦃ fun _ _ final => SolvesInput input s.Memory final.machine; fun _ => False ⦄ := by
  have hs := setup_loop_spec input s h spare
  have hl := loop_spec input 0 s.Memory ⟨6, {0}⟩ (2 + spare)
  have hf := finish_spec input 0 s.Memory ⟨6, {0}⟩ spare h.fits
  vcgen [linearSearch, hs, hl, hf]
  all_goals grind [FinishedPost, SolvesInput, RepresentsSearchOutput]

/-- Uniform first-match search on every represented input, with no resource assumptions. -/
def SolvesSearch (w : Nat) : Prop :=
  Solves (linearSearch w) Search.linearSearch
    (fun input s => RepresentsSizedSearchInput input key s) (RepresentsSearchOutput index)

/-- The verified program satisfies the shared solving interface. -/
theorem linearSearch_solves (w : Nat) : SolvesSearch w := by
  intro input s hi
  obtain ⟨cost, final, hc, hs⟩ :=
    WordRAM.Spec.completes (linearSearch_correct input s hi 0) ⟨rfl, rfl⟩
  exact ⟨searchOutput index final.machine, cost, final.machine, hc, rfl, hs.1, trivial⟩

/-- The same first-match guarantee holds for every successful fuelled execution. -/
theorem linearSearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s)
    {fuel : Nat} {result : AddWriter (RAMCost w) Unit} {final : ExecutionState w 5}
    (hr : execute fuel (linearSearch w) s = some (result, final)) :
    searchOutput index final.machine ∈ Search.linearSearch input := by
  obtain ⟨output, ho, hs⟩ := SolvesIn.correct (linearSearch_solves w) hi (completes_of_execute hr)
  simpa only [show searchOutput index final.machine = output from ho] using hs

/-- A completed search preserves every memory cell, including unrelated background cells. -/
theorem linearSearch_memory (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s) {cost : RAMCost w} {final : RAMState w 5}
    (hc : Completes (linearSearch w) s cost final) : final.Memory = s.Memory := by
  obtain ⟨_, _, hc', hs⟩ :=
    WordRAM.Spec.completes (linearSearch_correct input s hi 0) ⟨rfl, rfl⟩
  obtain ⟨rfl, rfl⟩ := hc'.unique hc
  exact hs.2

end Algolean.Algorithms.WordRAM
