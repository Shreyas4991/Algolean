/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Algorithm
public import Algolean.Models.WordRAM.Verification

/-!
# Linear-search invariants and execution

The cursor names the first unexamined element. The loop invariant excludes the preceding prefix;
each unsuccessful iteration advances the cursor or reaches the inclusive last address.
VCGen tracks exact costs and a sufficient fuel budget through the existing WordRAM handlers.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM.LinearSearch

open Cslib Std.WP
open scoped WordRAM.Spec

set_option experimental.vcgen true

/-- Physical state at the start of a probe of zero-based position `i`. -/
def Cursor (input : Search.Input (Word w)) (i : Nat) (s : RAMState w 5) : Prop :=
  RepresentsSizedSearchInput input key s ∧
    s.Registers index = BitVec.ofNat w (i + 1) ∧ s.Registers one = 1 ∧
    s.Registers last = BitVec.ofNat w input.data.size

/-- Before `finish`, a successful result still names a one-based memory address. -/
def AtResult (output : Option Nat) (s : RAMState w 5) : Prop :=
  match output with
  | none => s.Flags .eq = false
  | some i => s.Flags .eq = true ∧ s.Registers index = BitVec.ofNat w (i + 1)

/-- Setup initializes its working state and charges the header read to any initial cost. -/
theorem setup_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) (initial : RAMCost w) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 6⟩ ⦄ (setup w)
      ⦃ fun _ cost final => cost = initial + ⟨6, {0}⟩ ∧ Cursor input 0 final.machine ∧
        final.machine.Flags .eq = false ∧
        final.machine.Flags .ult = decide (0 < input.data.size) ∧
        final.machine.Memory = s.Memory ∧ final.fuel = fuel; fun _ => False ⦄ := by
  let t := (((((s.writeFlag .eq false).writeRegister index 0).writeRegister last
    (BitVec.ofNat w input.data.size)).writeFlag .ult (decide (0 < input.data.size))).writeRegister
    one 1).writeRegister index 1
  have hn : (BitVec.ofNat w input.data.size).toNat = input.data.size :=
    Nat.mod_eq_of_lt h.fits
  have hheader : s.Memory (BitVec.ofNat w 0) = BitVec.ofNat w input.data.size := h.header
  have hm : t.Memory = s.Memory := by simp [t]
  have hk : t.Registers key = input.key := by simp [t, index, key, last, one, h.key_eq]
  have hcursor : Cursor input 0 t := by
    refine ⟨⟨h.fits, ?_, ?_, hk⟩, ?_, ?_, ?_⟩
    · simpa only [hm] using h.header
    · intro i hi
      simpa only [hm] using h.read i hi
    all_goals simp [t, index, one, last]
  vcgen [setup]
  all_goals simp_all [t, CmpOp.eval, add_assoc]

private def hitState (s : RAMState w 5) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq true).writeFlag .ult false

private def advanceState (s : RAMState w 5) : RAMState w 5 :=
  (((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq false).writeFlag
    .ult true).writeRegister index (s.Registers index + s.Registers one)

private def exhaustedState (s : RAMState w 5) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq false).writeFlag .ult false

private theorem probe_spec (s : RAMState w 5) (initial : RAMCost w) (fuel : Nat)
    (post : Unit → RAMCost w → ExecutionState w 5 → Prop)
    (hit : s.Memory (s.Registers index) = s.Registers key →
      post () (initial + ⟨3, {s.Registers index}⟩) ⟨hitState s, fuel + 2⟩)
    (advance : s.Memory (s.Registers index) ≠ s.Registers key →
      (s.Registers index).toNat < (s.Registers last).toNat →
      post () (initial + ⟨4, {s.Registers index}⟩) ⟨advanceState s, fuel⟩)
    (exhausted : s.Memory (s.Registers index) ≠ s.Registers key →
      ¬(s.Registers index).toNat < (s.Registers last).toNat →
      post () (initial + ⟨4, {s.Registers index}⟩) ⟨exhaustedState s, fuel⟩) :
    Triple (body w) (fun cost current => cost = initial ∧ current = ⟨s, fuel + 6⟩)
      post (fun _ => False) := by
  by_cases found : s.Memory (s.Registers index) = s.Registers key
  all_goals by_cases more : (s.Registers index).toNat < (s.Registers last).toNat
  all_goals repeat' (vcgen [body, Prog.ifThenElse, test] <;>
    simp_all only [hitState, advanceState, exhaustedState, index, value, one,
      ↓binderNameHint.eq_1, Fin.isValue, ifThenElse_test, step, FreeM.wp_bind, FreeM.wp_lift,
      WordRAM.Spec.costHandler_apply, FuelExecMonad.execute_lift_succ, CmpOp.eval,
      BinOp.eval, RAMState.writeRegister_registers, RAMState.writeFlag_flags,
      RAMState.writeFlag_registers, ↓reduceIte, Fin.reduceEq, decide_true, decide_false,
      FuelExecMonad.execute_pure, RAMCost.mk_add, Finset.empty_union, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some, RAMCost.zero_time, add_zero,
      RAMCost.zero_addresses, add_assoc, Nat.reduceAdd, Finset.union_empty, true_and,
      lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true, Nat.add_one_sub_one,
      and_true, Bool.false_eq_true])
  all_goals grind only

/-- Finish decodes the answer, preserves memory, and costs one operation and two fuel units. -/
private theorem finish_at_spec (input : Search.Input (Word w)) (output : Option Nat)
    (s : RAMState w 5)
    (hfits : input.data.size < 2 ^ w) (ho : output ∈ Search.linearSearch input)
    (hr : AtResult output s) (hone : s.Registers one = 1) (initial : RAMCost w) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 2⟩ ⦄ (finish w)
      ⦃ fun _ cost final => cost = initial + ⟨1, ∅⟩ ∧ RepresentsSearchOutput index output
        final.machine ∧ final.machine.Memory = s.Memory ∧ final.fuel = fuel;
        fun _ => False ⦄ := by
  cases output <;> vcgen [finish, Prog.ifThenElse, flag]
  all_goals simp_all [RepresentsSearchOutput, searchOutput, AtResult, BinOp.eval,
    BitVec.ofNat_add, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  all_goals grind [Search.linearSearch, Search.IsFirstMatch]

/-- A fixed initial state, zero accumulated cost, and a sufficient interpreter budget. -/
def SearchPre (input : Search.Input (Word w)) (s : RAMState w 5) (spare : Nat)
    (cost : RAMCost w) (current : ExecutionState w 5) : Prop :=
  cost = 0 ∧ current = ⟨s, 7 * input.data.size + 9 + spare⟩

/-- Correct first-match output together with preservation of the entire memory. -/
def SolvesInput (input : Search.Input (Word w)) (memory : Memory w) (final : RAMState w 5) : Prop :=
  searchOutput index final ∈ Search.linearSearch input ∧ final.Memory = memory

/-- Exact total time as a function of the decoded answer. -/
def searchTime (size : Nat) : Option Nat → Nat
  | none => 4 * size + 7
  | some i => 4 * i + 10

/-- Exact and worst-case time, no auxiliary cells, and total input space. -/
def ComplexityBound (input : Search.Input (Word w)) (cost : RAMCost w)
    (final : RAMState w 5) : Prop :=
  cost.time = searchTime input.data.size (searchOutput index final) ∧
    cost.time ≤ 4 * input.data.size + 7 ∧
    cost.auxiliarySpace (sizedInputRegion input.data) = 0 ∧
    cost.totalSpace (sizedInputRegion input.data) = input.data.size + 1

/-- Exact loop time, measured from the first position considered by this invocation. -/
def loopTime (size start : Nat) : Option Nat → Nat
  | none => 4 * (size - start)
  | some j => 4 * (j - start) + 3

/-- The loop's answer, preserved memory, exact accumulated time, and input-only accesses. -/
def LoopPost (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (cost : RAMCost w) (current : ExecutionState w 5) : Prop :=
  ∃ output, output ∈ Search.linearSearch input ∧ AtResult output current.machine ∧
    current.machine.Memory = memory ∧ current.machine.Registers one = 1 ∧
    cost.time = initial.time + loopTime input.data.size start output ∧
    cost.addresses ⊆ initial.addresses ∪ sizedInputRegion input.data

/-- A pending probe, with enough remaining fuel for every unexamined cell and the exit test. -/
@[grind] structure Running (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve position : Nat) (cost : RAMCost w)
    (current : ExecutionState w 5) : Prop where
  from_start : start ≤ position
  in_bounds : position < input.data.size
  cursor : Cursor input position current.machine
  before : ∀ j, j < position → input.data[j]? ≠ some input.key
  running : current.machine.Flags .ult = true
  memory_eq : current.machine.Memory = memory
  time_eq : cost.time = initial.time + 4 * (position - start)
  fuel_eq : current.fuel = 7 * (input.data.size - position) + 1 + reserve
  addresses : cost.addresses ⊆ initial.addresses ∪ sizedInputRegion input.data

/-- Either a pending probe or a finished answer with fuel reserved for the final test. -/
def LoopInvariant (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve : Nat) (cost : RAMCost w)
    (current : ExecutionState w 5) : Prop :=
  (∃ position, Running input start memory initial reserve position cost current) ∨
    (LoopPost input start memory initial cost current ∧ current.machine.Flags .ult = false ∧
      reserve + 1 ≤ current.fuel)

private theorem exclude_next {input : Search.Input (Word w)} {j : Nat}
    (hj : j < input.data.size) (before : ∀ k, k < j → input.data[k]? ≠ some input.key)
    (miss : input.data[j] ≠ input.key) :
    ∀ k, k < j + 1 → input.data[k]? ≠ some input.key := by
  grind [Array.getElem?_eq_getElem]

private theorem cursor_advance {input : Search.Input (Word w)} {j : Nat} {s : RAMState w 5}
    (h : Cursor input j s) : Cursor input (j + 1) (advanceState s) := by
  obtain ⟨hinput, hindex, hone, hlast⟩ := h
  have hm : (advanceState s).Memory = s.Memory := by simp [advanceState]
  have hk : (advanceState s).Registers key = input.key := by
    simp [advanceState, index, value, key, hinput.key_eq]
  simp only [index, one, last] at hindex hone hlast
  refine ⟨⟨hinput.fits, ?_, ?_, hk⟩, ?_, ?_, ?_⟩
  · simpa only [hm] using hinput.header
  · intro k hk
    simpa only [hm] using hinput.read k hk
  all_goals simp [advanceState, index, value, one, last, hindex, hone, hlast, BitVec.ofNat_add]

section Transitions

variable {input : Search.Input (Word w)} {start reserve j fuel : Nat} {memory : Memory w}
  {initial cost : RAMCost w} {s : RAMState w 5}

private theorem probe_footprint
    (h : Running input start memory initial reserve j cost ⟨s, fuel + 1⟩) (time : Nat) :
    (cost + ⟨time, {s.Registers index}⟩).addresses ⊆
      initial.addresses ∪ sizedInputRegion input.data := by
  apply Finset.union_subset h.addresses
  simp only [Finset.singleton_subset_iff]
  apply Finset.mem_union_right
  rw [h.cursor.2.1]
  exact Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr (by have := h.in_bounds; lia), rfl⟩

private theorem hit_preserves
    (h : Running input start memory initial reserve j cost ⟨s, fuel + 1⟩)
    (found : input.data[j]'h.in_bounds = input.key) :
    LoopInvariant input start memory initial reserve
      (cost + ⟨3, {s.Registers index}⟩) ⟨hitState s, fuel - 4⟩ := by
  refine Or.inr ⟨?_, by simp [hitState], ?_⟩
  · refine ⟨some j, ⟨h.in_bounds, by simp [h.in_bounds, found], h.before⟩,
      ?_, ?_, ?_, ?_, probe_footprint h 3⟩
    · simpa [AtResult, hitState, index, value] using h.cursor.2.1
    · simpa [hitState] using h.memory_eq
    · simpa [hitState, value, one] using h.cursor.2.2.1
    · change cost.time + 3 = initial.time + (4 * (j - start) + 3)
      grind
  · grind

private theorem advance_preserves
    (h : Running input start memory initial reserve j cost ⟨s, fuel + 1⟩)
    (miss : input.data[j]'h.in_bounds ≠ input.key) (more : j + 1 < input.data.size) :
    LoopInvariant input start memory initial reserve
      (cost + ⟨4, {s.Registers index}⟩) ⟨advanceState s, fuel - 6⟩ := by
  refine Or.inl ⟨j + 1, ?_⟩
  refine ⟨by grind, more, cursor_advance h.cursor,
    exclude_next h.in_bounds h.before miss, by simp [advanceState], ?_, ?_, ?_,
    probe_footprint h 4⟩
  · simpa [advanceState] using h.memory_eq
  · change cost.time + 4 = initial.time + 4 * (j + 1 - start)
    grind
  · change fuel - 6 = 7 * (input.data.size - (j + 1)) + 1 + reserve
    grind

private theorem exhausted_preserves
    (h : Running input start memory initial reserve j cost ⟨s, fuel + 1⟩)
    (miss : input.data[j]'h.in_bounds ≠ input.key) (lastCell : ¬j + 1 < input.data.size) :
    LoopInvariant input start memory initial reserve
      (cost + ⟨4, {s.Registers index}⟩) ⟨exhaustedState s, fuel - 6⟩ := by
  have before := exclude_next h.in_bounds h.before miss
  have absent : input.key ∉ input.data := by
    intro hmem
    obtain ⟨k, hk, heq⟩ := Array.mem_iff_getElem.mp hmem
    exact before k (by have := h.in_bounds; lia) (by simpa [hk] using heq)
  refine Or.inr ⟨?_, by simp [exhaustedState], ?_⟩
  · refine ⟨none, absent, by simp [AtResult, exhaustedState], ?_, ?_, ?_,
      probe_footprint h 4⟩
    · simpa [exhaustedState] using h.memory_eq
    · simpa [exhaustedState, value, one] using h.cursor.2.2.1
    · change cost.time + 4 = initial.time + 4 * (input.data.size - start)
      grind
  · grind

end Transitions

private theorem invariant_enough (input : Search.Input (Word w)) (start : Nat)
    (memory : Memory w) (initial : RAMCost w) (reserve : Nat) :
    ∀ cost current, LoopInvariant input start memory initial reserve cost current →
      0 < current.fuel := by
  rintro cost current (⟨j, h⟩ | ⟨_, _, hf⟩)
  · grind
  · lia

private theorem invariant_exit (input : Search.Input (Word w)) (start : Nat)
    (memory : Memory w) (initial : RAMCost w) (reserve : Nat) :
    ∀ cost current, LoopInvariant input start memory initial reserve cost current →
      current.machine.Flags .ult = false →
      LoopPost input start memory initial cost { current with fuel := current.fuel - 1 } ∧
        reserve ≤ current.fuel - 1 := by
  rintro cost current (⟨j, h⟩ | ⟨hp, _, hbudget⟩) hf
  · grind
  · exact ⟨hp, by lia⟩

/-- One probe preserves the resource invariant after the loop test has consumed its fuel. -/
@[spec] theorem body_spec (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve : Nat) :
    Triple (body w)
      (fun cost current =>
        LoopInvariant input start memory initial reserve cost
          { current with fuel := current.fuel + 1 } ∧ current.machine.Flags .ult = true)
      (fun _ => LoopInvariant input start memory initial reserve) (fun _ => False) := by
  apply Triple.intro
  rintro cost ⟨s, fuel⟩ ⟨hinv, hflag⟩
  rcases hinv with ⟨j, h⟩ | ⟨_, hstopped, _⟩
  · have hf : 6 ≤ fuel := by grind
    have hj : j < input.data.size := h.in_bounds
    have hread : s.Memory (s.Registers index) = input.data[j] := by
      rw [h.cursor.2.1]
      exact h.cursor.1.read j hj
    have hidxn : (s.Registers index).toNat = j + 1 := by
      rw [h.cursor.2.1]
      exact Nat.mod_eq_of_lt (by have := h.cursor.1.fits; lia)
    have hlastn : (s.Registers last).toNat = input.data.size := by
      rw [h.cursor.2.2.2]
      exact Nat.mod_eq_of_lt h.cursor.1.fits
    refine (probe_spec s cost (fuel - 6) _ ?_ ?_ ?_).le_wp cost ⟨s, fuel⟩ ⟨rfl, ?_⟩
    · intro found
      simpa only [show fuel - 6 + 2 = fuel - 4 by lia] using
        hit_preserves h ((hread.symm.trans found).trans h.cursor.1.key_eq)
    · intro miss more
      apply advance_preserves h
      · exact fun heq => miss (hread.trans (heq.trans h.cursor.1.key_eq.symm))
      · simpa only [hidxn, hlastn] using more
    · intro miss lastCell
      apply exhausted_preserves h
      · exact fun heq => miss (hread.trans (heq.trans h.cursor.1.key_eq.symm))
      · simpa only [hidxn, hlastn] using lastCell
    · congr 1; lia
  · simp_all

/-- Verify the whole loop through the shared fuel-aware WordRAM loop rule. -/
theorem loop_spec (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve : Nat) :
    Triple (whileLoop .ult (body w)) (LoopInvariant input start memory initial reserve)
      (fun _ cost final => LoopPost input start memory initial cost final ∧
        reserve ≤ final.fuel) (fun _ => False) := by
  vcgen invariants
  · LoopInvariant input start memory initial reserve
  all_goals first
    | exact invariant_enough input start memory initial reserve _ _ ‹_›
    | exact invariant_exit input start memory initial reserve _ _ ‹_› ‹_›
    | assumption

/-- The final phase's decoded answer and exact resources, before choosing a public postcondition. -/
def FinishedPost (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (cost : RAMCost w) (current : ExecutionState w 5) : Prop :=
  ∃ output, output ∈ Search.linearSearch input ∧ RepresentsSearchOutput index output
    current.machine ∧ current.machine.Memory = memory ∧
    cost.time = initial.time + loopTime input.data.size start output + 1 ∧
    cost.addresses ⊆ initial.addresses ∪ sizedInputRegion input.data

/-- Finish a verified loop, preserving its answer and accounting for the final operation. -/
theorem finish_spec (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve : Nat) (hfits : input.data.size < 2 ^ w) :
    ⦃ fun cost current => LoopPost input start memory initial cost current ∧
        reserve + 2 ≤ current.fuel ⦄ (finish w)
      ⦃ fun _ cost final => FinishedPost input start memory initial cost final ∧
        reserve ≤ final.fuel; fun _ => False ⦄ := by
  apply Triple.intro
  rintro cost ⟨s, fuel⟩ ⟨⟨output, ho, hr, hm, hone, ht, ha⟩, hf⟩
  refine (finish_at_spec input output s hfits ho hr hone cost (fuel - 2)).entails_wp_of_post
    ?_ cost ⟨s, fuel⟩ ⟨rfl, ?_⟩
  · rintro _ total final ⟨rfl, hout, hmem, hfuel⟩
    refine ⟨⟨output, ho, hout, hmem.trans hm, ?_, ?_⟩, by lia⟩
    · change cost.time + 1 = _
      rw [ht]
    · simpa only [RAMCost.add_addresses, Finset.union_empty] using ha
  · congr 1; lia

private theorem initialized (input : Search.Input (Word w)) (memory : Memory w) (spare : Nat)
    (current : ExecutionState w 5) (hcursor : Cursor input 0 current.machine)
    (heq : current.machine.Flags .eq = false)
    (hult : current.machine.Flags .ult = decide (0 < input.data.size))
    (hm : current.machine.Memory = memory) (hf : current.fuel = 7 * input.data.size + 3 + spare) :
    LoopInvariant input 0 memory ⟨6, {0}⟩ (2 + spare) ⟨6, {0}⟩ current := by
  by_cases hn : input.data.size = 0
  · refine Or.inr ⟨?_, by simpa [hn] using hult, by lia⟩
    refine ⟨none, ?_, heq, hm, hcursor.2.2.1, by simp [loopTime, hn], Finset.subset_union_left⟩
    grind [Search.linearSearch, Array.mem_iff_getElem]
  · refine Or.inl ⟨0, ⟨le_rfl, by lia, hcursor, by simp, ?_, hm,
      by simp, by lia, Finset.subset_union_left⟩⟩
    simpa [show 0 < input.data.size by lia] using hult

/-- Setup establishes the loop invariant, including the empty-array case. -/
theorem setup_loop_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) (spare : Nat) :
    ⦃ SearchPre input s spare ⦄ (setup w)
      ⦃ fun _ => LoopInvariant input 0 s.Memory ⟨6, {0}⟩ (2 + spare); fun _ => False ⦄ := by
  have hs := setup_spec input s h 0 (7 * input.data.size + 3 + spare)
  vcgen [hs]
  · grind [SearchPre]
  · rename_i cost current hp
    rcases hp with ⟨rfl, hc, heq, hult, hm, hf⟩
    exact initialized input s.Memory spare current hc heq hult hm hf

end Algolean.Algorithms.WordRAM.LinearSearch
