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

The cursor names the first unexamined element. The induction excludes the preceding prefix;
each unsuccessful iteration advances the cursor or reaches the inclusive last address.
Costs are accumulated along this same terminating execution, independently of interpreter fuel.
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

/-- Extract the successful initialized state through the shared handler's soundness bridge. -/
theorem setup_run (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) :
    ∃ t, Completes (setup w) s ⟨6, {0}⟩ t ∧ Cursor input 0 t ∧
      t.Flags .eq = false ∧ t.Flags .ult = decide (0 < input.data.size) ∧ t.Memory = s.Memory := by
  obtain ⟨cost, final, hc, ht, hcursor, heq, hult, hm, _⟩ :=
    WordRAM.Spec.completes (setup_spec input s h 0 0) ⟨rfl, rfl⟩
  simp only [zero_add] at ht
  subst cost
  exact ⟨final.machine, hc, hcursor, heq, hult, hm⟩

private def hitState (s : RAMState w 5) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq true).writeFlag .ult false

private def advanceState (s : RAMState w 5) : RAMState w 5 :=
  (((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq false).writeFlag
    .ult true).writeRegister index (s.Registers index + s.Registers one)

private def exhaustedState (s : RAMState w 5) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq false).writeFlag .ult false

private theorem probe_hit_spec (s : RAMState w 5) (initial : RAMCost w) (fuel : Nat)
    (found : s.Memory (s.Registers index) = s.Registers key) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 4⟩ ⦄ (body w)
      ⦃ fun _ cost final => cost = initial + ⟨3, {s.Registers index}⟩ ∧
        final = ⟨hitState s, fuel⟩; fun _ => False ⦄ := by
  repeat' (vcgen [body, Prog.ifThenElse, test] <;>
    simp_all only [hitState, index, value, ↓binderNameHint.eq_1, Fin.isValue,
      ifThenElse_test, step,
      FreeM.wp_bind, FreeM.wp_lift, WordRAM.Spec.costHandler_apply,
      FuelExecMonad.execute_lift_succ, CmpOp.eval, RAMState.writeRegister_registers,
      ↓reduceIte, Fin.reduceEq, decide_true, FuelExecMonad.execute_pure,
      RAMCost.mk_add, Finset.empty_union, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, RAMCost.zero_time, add_zero, RAMCost.zero_addresses, add_assoc,
      Nat.reduceAdd, Finset.union_empty, true_and, lt_add_iff_pos_left, add_pos_iff,
      Nat.ofNat_pos, or_true, Nat.add_one_sub_one, and_true,
      RAMState.writeFlag_flags])

private theorem probe_advance_spec (s : RAMState w 5) (initial : RAMCost w) (fuel : Nat)
    (miss : s.Memory (s.Registers index) ≠ s.Registers key)
    (more : (s.Registers index).toNat < (s.Registers last).toNat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 6⟩ ⦄ (body w)
      ⦃ fun _ cost final => cost = initial + ⟨4, {s.Registers index}⟩ ∧
        final = ⟨advanceState s, fuel⟩; fun _ => False ⦄ := by
  repeat' (vcgen [body, Prog.ifThenElse, test] <;>
    simp_all only [advanceState, index, value, one, BinOp.eval, ↓binderNameHint.eq_1, Fin.isValue,
      ifThenElse_test, step,
      FreeM.wp_bind, FreeM.wp_lift, WordRAM.Spec.costHandler_apply,
      FuelExecMonad.execute_lift_succ, CmpOp.eval, RAMState.writeRegister_registers,
      ↓reduceIte, Fin.reduceEq, decide_true, decide_false, FuelExecMonad.execute_pure,
      RAMCost.mk_add, Finset.empty_union, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, RAMCost.zero_time, add_zero, RAMCost.zero_addresses, add_assoc,
      Nat.reduceAdd, Finset.union_empty, true_and, lt_add_iff_pos_left, add_pos_iff,
      Nat.ofNat_pos, or_true, Nat.add_one_sub_one, and_true,
      RAMState.writeFlag_flags, RAMState.writeFlag_registers,
      Bool.false_eq_true])

private theorem probe_exhausted_spec (s : RAMState w 5) (initial : RAMCost w) (fuel : Nat)
    (miss : s.Memory (s.Registers index) ≠ s.Registers key)
    (lastCell : ¬(s.Registers index).toNat < (s.Registers last).toNat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 6⟩ ⦄ (body w)
      ⦃ fun _ cost final => cost = initial + ⟨4, {s.Registers index}⟩ ∧
        final = ⟨exhaustedState s, fuel⟩; fun _ => False ⦄ := by
  have noMore : decide ((s.Registers index).toNat < (s.Registers last).toNat) = false := by
    simp only [decide_eq_false_iff_not]
    exact lastCell
  repeat' (vcgen [body, Prog.ifThenElse, test] <;>
    simp_all only [exhaustedState, index, value, not_lt, ↓binderNameHint.eq_1, Fin.isValue,
      ifThenElse_test, step,
      FreeM.wp_bind, FreeM.wp_lift, WordRAM.Spec.costHandler_apply,
      FuelExecMonad.execute_lift_succ, CmpOp.eval, RAMState.writeRegister_registers,
      ↓reduceIte, Fin.reduceEq, decide_false, FuelExecMonad.execute_pure,
      RAMCost.mk_add, Finset.empty_union, Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, RAMCost.zero_time, add_zero, RAMCost.zero_addresses, add_assoc,
      Nat.reduceAdd, Finset.union_empty, true_and, lt_add_iff_pos_left, add_pos_iff,
      Nat.ofNat_pos, or_true, Nat.add_one_sub_one, and_true,
      RAMState.writeFlag_flags, RAMState.writeFlag_registers,
      Bool.false_eq_true])

/-- Finishing costs one primitive operation, preserves memory, and decodes the result. -/
theorem finish_run (input : Search.Input (Word w)) (output : Option Nat) (s : RAMState w 5)
    (hfits : input.data.size < 2 ^ w) (ho : output ∈ Search.linearSearch input)
    (hr : AtResult output s) (hone : s.Registers one = 1) :
    ∃ t, Completes (finish w) s ⟨1, ∅⟩ t ∧ RepresentsSearchOutput index output t ∧
      t.Memory = s.Memory := by
  cases output with
  | none =>
    have hflag : s.Flags .eq = false := hr
    exact ⟨s, ⟨2, by simp [finish, Prog.ifThenElse, flag, hflag]⟩,
      by simp [RepresentsSearchOutput, searchOutput, hflag], rfl⟩
  | some i =>
    obtain ⟨hflag, hindex⟩ := hr
    have hi : i < input.data.size := ho.1
    have hiw : i < 2 ^ w := by lia
    let t := s.writeRegister index (BitVec.ofNat w i)
    have hsub : BitVec.ofNat w (i + 1) - BitVec.ofNat w 1 = BitVec.ofNat w i := by
      rw [BitVec.ofNat_add]
      exact BitVec.add_sub_cancel _ _
    refine ⟨t, ⟨2, ?_⟩, ?_, by simp [t]⟩
    · simp [finish, Prog.ifThenElse, flag, t, hflag, hindex, hone, BinOp.eval, hsub]
    · simp [RepresentsSearchOutput, searchOutput, t, hflag, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hiw]

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
      0 < current.fuel)

private theorem exclude_next {input : Search.Input (Word w)} {j : Nat}
    (hj : j < input.data.size) (before : ∀ k, k < j → input.data[k]? ≠ some input.key)
    (miss : input.data[j] ≠ input.key) :
    ∀ k, k < j + 1 → input.data[k]? ≠ some input.key := by
  intro k hk
  by_cases hkj : k < j
  · exact before k hkj
  · have : k = j := by lia
    subst k
    simpa [hj] using miss

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
      rw [h.time_eq]
      lia
  · have := h.fuel_eq
    have := h.in_bounds
    lia

private theorem advance_preserves
    (h : Running input start memory initial reserve j cost ⟨s, fuel + 1⟩)
    (miss : input.data[j]'h.in_bounds ≠ input.key) (more : j + 1 < input.data.size) :
    LoopInvariant input start memory initial reserve
      (cost + ⟨4, {s.Registers index}⟩) ⟨advanceState s, fuel - 6⟩ := by
  refine Or.inl ⟨j + 1, ?_⟩
  refine ⟨by have := h.from_start; lia, more, cursor_advance h.cursor,
    exclude_next h.in_bounds h.before miss, by simp [advanceState], ?_, ?_, ?_,
    probe_footprint h 4⟩
  · simpa [advanceState] using h.memory_eq
  · change cost.time + 4 = initial.time + 4 * (j + 1 - start)
    have := h.time_eq
    have := h.from_start
    lia
  · change fuel - 6 = 7 * (input.data.size - (j + 1)) + 1 + reserve
    have := h.fuel_eq
    lia

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
      have := h.time_eq
      have := h.from_start
      have := h.in_bounds
      lia
  · have := h.fuel_eq
    have := h.in_bounds
    lia

end Transitions

private theorem invariant_enough (input : Search.Input (Word w)) (start : Nat)
    (memory : Memory w) (initial : RAMCost w) (reserve : Nat) :
    ∀ cost current, LoopInvariant input start memory initial reserve cost current →
      0 < current.fuel := by
  rintro cost current (⟨j, h⟩ | ⟨_, _, hf⟩)
  · have := h.fuel_eq
    lia
  · exact hf

private theorem invariant_exit (input : Search.Input (Word w)) (start : Nat)
    (memory : Memory w) (initial : RAMCost w) (reserve : Nat) :
    ∀ cost current, LoopInvariant input start memory initial reserve cost current →
      current.machine.Flags .ult = false →
      LoopPost input start memory initial cost { current with fuel := current.fuel - 1 } := by
  rintro cost current (⟨j, h⟩ | ⟨hp, _, _⟩) hf
  · have := h.running
    simp_all
  · exact hp

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
  · have hf : 6 ≤ fuel := by have := h.fuel_eq; have := h.in_bounds; lia
    have hj : j < input.data.size := h.in_bounds
    have hread : s.Memory (s.Registers index) = input.data[j] := by
      rw [h.cursor.2.1]
      exact h.cursor.1.read j h.in_bounds
    have hkey : s.Registers key = input.key := h.cursor.1.key_eq
    by_cases found : input.data[j] = input.key
    · have heq : s.Memory (s.Registers index) = s.Registers key := by rwa [hread, hkey]
      refine (probe_hit_spec s cost (fuel - 4) heq).entails_wp_of_post ?_
        cost ⟨s, fuel⟩ ⟨rfl, ?_⟩
      · rintro _ total final ⟨rfl, rfl⟩
        exact hit_preserves h found
      · congr 1; lia
    · have hne : s.Memory (s.Registers index) ≠ s.Registers key := by rwa [hread, hkey]
      have hidxn : (s.Registers index).toNat = j + 1 := by
        rw [h.cursor.2.1]
        exact Nat.mod_eq_of_lt (by have := h.cursor.1.fits; have := h.in_bounds; lia)
      have hlastn : (s.Registers last).toNat = input.data.size := by
        rw [h.cursor.2.2.2]
        exact Nat.mod_eq_of_lt h.cursor.1.fits
      by_cases more : j + 1 < input.data.size
      · have hlt : (s.Registers index).toNat < (s.Registers last).toNat := by
          rwa [hidxn, hlastn]
        refine (probe_advance_spec s cost (fuel - 6) hne hlt).entails_wp_of_post ?_
          cost ⟨s, fuel⟩ ⟨rfl, ?_⟩
        · rintro _ total final ⟨rfl, rfl⟩
          exact advance_preserves h found more
        · congr 1; lia
      · have hnlt : ¬(s.Registers index).toNat < (s.Registers last).toNat := by
          rwa [hidxn, hlastn]
        refine (probe_exhausted_spec s cost (fuel - 6) hne hnlt).entails_wp_of_post ?_
          cost ⟨s, fuel⟩ ⟨rfl, ?_⟩
        · rintro _ total final ⟨rfl, rfl⟩
          exact exhausted_preserves h found more
        · congr 1; lia
  · simp_all

/-- Verify the whole loop through the shared fuel-aware WordRAM loop rule. -/
theorem loop_spec (input : Search.Input (Word w)) (start : Nat) (memory : Memory w)
    (initial : RAMCost w) (reserve : Nat) :
    Triple (whileLoop .ult (body w)) (LoopInvariant input start memory initial reserve)
      (fun _ => LoopPost input start memory initial) (fun _ => False) := by
  vcgen invariants
  · LoopInvariant input start memory initial reserve
  all_goals first
    | exact invariant_enough input start memory initial reserve _ _ ‹_›
    | exact invariant_exit input start memory initial reserve _ _ ‹_› ‹_›
    | assumption

/-- The verified loop terminates after an excluded prefix, with exact time and footprint. -/
theorem loop_run (input : Search.Input (Word w)) (i : Nat) (s : RAMState w 5)
    (hcursor : Cursor input i s) (hi : i < input.data.size) (hflag : s.Flags .ult = true)
    (before : ∀ j, j < i → input.data[j]? ≠ some input.key) :
    ∃ output cost t, Completes (whileLoop .ult (body w)) s cost t ∧
      output ∈ Search.linearSearch input ∧ AtResult output t ∧ t.Memory = s.Memory ∧
      t.Registers one = 1 ∧
      cost.time = (match output with
        | none => 4 * (input.data.size - i)
        | some j => 4 * (j - i) + 3) ∧ cost.addresses ⊆ sizedInputRegion input.data := by
  have hp : LoopInvariant input i s.Memory 0 0 0 ⟨s, 7 * (input.data.size - i) + 1⟩ := by
    exact Or.inl ⟨i, ⟨le_rfl, hi, hcursor, before, hflag, rfl, by simp, by simp, by simp⟩⟩
  obtain ⟨cost, final, hc, output, ho, hr, hm, hone, ht, ha⟩ :=
    WordRAM.Spec.completes (loop_spec input i s.Memory 0 0) hp
  refine ⟨output, cost, final.machine, hc, ho, hr, hm, hone, ?_, ?_⟩
  · cases output <;> simpa [loopTime] using ht
  · simpa using ha

end Algolean.Algorithms.WordRAM.LinearSearch
