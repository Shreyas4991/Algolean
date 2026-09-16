/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Algorithm

/-!
# Shared proofs for linear search

Lemmas about each loop iteration and the complete search, used by the correctness
and complexity proofs.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

@[simp] theorem linearSearchState_represents (input : Array (Word w)) (target : Word w)
    (hfits : input.size < 2 ^ w) :
    RepresentsSizedSearchInput ⟨input, target⟩ LinearSearch.key (linearSearchState input target) :=
  ⟨sizedArrayMemory_represents input hfits, by simp [linearSearchState]⟩

open LinearSearch

attribute [local simp] index key value one last CmpOp.eval BinOp.eval wordAddress_toNat

private def checked (s : RAMState w 5) (found active : Bool) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq found).writeFlag
    .ult active

@[simp, grind =] private theorem checked_memory (s : RAMState w 5) (found active : Bool) :
    (checked s found active).Memory = s.Memory := rfl

@[simp, grind =] private theorem checked_registers (s : RAMState w 5) (found active : Bool)
    (r : Register 5) : (checked s found active).Registers r =
      if r = value then s.Memory (s.Registers index) else s.Registers r := by
  simp [checked]

@[simp, grind =] private theorem checked_flags (s : RAMState w 5) (found active : Bool)
    (op : CmpOp) : (checked s found active).Flags op =
      if op = .ult then active else found := by
  cases op <;> simp [checked]

private theorem body_found (s : RAMState w 5)
    (h : s.Memory (s.Registers index) = s.Registers key) :
    Completes (instructions (body w)) s ⟨3, {s.Registers index}⟩ (checked s true false) :=
  ⟨4, by simp [body, checked, branch, runCode, step, h]⟩

private theorem body_advance (s : RAMState w 5)
    (h : s.Memory (s.Registers index) ≠ s.Registers key)
    (hlt : (s.Registers index).toNat < (s.Registers last).toNat) :
    Completes (instructions (body w)) s ⟨4, {s.Registers index}⟩
      ((checked s false true).writeRegister index (s.Registers index + s.Registers one)) :=
  ⟨6, by simp [body, checked, branch, runCode, step, h, hlt]⟩

private theorem body_last (s : RAMState w 5)
    (h : s.Memory (s.Registers index) ≠ s.Registers key)
    (hlt : ¬(s.Registers index).toNat < (s.Registers last).toNat) :
    Completes (instructions (body w)) s ⟨4, {s.Registers index}⟩ (checked s false false) :=
  ⟨6, by simp [body, checked, branch, runCode, step, h, hlt]⟩

/-- The invariant describes the remaining suffix and the exact cost from its first address. -/
private def Summary (input : Array (Word w)) (target : Word w) (start n : Nat)
    (s t : RAMState w 5) (cost : RAMCost w 5) : Prop :=
  t.Memory = s.Memory ∧ cost.addresses ⊆ inputRegion input ∧
    if t.Flags .eq then
      let i := (t.Registers index).toNat
      start ≤ i ∧ i < start + n ∧ input[i]? = some target ∧
        (∀ j, start ≤ j → j < i → input[j]? ≠ some target) ∧
        cost.time = 4 * (i - start) + 3
    else
      (∀ j, start ≤ j → j < start + n → input[j]? ≠ some target) ∧
        cost.time = 4 * n

private theorem loop_spec (input : Array (Word w)) (target : Word w) (n start : Nat)
    (hn : 0 < n) (hsize : start + n = input.size) (s : RAMState w 5)
    (hmem : RepresentsArray input s.Memory)
    (hi : s.Registers index = BitVec.ofNat w start)
    (hk : s.Registers key = target) (h1 : s.Registers one = 1)
    (hl : s.Registers last = BitVec.ofNat w (input.size - 1)) (ha : s.Flags .ult = true) :
    ∃ cost t, Completes (instructions (whileLoop .ult (body w))) s cost t ∧
      Summary input target start n s t cost ∧ t.Registers one = 1 := by
  induction n generalizing start s with
  | zero => lia
  | succ n ih =>
    have hstart : start < input.size := by lia
    have hread := hmem.read_of_eq hstart hi
    have hprobe := ofNat_mem_inputRegion input start hstart
    by_cases heq : input[start] = target
    · have hb := body_found s (by simpa [hread, hk] using heq)
      refine ⟨_, _, hb.while_stop ha (by simp), ?_, by simp [h1]⟩
      suffices ∀ j, start ≤ j → j < start → input[j]? ≠ some target by
        simpa [Summary, hi, Nat.mod_eq_of_lt (hmem.index_lt hstart), hprobe, heq, hstart] using this
      intro j hj hj'
      lia
    · have hmiss : input[start]? ≠ some target := by simpa [hstart] using heq
      by_cases hn0 : n = 0
      · subst n
        have hb := body_last s (by simpa [hread, hk] using heq)
          (by grind only [RepresentsArray.fits, wordAddress_toNat])
        refine ⟨_, _, hb.while_stop ha (by simp), ?_, by simp [h1]⟩
        simp only [Summary, checked_memory, Finset.singleton_subset_iff, hi, hprobe,
          true_and, checked_flags]
        exact ⟨by grind only, trivial⟩
      · let next := (checked s false true).writeRegister index (BitVec.ofNat w (start + 1))
        have hb : Completes (instructions (body w)) s ⟨4, {BitVec.ofNat w start}⟩ next := by
          simpa only [next, hi, h1, wordAddress_succ] using body_advance s
            (by simpa [hread, hk] using heq)
            (by grind only [RepresentsArray.fits, wordAddress_toNat])
        obtain ⟨cost, t, hr, hs, htone⟩ := ih (start + 1) (by lia) (by lia) next
          (by simpa [next] using hmem) (by simp [next]) (by simp [next, hk])
          (by simp [next, h1]) (by simp [next, hl]) (by simp [next])
        refine ⟨_, t, completes_while_true .ult (body w) ha hb hr, ?_, htone⟩
        simp only [Summary, next, RAMState.writeRegister_memory, checked_memory,
          RAMCost.mk_add] at hs ⊢
        obtain ⟨hm, hp, hs⟩ := hs
        refine ⟨hm, Finset.union_subset (Finset.singleton_subset_iff.mpr hprobe) hp, ?_⟩
        split_ifs at hs ⊢ <;> grind only

/-- Maximum time, attained by a missing key when the word width is positive. -/
def linearSearchTime (n : Nat) : Nat := 4 * n + 7

/-- Exact time, including setup and conversion to a zero-based result. -/
def linearSearchCost (n : Nat) : Option Nat → Nat
  | none => linearSearchTime n
  | some i => 4 * i + 10

private def initialized (n : Nat) (s : RAMState w 5) : RAMState w 5 :=
  ⟨s.Memory, fun r => if r = index then 1 else if r = one then 1
    else if r = last then BitVec.ofNat w n else s.Registers r,
    fun op => if op = .ult then decide (n ≠ 0) else false⟩

attribute [local simp] initialized

private theorem setup_completes (input : Search.Input (Word w)) (s : RAMState w 5)
    (hi : RepresentsSizedSearchInput input key s) :
    Completes (instructions (setup w)) s ⟨6, {0}⟩ (initialized input.data.size s) := by
  have hh := hi.header
  have hn := hi.size_lt
  refine ⟨6, ?_⟩
  simp only [setup, index, Fin.isValue, BitVec.ofNat_eq_ofNat, last, one, instructions_bind,
    instructions_lift,
    List.cons_append, List.nil_append, runCode, step, RAMState.writeFlag,
    RAMState.writeRegister, Function.update,
    ↓reduceDIte, hh, CmpOp.eval, Fin.reduceEq, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.mod_eq_of_lt hn,
    Nat.pos_iff_ne_zero, ne_eq, Array.size_eq_zero_iff, decide_not, runCode_nil,
    RAMCost.mk_add, Finset.empty_union,
    Option.pure_def, Option.bind_eq_bind, Option.bind_some, RAMCost.zero_time, add_zero,
    RAMCost.zero_addresses,
    Nat.reduceAdd, Finset.singleton_union, insert_empty_eq, initialized, Bool.if_false_right,
    Option.some.injEq,
    Prod.mk.injEq, ExecutionState.mk.injEq, RAMState.mk.injEq, true_and, and_true]
  constructor
  · funext r
    simp only [Function.update_apply]
    split_ifs <;> simp_all only [Fin.reduceEq]
  · funext op
    cases op <;> simp

private def finished (s : RAMState w 5) : RAMState w 5 :=
  if s.Flags .eq then s.writeRegister index (s.Registers index - 1) else s

private theorem finish_completes (s : RAMState w 5) (h1 : s.Registers one = 1) :
    Completes (instructions (finish w)) s ⟨1, ∅⟩ (finished s) := by
  refine ⟨2, ?_⟩
  cases hf : s.Flags .eq <;> simp [finish, finished, branch, runCode, step, hf, h1]

@[simp] private theorem finished_memory (s : RAMState w 5) : (finished s).Memory = s.Memory := by
  simp [finished]; split <;> rfl

@[simp] private theorem finished_flags (s : RAMState w 5) (op : CmpOp) :
    (finished s).Flags op = s.Flags op := by
  simp [finished]; split <;> rfl

private theorem finished_output (s : RAMState w 5) (hf : s.Flags .eq = true)
    (hp : 0 < (s.Registers index).toNat) :
    searchOutput index (finished s) = some ((s.Registers index).toNat - 1) := by
  simp only [finished, hf, ↓reduceIte, searchOutput, RAMState.writeRegister_flags,
    RAMState.writeRegister_registers]
  rw [word_pred_toNat _ hp]

private theorem search_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsSizedSearchInput input key s) :
    ∃ cost t, Completes (instructions (linearSearch w)) s cost t ∧
      Search.linearSearch.spec input (searchOutput index t) ∧ t.Memory = s.Memory ∧
      cost.addresses ⊆ sizedInputRegion input.data ∧
      cost.time = linearSearchCost input.data.size (searchOutput index t) := by
  have hkey := hinput.key_eq
  by_cases hn : input.data.size = 0
  · have hr := completes_while_false .ult (body w) (initialized input.data.size s) (by simp [hn])
    have hc := (setup_completes input s hinput).append
      (hr.append (finish_completes _ (by simp)))
    refine ⟨⟨6, {0}⟩ + (0 + ⟨1, ∅⟩), finished (initialized input.data.size s),
      ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [linearSearch, instructions_bind] using hc
    · simp [finished, searchOutput, Search.linearSearch_spec_none,
        Array.eq_empty_of_size_eq_zero hn]
    · simp
    · simp [RAMCost.mk_add]
    · simp [finished, searchOutput, linearSearchCost, linearSearchTime, hn, RAMCost.mk_add]
  · obtain ⟨cost, t, hr, hs, htone⟩ := loop_spec (withSize input.data) input.key input.data.size 1
      (by lia) (by simp [Nat.add_comm]) (initialized input.data.size s)
      (by simpa using hinput.toRepresentsArray)
      (by simp) (by simp [hkey]) (by simp) (by simp) (by simp [hn])
    have hc := (setup_completes input s hinput).append (hr.append (finish_completes t htone))
    refine ⟨⟨6, {0}⟩ + (cost + ⟨1, ∅⟩), finished t, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [linearSearch, instructions_bind] using hc
    all_goals simp only [Summary, initialized] at hs
    · obtain ⟨_, _, hs⟩ := hs
      cases hf : t.Flags .eq with
      | false =>
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hs
        simp only [searchOutput, finished_flags, hf, Bool.false_eq_true, ↓reduceIte,
          Search.linearSearch_spec_none]
        rw [Array.mem_iff_getElem?]
        rintro ⟨i, hi⟩
        have hib : i < input.data.size := by
          exact Array.getElem?_eq_some_iff.mp hi |>.choose
        exact hs.left (i + 1) (by lia) (by lia) (by simpa using hi)
      | true =>
        simp only [hf, ↓reduceIte] at hs
        rw [finished_output t hf (by lia)]
        refine ⟨by lia, ?_, ?_⟩
        · rw [← withSize_getElem?_succ, Nat.sub_add_cancel (by lia : 1 ≤ (t.Registers index).toNat)]
          exact hs.right.right.left
        · intro j hj
          simpa using hs.right.right.right.left (j + 1) (by lia) (by lia)
    · simpa using hs.left
    · simpa [RAMCost.add_addresses, sizedInputRegion] using
        Finset.insert_subset (zero_mem_sizedInputRegion input.data) hs.right.left
    · obtain ⟨_, _, hs⟩ := hs
      cases hf : t.Flags .eq with
      | false =>
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hs
        simp [searchOutput, hf, linearSearchCost, linearSearchTime, RAMCost.mk_add, hs.right]
        lia
      | true =>
        simp only [hf, ↓reduceIte] at hs
        rw [finished_output t hf (by lia)]
        simp only [linearSearchCost, RAMCost.add_time]
        lia

/-- A successful fuelled execution satisfies the specification, exact time formula, and
memory footprint on every representing state. -/
theorem linearSearch_run_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsSizedSearchInput input key s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    let t := final.ram
    let cost := result.tell
    Search.linearSearch.spec input (searchOutput index t) ∧ t.Memory = s.Memory ∧
      cost.addresses ⊆ sizedInputRegion input.data ∧
      cost.time = linearSearchCost input.data.size (searchOutput index t) := by
  obtain ⟨cost, t, hc, hs⟩ := search_spec input s hinput
  obtain ⟨hcost, hstate⟩ := hc.unique (by simpa only [execute_eq_runCode] using hrun)
  simpa only [hcost, hstate] using hs

end Algolean.Algorithms.WordRAM
