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
    (hfits : input.size ≤ 2 ^ w) :
    RepresentsBoundedSearchInput ⟨input, target⟩ LinearSearch.key LinearSearch.last
      (linearSearchState input target) :=
  ⟨⟨arrayMemory_represents input hfits, by simp [linearSearchState]⟩,
    by simp [linearSearchState, LinearSearch.last, LinearSearch.key],
    by simp [linearSearchState]⟩

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
      Summary input target start n s t cost := by
  induction n generalizing start s with
  | zero => lia
  | succ n ih =>
    have hstart : start < input.size := by lia
    have hread := hmem.read_of_eq hstart hi
    have hprobe := ofNat_mem_inputRegion input start hstart
    by_cases heq : input[start] = target
    · have hb := body_found s (by simpa [hread, hk] using heq)
      refine ⟨_, _, hb.while_stop ha (by simp), ?_⟩
      suffices ∀ j, start ≤ j → j < start → input[j]? ≠ some target by
        simpa [Summary, hi, Nat.mod_eq_of_lt (hmem.index_lt hstart), hprobe, heq, hstart] using this
      intro j hj hj'
      lia
    · have hmiss : input[start]? ≠ some target := by simpa [hstart] using heq
      by_cases hn0 : n = 0
      · subst n
        have hb := body_last s (by simpa [hread, hk] using heq)
          (by grind only [RepresentsArray.fits, wordAddress_toNat])
        refine ⟨_, _, hb.while_stop ha (by simp), ?_⟩
        simp only [Summary, checked_memory, Finset.singleton_subset_iff, hi, hprobe,
          true_and, checked_flags]
        exact ⟨by grind only, trivial⟩
      · let next := (checked s false true).writeRegister index (BitVec.ofNat w (start + 1))
        have hb : Completes (instructions (body w)) s ⟨4, {BitVec.ofNat w start}⟩ next := by
          simpa only [next, hi, h1, wordAddress_succ] using body_advance s
            (by simpa [hread, hk] using heq)
            (by grind only [RepresentsArray.fits, wordAddress_toNat])
        obtain ⟨cost, t, hr, hs⟩ := ih (start + 1) (by lia) (by lia) next
          (by simpa [next] using hmem) (by simp [next]) (by simp [next, hk])
          (by simp [next, h1]) (by simp [next, hl]) (by simp [next])
        refine ⟨_, t, completes_while_true .ult (body w) ha hb hr, ?_⟩
        simp only [Summary, next, RAMState.writeRegister_memory, checked_memory,
          RAMCost.mk_add] at hs ⊢
        obtain ⟨hm, hp, hs⟩ := hs
        refine ⟨hm, Finset.union_subset (Finset.singleton_subset_iff.mpr hprobe) hp, ?_⟩
        split_ifs at hs ⊢ <;> grind only

/-- Maximum time, attained by a missing key when the word width is positive. -/
def linearSearchTime (n : Nat) : Nat := if n = 0 then 3 else 4 * n + 3

/-- Exact charged time as a function of the represented output. -/
def linearSearchCost (n : Nat) : Option Nat → Nat
  | none => linearSearchTime n
  | some i => 4 * i + 6

@[simp] private def initialized (s : RAMState w 5) : RAMState w 5 :=
  ((s.writeFlag .eq false).writeRegister index 0).writeRegister one 1

private theorem setup_completes (s : RAMState w 5) :
    Completes (instructions (setup w)) s ⟨3, ∅⟩ (initialized s) :=
  ⟨3, by simp [setup, runCode, step]⟩

private theorem search_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s) :
    ∃ cost t, Completes (instructions (linearSearch w)) s cost t ∧
      Search.linearSearch.spec input (searchOutput index t) ∧ t.Memory = s.Memory ∧
      cost.addresses ⊆ inputRegion input.data ∧
      cost.time = linearSearchCost input.data.size (searchOutput index t) := by
  have hkey := hinput.key_eq
  have hlast := hinput.last_eq
  have hactive := hinput.nonempty_eq
  by_cases hn : input.data.size = 0
  · have hr := completes_while_false .ult (body w) (initialized s) (by simp [hactive, hn])
    have hc := (setup_completes s).append hr
    refine ⟨⟨3, ∅⟩ + 0, initialized s, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [linearSearch, instructions_bind] using hc
    · simp only [searchOutput, initialized, RAMState.writeRegister_flags,
        RAMState.writeFlag_flags, ↓reduceIte, Bool.false_eq_true,
        Search.linearSearch_spec_none]
      grind [Array.mem_iff_getElem?]
    · simp
    · simp
    · simp [linearSearchCost, linearSearchTime, searchOutput, hn]
  · obtain ⟨cost, t, hr, hs⟩ := loop_spec input.data input.key input.data.size 0
      (by lia) (by simp) (initialized s)
      (by simpa using hinput.toRepresentsSearchInput.toRepresentsArray)
      (by simp) (by simp [hkey]) (by simp) (by simp [hlast]) (by simp [hactive, hn])
    have hc := (setup_completes s).append hr
    refine ⟨⟨3, ∅⟩ + cost, t, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [linearSearch, instructions_bind] using hc
    all_goals simp only [Summary, initialized, RAMState.writeRegister_memory,
      RAMState.writeFlag_memory, zero_add, Nat.sub_zero] at hs
    · rcases hs with ⟨_, _, hs⟩
      simp only [searchOutput]
      split_ifs at hs ⊢
      · exact ⟨hs.right.left, hs.right.right.left,
          fun j hj => hs.right.right.right.left j (Nat.zero_le j) hj⟩
      · simp only [Search.linearSearch_spec_none]
        grind [Array.mem_iff_getElem?]
    · exact hs.left
    · simpa using hs.right.left
    · rcases hs with ⟨_, _, hs⟩
      simp only [searchOutput, RAMCost.mk_add]
      split_ifs at hs ⊢ <;> simp only [linearSearchCost, linearSearchTime, if_neg hn]
      · lia
      · lia

/-- A successful fuelled execution satisfies the specification, exact time formula, and
memory footprint on every representing state. -/
theorem linearSearch_run_spec (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    let t := final.ram
    let cost := result.tell
    Search.linearSearch.spec input (searchOutput index t) ∧ t.Memory = s.Memory ∧
      cost.addresses ⊆ inputRegion input.data ∧
      cost.time = linearSearchCost input.data.size (searchOutput index t) := by
  obtain ⟨cost, t, hc, hs⟩ := search_spec input s hinput
  obtain ⟨hcost, hstate⟩ := hc.unique (by simpa only [execute_eq_runCode] using hrun)
  simpa only [hcost, hstate] using hs

end Algolean.Algorithms.WordRAM
