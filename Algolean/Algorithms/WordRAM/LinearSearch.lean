/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic

/-!
# Linear search with four word-RAM registers

The index, key, loaded value, and constant one occupy four registers. No computed word escapes
into a program continuation. The equality flag records success;
the answer is read from the index register in the final machine state.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

namespace LinearSearch

/-- Current address, and the result register on success. -/
abbrev index : Register 4 := 0
/-- Search key supplied by the initial machine state. -/
abbrev key : Register 4 := 1
/-- Scratch register for the most recently loaded word. -/
abbrev value : Register 4 := 2
/-- Constant one used by the index increment instruction. -/
abbrev one : Register 4 := 3

/-- Only control flow escapes the register machine. -/
def loop : Nat → Prog (WordRAM w 4) Unit
  | 0 => pure ()
  | n + 1 => do
    load (w := w) value index
    cmp (w := w) .eq value key
    branch .eq (pure ()) (do
      binop (w := w) .add index index one
      loop n)

end LinearSearch

/-- Search `n` input cells. The caller supplies the key in `LinearSearch.key`.
Three initial instructions clear the result flag and initialize the index and increment
registers. -/
def linearSearch (w n : Nat) : Prog (WordRAM w 4) Unit := do
  clearFlag (w := w) (k := 4) .eq
  set (w := w) LinearSearch.index 0
  set (w := w) LinearSearch.one 1
  LinearSearch.loop n

/-- Input memory and key register, supplied before execution. -/
def linearSearchState (input : Array (BitVec w)) (key : Word w) : RAMState w 4 :=
  ⟨arrayMemory input, fun r => if r = LinearSearch.key then key else 0, fun _ => false⟩

section CorrectnessAndComplexity

open LinearSearch

attribute [local simp] loop runQuery CmpOp.eval BinOp.eval index key value one wordAddress_toNat

private theorem loop_memory (n : Nat) (s : RAMState w 4) :
    (((loop n).runStateM timeAndSpaceCost).run s).snd.Memory = s.Memory := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all

private theorem loop_time_le (n : Nat) (s : RAMState w 4) :
    (((loop n).runStateM timeAndSpaceCost).run s).fst.tell.time ≤ 3 * n := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all <;> grind

private theorem loop_time_of_none (n : Nat) (s : RAMState w 4)
    (hnone : (((loop n).runStateM timeAndSpaceCost).run s).snd.Flags .eq = false) :
    (((loop n).runStateM timeAndSpaceCost).run s).fst.tell.time = 3 * n := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all
  grind

/-- The address points to the first occurrence of the key. -/
def IsFirstMatch (input : Array (BitVec w)) (key : BitVec w) (addr : Word w) : Prop :=
  addr.toNat < input.size ∧ input[addr.toNat]? = some key ∧
    ∀ i, i < addr.toNat → input[i]? ≠ some key

private theorem loop_correct_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (s : RAMState w 4) (hmem : s.Memory = arrayMemory input)
    (hindex : s.Registers index = BitVec.ofNat w start) (hkey : s.Registers key = target)
    (hone : s.Registers one = 1) (hflag : s.Flags .eq = false)
    (hresult : (((loop n).runStateM timeAndSpaceCost).run s).snd.Flags .eq = true) :
    let addr := (((loop n).runStateM timeAndSpaceCost).run s).snd.Registers index
    start ≤ addr.toNat ∧ addr.toNat < start + n ∧
      input[addr.toNat]? = some target ∧
      ∀ i, start ≤ i → i < addr.toNat → input[i]? ≠ some target := by
  induction n generalizing start s with
  | zero => simp_all
  | succ n ih =>
    have hi : start < input.size := by lia
    have hstart : start % 2 ^ w = start := Nat.mod_eq_of_lt (by lia)
    have ht := ih (start + 1) (by lia)
      (((s.writeRegister value input[start]).writeFlag .eq false).writeRegister index
        (BitVec.ofNat w (start + 1)))
      (by simp [hmem]) (by simp) (by simp [hkey]) (by simp [hone]) (by simp)
    clear ih
    simp_all
    split_ifs at hresult ⊢ <;> simp_all
    grind

private theorem loop_correct_not_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (s : RAMState w 4) (hmem : s.Memory = arrayMemory input)
    (hindex : s.Registers index = BitVec.ofNat w start) (hkey : s.Registers key = target)
    (hone : s.Registers one = 1)
    (hresult : (((loop n).runStateM timeAndSpaceCost).run s).snd.Flags .eq = false) :
    ∀ i, start ≤ i → i < start + n → input[i]? ≠ some target := by
  induction n generalizing start s with
  | zero => lia
  | succ n ih =>
    have hi : start < input.size := by lia
    have hstart : start % 2 ^ w = start := Nat.mod_eq_of_lt (by lia)
    have ht := ih (start + 1) (by lia)
      (((s.writeRegister value input[start]).writeFlag .eq false).writeRegister index
        (BitVec.ofNat w (start + 1)))
      (by simp [hmem]) (by simp) (by simp [hkey]) (by simp [hone])
    clear ih
    simp_all
    split_ifs at hresult ⊢ <;> simp_all
    grind

private def initialized (s : RAMState w 4) : RAMState w 4 :=
  ((s.writeFlag .eq false).writeRegister index 0).writeRegister one 1

@[simp, grind =] private theorem linearSearch_run (n : Nat) (s : RAMState w 4) :
    ((linearSearch w n).runStateM timeAndSpaceCost).run s =
      let rest := ((loop n).runStateM timeAndSpaceCost).run (initialized s)
      ((⟨rest.fst.ret, ⟨3, ∅⟩ + rest.fst.tell⟩ :
        AddWriter (RAMCost w 4) Unit), rest.snd) := by
  simp [linearSearch, initialized, ← Nat.add_assoc]

/-- The equality flag indicates success, with the first matching address in the index register. -/
theorem linearSearch_correct (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    let result := ((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)
    if result.snd.Flags .eq then IsFirstMatch input target (result.snd.Registers index)
    else target ∉ input := by
  simp only [linearSearch_run]
  split_ifs with hresult
  · have h := loop_correct_found input target hfits input.size 0 (by lia)
      (initialized (linearSearchState input target)) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simp [initialized]) hresult
    simpa [IsFirstMatch] using h
  · have h := loop_correct_not_found input target hfits input.size 0 (by lia)
      (initialized (linearSearchState input target)) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simpa using hresult)
    grind [Array.mem_iff_getElem?]

/-- A cleared equality flag certifies absence of the key. -/
theorem linearSearch_none_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    let result := ((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)
    result.snd.Flags .eq = false ↔ target ∉ input := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- A set equality flag certifies the first matching address in the index register. -/
theorem linearSearch_some_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    let result := ((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)
    result.snd.Flags .eq = true ↔ IsFirstMatch input target (result.snd.Registers index) := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Register operations and loads preserve the entire memory. -/
theorem linearSearch_memory (n : Nat) (s : RAMState w 4) :
    (((linearSearch w n).runStateM timeAndSpaceCost).run s).snd.Memory = s.Memory := by
  simpa [initialized] using loop_memory n (initialized s)

/-- Three setup instructions and at most three queries per input element. -/
theorem linearSearch_time_le (n : Nat) (s : RAMState w 4) :
    (((linearSearch w n).runStateM timeAndSpaceCost).run s).fst.tell.time ≤ 3 * n + 3 := by
  simpa [Nat.add_comm] using Nat.add_le_add_left (loop_time_le n (initialized s)) 3

/-- A missing key forces all `n` iterations, in addition to three setup instructions. -/
theorem linearSearch_time_of_not_mem (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hnot : target ∉ input) :
    (((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.time = 3 * input.size + 3 := by
  have ht := loop_time_of_none input.size (initialized (linearSearchState input target))
    (by simpa using (linearSearch_none_iff input target hfits).mpr hnot)
  simp [ht, Nat.add_comm]

private theorem loop_time_of_some (n start : Nat) (hbound : start + n ≤ 2 ^ w)
    (s : RAMState w 4) (hindex : s.Registers index = BitVec.ofNat w start)
    (hone : s.Registers one = 1) (hflag : s.Flags .eq = false)
    (hfound : (((loop n).runStateM timeAndSpaceCost).run s).snd.Flags .eq = true) :
    (((loop n).runStateM timeAndSpaceCost).run s).fst.tell.time + 3 * start =
      3 * ((((loop n).runStateM timeAndSpaceCost).run s).snd.Registers index).toNat + 2 := by
  induction n generalizing start s with
  | zero => simp_all
  | succ n ih =>
    have hstart : start % 2 ^ w = start := Nat.mod_eq_of_lt (by lia)
    have ht := ih (start + 1) (by lia)
      (((s.writeRegister value (s.Memory (BitVec.ofNat w start))).writeFlag .eq false).writeRegister
        index (BitVec.ofNat w (start + 1))) (by simp) (by simp [hone]) (by simp)
    clear ih
    simp_all
    split_ifs at hfound ⊢ <;> simp_all <;> grind

/-- A first match at address `i` costs `3 * i + 5`, including register initialization. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w)
    (hfound : (((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)).snd.Flags .eq = true) :
    let result := ((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)
    let address := result.snd.Registers index
    result.fst.tell.time = 3 * address.toNat + 5 := by
  have ht := loop_time_of_some input.size 0 (by lia)
    (initialized (linearSearchState input target)) (by simp [initialized])
    (by simp [initialized]) (by simp [initialized]) (by simpa using hfound)
  simp_all only [linearSearch_run, RAMCost.mk_add, Finset.empty_union, mul_zero, add_zero]
  lia

private theorem loop_addresses_subset (input : Array (BitVec w)) (n start : Nat)
    (hbound : start + n ≤ input.size) (s : RAMState w 4)
    (hindex : s.Registers index = BitVec.ofNat w start) (hone : s.Registers one = 1) :
    (((loop n).runStateM timeAndSpaceCost).run s).fst.tell.addresses ⊆ inputRegion input := by
  induction n generalizing start s with
  | zero => simp
  | succ n ih =>
    have hm := ofNat_mem_inputRegion input start (by lia)
    have ht := ih (start + 1) (by lia)
      (((s.writeRegister value (s.Memory (BitVec.ofNat w start))).writeFlag .eq false).writeRegister
        index (BitVec.ofNat w (start + 1))) (by simp) (by simp [hone])
    clear ih
    simp_all
    split_ifs <;> grind [Finset.insert_subset_iff]

/-- The memory probes are confined to the input; all working words are in four registers. -/
theorem linearSearch_addresses_subset (input : Array (BitVec w)) (target : Word w) :
    (((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.addresses ⊆ inputRegion input := by
  simpa using loop_addresses_subset input input.size 0 (by lia)
    (initialized (linearSearchState input target)) (by simp [initialized])
    (by simp [initialized])

/-- Auxiliary memory usage is zero: no cells outside the input are probed or written to. -/
theorem linearSearch_auxiliarySpace (input : Array (BitVec w)) (target : Word w) :
    (((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.auxiliarySpace
        (inputRegion input) = 0 := by
  simp only [RAMCost.auxiliarySpace,
    Finset.sdiff_eq_empty_iff_subset.mpr (linearSearch_addresses_subset input target),
    Finset.card_empty]

/-- Total memory usage is the size of the input array. -/
theorem linearSearch_totalSpace (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    (((linearSearch w input.size).runStateM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.totalSpace
        (inputRegion input) = input.size := by
  simp only [RAMCost.totalSpace,
    Finset.union_eq_right.mpr (linearSearch_addresses_subset input target),
    inputRegion_card input hfits]

/-- Every representable length has a worst-case instance, for a positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    (((linearSearch w n).runStateM timeAndSpaceCost).run
      (linearSearchState (Array.replicate n (0 : BitVec w)) 1)).fst.tell.time =
        3 * n + 3 := by
  simpa using linearSearch_time_of_not_mem (Array.replicate n (0 : BitVec w)) 1
    (by simpa using hn) (by simp [ne_of_gt hw])

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
