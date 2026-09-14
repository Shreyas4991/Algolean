/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-!
# Linear search with four word-RAM registers

The index, key, loaded value, and constant one occupy four registers. No computed word escapes
into a program continuation. A successful search returns the identifier of the index register;
the answer is read from that register in the final machine state.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Array layout used by the initial machine state. -/
def arrayMemory (input : Array (BitVec w)) : Memory w :=
  fun addr => input[addr.toNat]?.getD 0

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
def loop : Nat → Prog (WordRAM w 4) (Option (Register 4))
  | 0 => pure none
  | n + 1 => do
    load (w := w) value index
    let found : Bool ← cmp (w := w) .eq value key
    if found then return some index
    binop (w := w) .add index index one
    loop n

end LinearSearch

/-- Search `n` input cells. The caller supplies the key in `LinearSearch.key`.
Two initial instructions set the index to zero and the increment register to one. -/
def linearSearch (w n : Nat) : Prog (WordRAM w 4) (Option (Register 4)) := do
  set (w := w) LinearSearch.index 0
  set (w := w) LinearSearch.one 1
  LinearSearch.loop n

/-- Input memory and key register, supplied before execution. -/
def linearSearchState (input : Array (BitVec w)) (key : Word w) : RAMState w 4 :=
  ⟨arrayMemory input, fun r => if r = LinearSearch.key then key else 0⟩

section CorrectnessAndComplexity

open LinearSearch

attribute [local simp] loop evalQuery queryProbes CmpOp.eval BinOp.eval index key value one

private theorem loop_memory (n : Nat) (s : RAMState w 4) :
    (((loop n).runM timeAndSpaceCost).run s).snd.Memory = s.Memory := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all

private theorem loop_time_le (n : Nat) (s : RAMState w 4) :
    (((loop n).runM timeAndSpaceCost).run s).fst.tell.time ≤ 3 * n := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all <;> grind

private theorem loop_time_of_none (n : Nat) (s : RAMState w 4)
    (hnone : (((loop n).runM timeAndSpaceCost).run s).fst.ret = none) :
    (((loop n).runM timeAndSpaceCost).run s).fst.tell.time = 3 * n := by
  induction n generalizing s <;> simp_all
  split_ifs <;> simp_all
  grind

@[grind =] private theorem wordAddress_toNat (i : Nat) (hi : i < 2 ^ w) :
    (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt hi

@[simp, grind =] private theorem arrayMemory_ofNat (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

@[grind =] private theorem wordAddress_succ (i : Nat) :
    BitVec.ofNat w i + 1 = BitVec.ofNat w (i + 1) := (BitVec.ofNat_add i 1).symm

/-- The address points to the first occurrence of the key. -/
def IsFirstMatch (input : Array (BitVec w)) (key : BitVec w) (addr : Word w) : Prop :=
  addr.toNat < input.size ∧ input[addr.toNat]? = some key ∧
    ∀ i, i < addr.toNat → input[i]? ≠ some key

private theorem loop_correct_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (s : RAMState w 4) (hmem : s.Memory = arrayMemory input)
    (hindex : s.Registers index = BitVec.ofNat w start) (hkey : s.Registers key = target)
    (hone : s.Registers one = 1) (r : Register 4)
    (hresult : (((loop n).runM timeAndSpaceCost).run s).fst.ret = some r) :
    let addr := (((loop n).runM timeAndSpaceCost).run s).snd.Registers r
    r = index ∧ start ≤ addr.toNat ∧ addr.toNat < start + n ∧
      input[addr.toNat]? = some target ∧
      ∀ i, start ≤ i → i < addr.toNat → input[i]? ≠ some target := by
  induction n generalizing start s with
  | zero => simp at hresult
  | succ n ih =>
    have hi : start < input.size := by lia
    have ht := ih (start + 1) (by lia)
      ((s.writeRegister value input[start]).writeRegister index (BitVec.ofNat w (start + 1)))
      (by simp [hmem]) (by simp) (by simp [hkey]) (by simp [hone])
    clear ih
    simp_all
    split_ifs at hresult ⊢ <;> grind

private theorem loop_correct_not_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (s : RAMState w 4) (hmem : s.Memory = arrayMemory input)
    (hindex : s.Registers index = BitVec.ofNat w start) (hkey : s.Registers key = target)
    (hone : s.Registers one = 1)
    (hresult : (((loop n).runM timeAndSpaceCost).run s).fst.ret = none) :
    ∀ i, start ≤ i → i < start + n → input[i]? ≠ some target := by
  induction n generalizing start s with
  | zero => lia
  | succ n ih =>
    have hi : start < input.size := by lia
    have ht := ih (start + 1) (by lia)
      ((s.writeRegister value input[start]).writeRegister index (BitVec.ofNat w (start + 1)))
      (by simp [hmem]) (by simp) (by simp [hkey]) (by simp [hone])
    clear ih
    simp_all
    split_ifs at hresult ⊢
    grind

private def initialized (s : RAMState w 4) : RAMState w 4 :=
  (s.writeRegister index 0).writeRegister one 1

@[simp, grind =] private theorem linearSearch_run (n : Nat) (s : RAMState w 4) :
    ((linearSearch w n).runM timeAndSpaceCost).run s =
      let rest := ((loop n).runM timeAndSpaceCost).run (initialized s)
      ((⟨rest.fst.ret, ⟨2, ∅⟩ + rest.fst.tell⟩ :
        AddWriter (RAMCost w 4) (Option (Register 4))), rest.snd) := by
  simp [linearSearch, initialized, ← Nat.add_assoc]

/-- The returned register holds the first match; failure certifies absence of the key. -/
theorem linearSearch_correct (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    let result := ((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)
    match result.fst.ret with
    | none => target ∉ input
    | some r => r = index ∧ IsFirstMatch input target (result.snd.Registers r) := by
  simp only [linearSearch_run]
  split
  · rename_i hresult
    have h := loop_correct_not_found input target hfits input.size 0 (by lia)
      (initialized (linearSearchState input target)) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simp [initialized, linearSearchState])
      (by simp [initialized]) hresult
    grind [Array.mem_iff_getElem?]
  · rename_i r hresult
    have h := loop_correct_found input target hfits input.size 0 (by lia)
      (initialized (linearSearchState input target)) (by simp [initialized, linearSearchState])
      (by simp [initialized]) (by simp [initialized, linearSearchState])
      (by simp [initialized]) r hresult
    simpa [IsFirstMatch] using h

/-- The search fails exactly when the key is absent. -/
theorem linearSearch_none_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.ret = none ↔ target ∉ input := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Success identifies the index register, whose final contents are the first matching address. -/
theorem linearSearch_some_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (r : Register 4) :
    let result := ((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)
    result.fst.ret = some r ↔ r = index ∧ IsFirstMatch input target (result.snd.Registers r) := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Register operations and loads preserve the entire memory. -/
theorem linearSearch_memory (n : Nat) (s : RAMState w 4) :
    (((linearSearch w n).runM timeAndSpaceCost).run s).snd.Memory = s.Memory := by
  simpa [initialized] using loop_memory n (initialized s)

/-- Two setup instructions and at most three queries per input element. -/
theorem linearSearch_time_le (n : Nat) (s : RAMState w 4) :
    (((linearSearch w n).runM timeAndSpaceCost).run s).fst.tell.time ≤ 3 * n + 2 := by
  simpa [Nat.add_comm] using Nat.add_le_add_left (loop_time_le n (initialized s)) 2

/-- A missing key forces all `n` iterations, in addition to two setup instructions. -/
theorem linearSearch_time_of_not_mem (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hnot : target ∉ input) :
    (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.time = 3 * input.size + 2 := by
  have ht := loop_time_of_none input.size (initialized (linearSearchState input target))
    (by simpa using (linearSearch_none_iff input target hfits).mpr hnot)
  simp [ht, Nat.add_comm]

private theorem loop_time_of_some (n start : Nat) (hbound : start + n ≤ 2 ^ w)
    (s : RAMState w 4) (hindex : s.Registers index = BitVec.ofNat w start)
    (hone : s.Registers one = 1) (r : Register 4)
    (hfound : (((loop n).runM timeAndSpaceCost).run s).fst.ret = some r) :
    (((loop n).runM timeAndSpaceCost).run s).fst.tell.time + 3 * start =
      3 * ((((loop n).runM timeAndSpaceCost).run s).snd.Registers r).toNat + 2 := by
  induction n generalizing start s with
  | zero => simp at hfound
  | succ n ih =>
    have ht := ih (start + 1) (by lia)
      ((s.writeRegister value (s.Memory (BitVec.ofNat w start))).writeRegister index
        (BitVec.ofNat w (start + 1))) (by simp) (by simp [hone])
    clear ih
    simp_all
    split_ifs at hfound ⊢ <;> grind

/-- A first match at address `i` costs `3 * i + 4`, including register initialization. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (r : Register 4)
    (hfound : (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.ret = some r) :
    let result := ((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)
    let address := result.snd.Registers r
    result.fst.tell.time = 3 * address.toNat + 4 := by
  have ht := loop_time_of_some input.size 0 (by lia)
    (initialized (linearSearchState input target)) (by simp [initialized])
    (by simp [initialized]) r (by simpa using hfound)
  simp_all only [linearSearch_run, RAMCost.mk_add, Finset.empty_union, mul_zero, add_zero]
  lia

/-- Memory cells occupied by the input array. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

@[simp, grind ←] theorem ofNat_mem_inputRegion (input : Array (BitVec w))
    (i : Nat) (hi : i < input.size) : BitVec.ofNat w i ∈ inputRegion input :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

private theorem loop_addresses_subset (input : Array (BitVec w)) (n start : Nat)
    (hbound : start + n ≤ input.size) (s : RAMState w 4)
    (hindex : s.Registers index = BitVec.ofNat w start) (hone : s.Registers one = 1) :
    (((loop n).runM timeAndSpaceCost).run s).fst.tell.addresses ⊆ inputRegion input := by
  induction n generalizing start s with
  | zero => simp
  | succ n ih =>
    have hm := ofNat_mem_inputRegion input start (by lia)
    have ht := ih (start + 1) (by lia)
      ((s.writeRegister value (s.Memory (BitVec.ofNat w start))).writeRegister index
        (BitVec.ofNat w (start + 1))) (by simp) (by simp [hone])
    clear ih
    simp_all
    split_ifs <;> grind [Finset.insert_subset_iff]

/-- The memory probes are confined to the input; all working words are in four registers. -/
theorem linearSearch_addresses_subset (input : Array (BitVec w)) (target : Word w) :
    (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.addresses ⊆ inputRegion input := by
  simpa using loop_addresses_subset input input.size 0 (by lia)
    (initialized (linearSearchState input target)) (by simp [initialized])
    (by simp [initialized])

/-- Auxiliary space is four register words, with no memory probes outside the input. -/
theorem linearSearch_auxiliarySpace (input : Array (BitVec w)) (target : Word w) :
    (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.auxiliarySpace
        (inputRegion input) = 4 := by
  simp only [RAMCost.auxiliarySpace,
    Finset.sdiff_eq_empty_iff_subset.mpr (linearSearch_addresses_subset input target),
    Finset.card_empty, Nat.add_zero]

/-- A fitting array occupies exactly one distinct cell per element. -/
theorem inputRegion_card (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w) :
    (inputRegion input).card = input.size := by
  unfold inputRegion
  rw [Finset.card_image_of_injOn (by
    intro i hi j hj heq
    have := congrArg BitVec.toNat heq
    grind), Finset.card_range]

/-- Total space comprises the array and four register words. -/
theorem linearSearch_totalSpace (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    (((linearSearch w input.size).runM timeAndSpaceCost).run
      (linearSearchState input target)).fst.tell.totalSpace
        (inputRegion input) = input.size + 4 := by
  simp only [RAMCost.totalSpace,
    Finset.union_eq_right.mpr (linearSearch_addresses_subset input target),
    inputRegion_card input hfits, Nat.add_comm]

/-- Every representable length has a worst-case instance, for a positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    (((linearSearch w n).runM timeAndSpaceCost).run
      (linearSearchState (Array.replicate n (0 : BitVec w)) 1)).fst.tell.time =
        3 * n + 2 := by
  simpa using linearSearch_time_of_not_mem (Array.replicate n (0 : BitVec w)) 1
    (by simpa using hn) (by simp [ne_of_gt hw])

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
