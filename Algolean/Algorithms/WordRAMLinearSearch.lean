/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-!
# Linear search on the word RAM

`linearSearch` searches an array laid out in consecutive memory cells by `arrayMemory`.
It returns the first matching address and preserves memory. The correctness and complexity section
proves the result specification, exact successful and unsuccessful query counts, a tight linear
worst-case time bound, and zero auxiliary RAM footprint. Total space including the input equals
the input size.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Lay out an array in consecutive RAM cells starting at address zero, with zero elsewhere.
This specifies the initial memory supplied to the interpreter; it is not part of the search cost. -/
def arrayMemory (input : Array (BitVec w)) : Memory w :=
  fun addr => input[addr.toNat]?.getD 0

/-- Search the array stored in `arrayMemory input`, returning the first matching address.
The size bound ensures every input element has a distinct word-sized address. The program uses
only the array's length; element access, key comparison, and address arithmetic are queries.

A match at index `i` costs `3 * i + 2` queries and touches `i + 1` cells. An unsuccessful search
costs `3 * input.size` queries and touches every input cell. The final address increment on a miss
may wrap when the array fills the address space, but no further load is performed.
-/
def linearSearch (input : Array (BitVec w)) (key : BitVec w)
    (_fits : input.size ≤ 2 ^ w) : Prog (WordRAM w) (Option (Word w)) := do
  let mut addr : Word w := 0
  for _ in List.range input.size do
    let value : Word w ← load addr
    let found : Bool ← cmp .eq value key
    if found then
      return some addr
    addr ← binop .add addr 1
  return none

/-!
## Correctness and complexity of linear search

The proofs apply to every input fitting in the address space, including a full address space.
They preserve the original `for` loop by proving it equal to a recursive loop for induction.
The final results establish first-match correctness, a tight linear time bound, zero auxiliary
RAM footprint, and total space equal to the input length. The word width may grow with input size.
-/

section CorrectnessAndComplexity

open Cslib

/-- Recursive form of the search loop, used only to prove properties of the `for` loop. -/
private def searchLoop (key : Word w) : Nat → Word w → Prog (WordRAM w) (Option (Word w))
  | 0, _ => pure none
  | n + 1, addr => do
    let value : Word w ← load addr
    let found : Bool ← cmp .eq value key
    if found then
      return some addr
    let next : Word w ← binop .add addr 1
    searchLoop key n next

/-- The elaborated `for` loop with an arbitrary list of iterations and starting address. -/
private def searchFor (key : Word w) (steps : List Nat) (addr : Word w) :
    Prog (WordRAM w) (Option (Word w)) := do
  let mut addr := addr
  for _ in steps do
    let value : Word w ← load addr
    let found : Bool ← cmp .eq value key
    if found then
      return some addr
    addr ← binop .add addr 1
  return none

private theorem searchFor_eq_searchLoop (key : Word w) (steps : List Nat) (addr : Word w) :
    searchFor key steps addr = searchLoop key steps.length addr := by
  induction steps generalizing addr with
  | nil => simp [searchFor, searchLoop]
  | cons x xs ih =>
    simp only [searchFor, List.forIn_cons, List.length_cons, searchLoop, bind_assoc]
    congr 1
    funext value
    congr 1
    funext found
    cases found <;> simp only [Bool.false_eq_true, ↓reduceIte, BitVec.ofNat_eq_ofNat,
      bind_pure_comp, bind_map_left, pure_bind]
    congr 1
    funext next
    exact ih next

private theorem linearSearch_eq_searchLoop (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    linearSearch input key hfits = searchLoop key input.size 0 := by
  change searchFor key (List.range input.size) 0 = _
  rw [searchFor_eq_searchLoop, List.length_range]

private theorem searchLoop_eval_zero (key : Word w) (addr : Word w) (mem : Memory w) :
    (searchLoop key 0 addr).evalM timeAndSpaceCost mem = (none (α := Word w), mem) := rfl

private theorem searchLoop_eval_succ (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) :
    (searchLoop key (n + 1) addr).evalM timeAndSpaceCost mem =
      if mem addr = key then (some addr, mem)
      else (searchLoop key n (addr + 1)).evalM timeAndSpaceCost mem := by
  change Prog.evalM (if decide (mem addr = key) then pure (some addr) else do
      let next : Word w ← binop .add addr 1
      searchLoop key n next : Prog (WordRAM w) (Option (Word w))) timeAndSpaceCost mem = _
  by_cases h : mem addr = key <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

private theorem searchLoop_cost_zero (key : Word w) (addr : Word w) (mem : Memory w) :
    (searchLoop key 0 addr).costM timeAndSpaceCost mem = ((0 : RAMCost w), mem) := rfl

private theorem searchLoop_cost_succ (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) :
    (searchLoop key (n + 1) addr).costM timeAndSpaceCost mem =
      if mem addr = key then (⟨2, {addr}⟩, mem)
      else
        let rest := (searchLoop key n (addr + 1)).costM timeAndSpaceCost mem
        (⟨3, {addr}⟩ + rest.1, rest.2) := by
  change (let rest := Prog.costM (if decide (mem addr = key) then pure (some addr) else do
      let next : Word w ← binop .add addr 1
      searchLoop key n next : Prog (WordRAM w) (Option (Word w))) timeAndSpaceCost mem
    ((⟨1, {addr}⟩ : RAMCost w) + (⟨1, ∅⟩ + rest.1), rest.2)) = _
  by_cases h : mem addr = key
  · simp only [h, decide_true, ↓reduceIte]
    change ((⟨1, {addr}⟩ : RAMCost w) + (⟨1, ∅⟩ + 0), mem) = (⟨2, {addr}⟩, mem)
    congr 1
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply Prod.ext
    · change (⟨1, {addr}⟩ + (⟨1, ∅⟩ + (⟨1, ∅⟩ +
          ((searchLoop key n (addr + 1)).costM timeAndSpaceCost mem).1)) : RAMCost w) = _
      ext <;> simp [← Nat.add_assoc]
    · rfl

private theorem searchLoop_memory (key : Word w) (n : Nat) (addr : Word w) (mem : Memory w) :
    ((searchLoop key n addr).evalM timeAndSpaceCost mem).2 = mem := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    rw [searchLoop_eval_succ]
    split_ifs
    · rfl
    · exact ih (addr + 1)

private theorem searchLoop_time_le (key : Word w) (n : Nat) (addr : Word w) (mem : Memory w) :
    ((searchLoop key n addr).costM timeAndSpaceCost mem).1.time ≤ 3 * n := by
  induction n generalizing addr with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [searchLoop_cost_succ]
    split_ifs
    · change 2 ≤ 3 * (n + 1)
      omega
    · change 3 + ((searchLoop key n (addr + 1)).costM timeAndSpaceCost mem).1.time ≤ _
      have := ih (addr + 1)
      omega

private theorem searchLoop_time_of_none (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) (hnone : ((searchLoop key n addr).evalM timeAndSpaceCost mem).1 = none) :
    ((searchLoop key n addr).costM timeAndSpaceCost mem).1.time = 3 * n := by
  induction n generalizing addr with
  | zero => rfl
  | succ n ih =>
    rw [searchLoop_eval_succ] at hnone
    rw [searchLoop_cost_succ]
    split_ifs with h
    · simp [h] at hnone
    · simp only [if_neg h] at hnone
      change 3 + ((searchLoop key n (addr + 1)).costM timeAndSpaceCost mem).1.time = _
      rw [ih (addr + 1) hnone]
      omega

private theorem arrayMemory_ofNat (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w)
    (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

private theorem wordAddress_succ (i : Nat) :
    BitVec.ofNat w i + 1 = BitVec.ofNat w (i + 1) := by
  simp [BitVec.ofNat_add]

/-- The returned address points to the key, and every earlier element differs from the key. -/
def IsFirstMatch (input : Array (BitVec w)) (key : BitVec w) (addr : Word w) : Prop :=
  addr.toNat < input.size ∧ input[addr.toNat]? = some key ∧
    ∀ i, i < addr.toNat → input[i]? ≠ some key

private theorem searchLoop_correct (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size) :
    match ((searchLoop key n (BitVec.ofNat w start)).evalM timeAndSpaceCost
        (arrayMemory input)).1 with
    | none => ∀ i, start ≤ i → i < start + n → input[i]? ≠ some key
    | some addr => start ≤ addr.toNat ∧ addr.toNat < start + n ∧
        input[addr.toNat]? = some key ∧
        ∀ i, start ≤ i → i < addr.toNat → input[i]? ≠ some key := by
  induction n generalizing start with
  | zero =>
    simp only [searchLoop_eval_zero, Nat.add_zero]
    intro i hlo hhi
    omega
  | succ n ih =>
    have hi : start < input.size := by omega
    have hw : start < 2 ^ w := lt_of_lt_of_le hi hfits
    rw [searchLoop_eval_succ, arrayMemory_ofNat input hfits start hi]
    by_cases h : input[start] = key
    · simp only [if_pos h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      refine ⟨le_rfl, by omega, ?_, ?_⟩
      · simp [hi, h]
      · intro i hlo hhi
        omega
    · simp only [if_neg h, wordAddress_succ]
      have htail := ih (start + 1) (by omega)
      cases he : ((searchLoop key n (BitVec.ofNat w (start + 1))).evalM timeAndSpaceCost
          (arrayMemory input)).1 with
      | none =>
        simp only [he] at htail ⊢
        intro i hlo hhi
        by_cases heq : i = start
        · subst i
          simpa [hi] using h
        · exact htail i (by omega) (by omega)
      | some addr =>
        simp only [he] at htail ⊢
        obtain ⟨hlo, hhi, hkey, hfirst⟩ := htail
        refine ⟨by omega, by omega, hkey, ?_⟩
        intro i hil hih
        by_cases heq : i = start
        · subst i
          simpa [hi] using h
        · exact hfirst i (by omega) hih

/-- Linear search returns the first match, or certifies that no array index contains the key. -/
theorem linearSearch_correct (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    match ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none => ∀ i, i < input.size → input[i]? ≠ some key
    | some addr => IsFirstMatch input key addr := by
  have h := searchLoop_correct input key hfits input.size 0 (by omega)
  rw [linearSearch_eq_searchLoop]
  split at h <;>
    simp_all only [evalM_timeAndSpaceCost, zero_le, zero_add, ne_eq, forall_const, true_and,
      BitVec.ofNat_eq_ofNat, IsFirstMatch, getElem?_pos, Option.some.injEq,
      not_false_eq_true, implies_true, and_true]
  exact (Array.getElem?_eq_some_iff.mp h.2.1).2

/-- Search preserves every memory cell. -/
theorem linearSearch_memory (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (mem : Memory w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost mem).2 = mem := by
  rw [linearSearch_eq_searchLoop]
  exact searchLoop_memory key input.size 0 mem

/-- A particular address is returned exactly when it is the first occurrence of the key. -/
theorem linearSearch_some_iff (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (addr : Word w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 = some addr ↔
      IsFirstMatch input key addr := by
  have hcorrect := linearSearch_correct input key hfits
  constructor
  · intro heq
    simpa only [heq] using hcorrect
  · intro hfirst
    cases he : ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none =>
      rw [he] at hcorrect
      exact False.elim (hcorrect addr.toNat hfirst.1 hfirst.2.1)
    | some found =>
      rw [he] at hcorrect
      have hindex : found.toNat = addr.toNat := by
        apply Nat.le_antisymm
        · by_contra h
          exact hcorrect.2.2 addr.toNat (by omega) hfirst.2.1
        · by_contra h
          exact hfirst.2.2 found.toNat (by omega) hcorrect.2.1
      exact congrArg some (BitVec.eq_of_toNat_eq hindex)

/-- Uniform linear time bound: at most three primitive queries per input element. -/
theorem linearSearch_time_le (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time ≤
      3 * input.size := by
  rw [linearSearch_eq_searchLoop]
  exact searchLoop_time_le key input.size 0 (arrayMemory input)

/-- The search fails exactly when the key is absent from the input array. -/
theorem linearSearch_none_iff (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 = none ↔
      key ∉ input := by
  have hcorrect := linearSearch_correct input key hfits
  constructor
  · intro hnone hmem
    rw [hnone] at hcorrect
    obtain ⟨i, hi, hkey⟩ := Array.mem_iff_getElem.mp hmem
    exact hcorrect i hi (by simp [hi, hkey])
  · intro hnot
    cases he : ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none => rfl
    | some addr =>
      rw [he] at hcorrect
      exact False.elim (hnot (Array.mem_of_getElem? hcorrect.2.1))

/-- An absent key forces exactly three queries per element, attaining the linear upper bound. -/
theorem linearSearch_time_of_not_mem (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (hnot : key ∉ input) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
      3 * input.size := by
  have hnone := (linearSearch_none_iff input key hfits).mpr hnot
  rw [linearSearch_eq_searchLoop] at hnone ⊢
  exact searchLoop_time_of_none key input.size 0 (arrayMemory input) hnone

private theorem searchLoop_time_of_some (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (addr : Word w)
    (hfound : ((searchLoop key n (BitVec.ofNat w start)).evalM timeAndSpaceCost
      (arrayMemory input)).1 = some addr) :
    ((searchLoop key n (BitVec.ofNat w start)).costM timeAndSpaceCost
      (arrayMemory input)).1.time + 3 * start = 3 * addr.toNat + 2 := by
  induction n generalizing start with
  | zero => simp [searchLoop_eval_zero] at hfound
  | succ n ih =>
    have hi : start < input.size := by omega
    have hw : start < 2 ^ w := lt_of_lt_of_le hi hfits
    rw [searchLoop_eval_succ, arrayMemory_ofNat input hfits start hi] at hfound
    rw [searchLoop_cost_succ, arrayMemory_ofNat input hfits start hi]
    split_ifs with h
    · simp only [if_pos h, Option.some.injEq] at hfound
      subst addr
      change 2 + 3 * start = 3 * (BitVec.ofNat w start).toNat + 2
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      omega
    · simp only [if_neg h, wordAddress_succ] at hfound
      change 3 + ((searchLoop key n (BitVec.ofNat w start + 1)).costM timeAndSpaceCost
        (arrayMemory input)).1.time + 3 * start = _
      rw [wordAddress_succ]
      have htail := ih (start + 1) (by omega) hfound
      omega

/-- A match at address `i` takes exactly `3 * i + 2` queries. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (addr : Word w)
    (hfound : ((linearSearch input key hfits).evalM timeAndSpaceCost
      (arrayMemory input)).1 = some addr) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
      3 * addr.toNat + 2 := by
  rw [linearSearch_eq_searchLoop] at hfound ⊢
  simpa using searchLoop_time_of_some input key hfits input.size 0 (by omega) addr hfound

/-- Addresses occupied by the input array, including cells not visited by an early return. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

private theorem searchLoop_addresses_subset (input : Array (BitVec w)) (key : BitVec w)
    (n start : Nat) (mem : Memory w) (hbound : start + n ≤ input.size) :
    ((searchLoop key n (BitVec.ofNat w start)).costM timeAndSpaceCost mem).1.addresses ⊆
      inputRegion input := by
  induction n generalizing start with
  | zero => exact Finset.empty_subset _
  | succ n ih =>
    have haddr : BitVec.ofNat w start ∈ inputRegion input :=
      Finset.mem_image.mpr ⟨start, Finset.mem_range.mpr (by omega), rfl⟩
    rw [searchLoop_cost_succ]
    split_ifs
    · exact Finset.singleton_subset_iff.mpr haddr
    · change {BitVec.ofNat w start} ∪
        ((searchLoop key n (BitVec.ofNat w start + 1)).costM timeAndSpaceCost mem).1.addresses ⊆ _
      apply Finset.union_subset (Finset.singleton_subset_iff.mpr haddr)
      rw [wordAddress_succ]
      exact ih (start + 1) (by omega)

/-- Every address accessed by the search lies in the input region. -/
theorem linearSearch_addresses_subset (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.addresses ⊆
      inputRegion input := by
  rw [linearSearch_eq_searchLoop]
  exact searchLoop_addresses_subset input key input.size 0 (arrayMemory input) (by omega)

/-- Auxiliary RAM space is exactly zero: the search only accesses input cells. -/
theorem linearSearch_auxiliarySpace (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.auxiliarySpace
      (inputRegion input) = 0 := by
  unfold RAMCost.auxiliarySpace
  rw [Finset.sdiff_eq_empty_iff_subset.mpr (linearSearch_addresses_subset input key hfits)]
  rfl

/-- Under the size bound, the input occupies exactly one cell per array element. -/
theorem inputRegion_card (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w) :
    (inputRegion input).card = input.size := by
  unfold inputRegion
  have hinj : Set.InjOn (BitVec.ofNat w) (↑(Finset.range input.size) : Set Nat) := by
    intro i hi j hj heq
    have hiw := lt_of_lt_of_le (Finset.mem_range.mp hi) hfits
    have hjw := lt_of_lt_of_le (Finset.mem_range.mp hj) hfits
    have h := congrArg BitVec.toNat heq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hiw, Nat.mod_eq_of_lt hjw] using h
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-- Total space including the input is exactly its length, even after an early return. -/
theorem linearSearch_totalSpace (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.totalSpace
      (inputRegion input) = input.size := by
  unfold RAMCost.totalSpace
  rw [Finset.union_eq_right.mpr (linearSearch_addresses_subset input key hfits)]
  exact inputRegion_card input hfits

/-- For every representable length and positive word width, an all-zero input searched for one
attains the upper bound. Thus the worst-case query time is linear, uniformly in the word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ((linearSearch (Array.replicate n (0 : BitVec w)) 1 (by simpa using hn)).costM
      timeAndSpaceCost (arrayMemory (Array.replicate n 0))).1.time = 3 * n := by
  simpa using linearSearch_time_of_not_mem (Array.replicate n (0 : BitVec w)) 1
    (by simpa using hn) (by simp [ne_of_gt hw])

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
