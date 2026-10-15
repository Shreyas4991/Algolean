/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic

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

@[simp, grind =]
private theorem searchLoop_eval_zero (key : Word w) (addr : Word w) (mem : Memory w) :
    (searchLoop key 0 addr).evalM timeAndSpaceCost mem = (none (α := Word w), mem) := rfl

@[grind =]
private theorem searchLoop_eval_succ (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) :
    (searchLoop key (n + 1) addr).evalM timeAndSpaceCost mem =
      if mem addr = key then (some addr, mem)
      else (searchLoop key n (addr + 1)).evalM timeAndSpaceCost mem := by
  by_cases h : mem addr = key <;> simp [searchLoop, CmpOp.eval, BinOp.eval, h]

@[simp, grind =]
private theorem searchLoop_cost_zero (key : Word w) (addr : Word w) (mem : Memory w) :
    (searchLoop key 0 addr).costM timeAndSpaceCost mem = ((0 : RAMCost w), mem) := rfl

@[grind =]
private theorem searchLoop_cost_succ (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) :
    (searchLoop key (n + 1) addr).costM timeAndSpaceCost mem =
      if mem addr = key then (⟨2, {addr}⟩, mem)
      else
        let rest := (searchLoop key n (addr + 1)).costM timeAndSpaceCost mem
        (⟨3, {addr}⟩ + rest.1, rest.2) := by
  by_cases h : mem addr = key <;>
    simp [searchLoop, CmpOp.eval, BinOp.eval, h, ← Nat.add_assoc]

private theorem searchLoop_memory (key : Word w) (n : Nat) (addr : Word w) (mem : Memory w) :
    ((searchLoop key n addr).evalM timeAndSpaceCost mem).2 = mem := by
  induction n generalizing addr <;> grind

private theorem searchLoop_time_le (key : Word w) (n : Nat) (addr : Word w) (mem : Memory w) :
    ((searchLoop key n addr).costM timeAndSpaceCost mem).1.time ≤ 3 * n := by
  induction n generalizing addr <;> grind

private theorem searchLoop_time_of_none (key : Word w) (n : Nat) (addr : Word w)
    (mem : Memory w) (hnone : ((searchLoop key n addr).evalM timeAndSpaceCost mem).1 = none) :
    ((searchLoop key n addr).costM timeAndSpaceCost mem).1.time = 3 * n := by
  induction n generalizing addr <;> grind

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
  induction n generalizing start <;> grind

/-- Linear search returns the first match, or certifies that no array index contains the key. -/
theorem linearSearch_correct (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    match ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none => ∀ i, i < input.size → input[i]? ≠ some key
    | some addr => IsFirstMatch input key addr := by
  rw [linearSearch_eq_searchLoop]
  have h := searchLoop_correct input key hfits input.size 0 (by omega)
  grind [IsFirstMatch]

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
  grind [IsFirstMatch, BitVec.eq_of_toNat_eq]

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
  grind [IsFirstMatch, Array.mem_iff_getElem?]

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
  induction n generalizing start <;> grind

/-- A match at address `i` takes exactly `3 * i + 2` queries. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (addr : Word w)
    (hfound : ((linearSearch input key hfits).evalM timeAndSpaceCost
      (arrayMemory input)).1 = some addr) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
      3 * addr.toNat + 2 := by
  rw [linearSearch_eq_searchLoop] at hfound ⊢
  simpa using searchLoop_time_of_some input key hfits input.size 0 (by omega) addr hfound

private theorem searchLoop_addresses_subset (input : Array (BitVec w)) (key : BitVec w)
    (n start : Nat) (mem : Memory w) (hbound : start + n ≤ input.size) :
    ((searchLoop key n (BitVec.ofNat w start)).costM timeAndSpaceCost mem).1.addresses ⊆
      inputRegion input := by
  induction n generalizing start <;> grind

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
