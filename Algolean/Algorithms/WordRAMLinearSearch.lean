/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Vignesh Karri
-/

module

public import Algolean.Models.WordRAM
public import Std.Tactic.Do

/-!
# Linear search on the word RAM

`linearSearch` searches an array laid out in consecutive memory cells by `arrayMemory`.
It returns the first matching address and preserves memory.

The proofs reason about `linearSearch` directly with `vcgen`. One Hoare triple,
`linearSearch_cost_correctness_spec`, establishes the result specification, the exact query count,
and the memory footprint. It is tagged `@[spec]`, so `vcgen` proofs about programs that call
`linearSearch` reuse it. `linearSearch_run` evaluates the triple on the array's memory, and the
public theorems follow from it: exact successful and unsuccessful query counts, a tight linear
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

/-- The returned address points to the key, and every earlier element differs from the key. -/
def IsFirstMatch (input : Array (BitVec w)) (key : BitVec w) (addr : Word w) : Prop :=
  addr.toNat < input.size ∧ input[addr.toNat]? = some key ∧
    ∀ i, i < addr.toNat → input[i]? ≠ some key

/-- Addresses occupied by the input array, including cells not visited by an early return. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

section CorrectnessAndComplexity

open Std.WP

set_option experimental.vcgen true

@[simp, grind =]
private theorem arrayMemory_ofNat (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w)
    (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

@[grind →]
private theorem length_lt_of_range_eq {n cur : Nat} {pref suff : List Nat}
    (h : List.range n = pref ++ cur :: suff) : pref.length < n := by
  have := congrArg List.length h
  simp at this
  omega

/-- Every valid array index belongs to the input's memory region. -/
@[simp, grind ←]
theorem ofNat_mem_inputRegion (input : Array (BitVec w)) (i : Nat) (hi : i < input.size) :
    BitVec.ofNat w i ∈ inputRegion input :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- Under the size bound, the input occupies exactly one cell per array element. -/
theorem inputRegion_card (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w) :
    (inputRegion input).card = input.size := by
  unfold inputRegion
  rw [Finset.card_image_of_injOn (by
    intro i hi j hj heq
    have := congrArg BitVec.toNat heq
    grind), Finset.card_range]

/-! ### Specifications -/

/-- One Hoare triple for correctness, exact query count and memory footprint. -/
@[spec]
theorem linearSearch_cost_correctness_spec (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (c₀ : RAMCost w) :
    ⦃fun cost mem => cost = c₀ ∧ mem = arrayMemory input⦄
    linearSearch input key hfits
    ⦃fun r cost mem => mem = arrayMemory input ∧
      cost.addresses ⊆ c₀.addresses ∪ inputRegion input ∧
      match r with
      | none => (∀ i, i < input.size → input[i]? ≠ some key) ∧
          cost.time = c₀.time + 3 * input.size
      | some addr => IsFirstMatch input key addr ∧
          cost.time = c₀.time + 3 * addr.toNat + 2⦄ := by
  vcgen [linearSearch] invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret addr cost mem =>
        IsFirstMatch input key addr ∧ ret = some addr ∧ mem = arrayMemory input ∧
          cost.time = c₀.time + 3 * addr.toNat + 2 ∧
          cost.addresses ⊆ c₀.addresses ∪ inputRegion input)
      (onContinue := fun pref _ addr cost mem =>
        (∀ i, i < pref.length → input[i]? ≠ some key) ∧
          addr = BitVec.ofNat w pref.length ∧ mem = arrayMemory input ∧
          cost.time = c₀.time + 3 * pref.length ∧
          cost.addresses ⊆ c₀.addresses ∪ inputRegion input)
  all_goals simp_all [CmpOp.eval, BinOp.eval]
  all_goals grind [IsFirstMatch]

/-- Search leaves every memory cell unchanged, from any starting memory and cost. -/
theorem linearSearch_preserves (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (mem₀ : Memory w) :
    ⦃fun _ mem => mem = mem₀⦄ linearSearch input key hfits ⦃fun _ _ mem => mem = mem₀⦄ := by
  vcgen [linearSearch] invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun _ _ _ mem => mem = mem₀)
      (onContinue := fun _ _ _ _ mem => mem = mem₀)
  all_goals simp_all [CmpOp.eval]

/-! ### Running the specification -/

/-- One run of linear search on the array's memory, from zero cost: every accessed address lies in
the input region, and the result is the first match (or a certificate of absence) with exact query
count `3 * addr + 2` on a match or `3 * input.size` on a miss. -/
theorem linearSearch_run (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.addresses ⊆
        inputRegion input ∧
      match ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
      | none => (∀ i, i < input.size → input[i]? ≠ some key) ∧
          ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
            3 * input.size
      | some addr => IsFirstMatch input key addr ∧
          ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
            3 * addr.toNat + 2 := by
  have h := ModelM.costM_of_triple timeAndSpaceCost
    (linearSearch_cost_correctness_spec input key hfits 0) 0 (arrayMemory input) ⟨rfl, rfl⟩
  simpa using h.2

/-! ### Public theorems

Each follows from `linearSearch_run`, except `linearSearch_memory`, which uses
`linearSearch_preserves` because it holds for any starting memory. -/

/-- Search preserves every memory cell. -/
theorem linearSearch_memory (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (mem : Memory w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost mem).2 = mem :=
  ModelM.costM_of_triple timeAndSpaceCost (linearSearch_preserves input key hfits mem) 0 mem rfl

/-- A particular address is returned exactly when it is the first occurrence of the key. -/
theorem linearSearch_some_iff (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (addr : Word w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 = some addr ↔
      IsFirstMatch input key addr := by
  have h := (linearSearch_run input key hfits).2
  grind [IsFirstMatch, BitVec.eq_of_toNat_eq]

/-- The search fails exactly when the key is absent from the input array. -/
theorem linearSearch_none_iff (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 = none ↔
      key ∉ input := by
  have h := (linearSearch_run input key hfits).2
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Uniform linear time bound: at most three primitive queries per input element. -/
theorem linearSearch_time_le (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time ≤
      3 * input.size := by
  have h := (linearSearch_run input key hfits).2
  grind [IsFirstMatch]

/-- An absent key forces exactly three queries per element, attaining the linear upper bound. -/
theorem linearSearch_time_of_not_mem (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (hnot : key ∉ input) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
      3 * input.size := by
  have h := (linearSearch_run input key hfits).2
  grind [linearSearch_none_iff]

/-- A match at address `i` takes exactly `3 * i + 2` queries. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) (addr : Word w)
    (hfound : ((linearSearch input key hfits).evalM timeAndSpaceCost
      (arrayMemory input)).1 = some addr) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
      3 * addr.toNat + 2 := by
  have h := (linearSearch_run input key hfits).2
  simp_all

/-- Auxiliary RAM space is exactly zero: the search only accesses input cells. -/
theorem linearSearch_auxiliarySpace (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.auxiliarySpace
      (inputRegion input) = 0 := by
  simp [RAMCost.auxiliarySpace,
    Finset.sdiff_eq_empty_iff_subset.mpr (linearSearch_run input key hfits).1]

/-- Total space including the input is exactly its length, even after an early return. -/
theorem linearSearch_totalSpace (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.totalSpace
      (inputRegion input) = input.size := by
  simp [RAMCost.totalSpace, Finset.union_eq_right.mpr (linearSearch_run input key hfits).1,
    inputRegion_card input hfits]

/-- For every representable length and positive word width, an all-zero input searched for one
attains the upper bound. Thus the worst-case query time is linear, uniformly in the word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ((linearSearch (Array.replicate n (0 : BitVec w)) 1 (by simpa using hn)).costM
      timeAndSpaceCost (arrayMemory (Array.replicate n 0))).1.time = 3 * n := by
  simpa using linearSearch_time_of_not_mem (Array.replicate n (0 : BitVec w)) 1
    (by simpa using hn) (by simp [ne_of_gt hw])

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
