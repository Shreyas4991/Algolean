/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Mathlib.Data.Nat.Log

/-!
# Binary search on the word RAM

Binary search uses unsigned comparisons on a sorted array. Inclusive interval endpoints allow
all `2 ^ w` memory cells to hold input. Midpoint arithmetic, boundary checks, loads, and key
comparisons are primitive queries. The recursion budget only supplies bounded control flow.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

/-- Search a nonempty inclusive interval, with a structural recursion budget.
The boundary tests prevent underflow on a left step and overflow on a right step. -/
def binarySearchLoop (key : Word w) : Nat → Word w → Word w → Prog (WordRAM w) (Option (Word w))
  | 0, _, _ => pure none
  | fuel + 1, lo, hi => do
    let span : Word w ← binop .sub hi lo
    let half : Word w ← binop .shr span 1
    let mid : Word w ← binop .add lo half
    let value : Word w ← load mid
    let found : Bool ← cmp .eq value key
    if found then return some mid
    let right : Bool ← cmp .ult value key
    if right then
      let last : Bool ← cmp .eq mid hi
      if last then return none
      let next : Word w ← binop .add mid 1
      binarySearchLoop key fuel next hi
    else
      let first : Bool ← cmp .eq mid lo
      if first then return none
      let prev : Word w ← binop .sub mid 1
      binarySearchLoop key fuel lo prev

/-- Search an array laid out by `arrayMemory`, returning a matching address or `none`.
Sortedness is needed for correctness, but not for the time or space bounds. -/
def binarySearch (input : Array (BitVec w)) (key : BitVec w)
    (_fits : input.size ≤ 2 ^ w) : Prog (WordRAM w) (Option (Word w)) :=
  if input.size = 0 then pure none
  else binarySearchLoop key input.size 0 (BitVec.ofNat w (input.size - 1))

/-- The input is nondecreasing under unsigned word order. -/
def SortedWords (input : Array (BitVec w)) : Prop :=
  ∀ i j, (hi : i < input.size) → (hj : j < input.size) →
    i ≤ j → input[i].toNat ≤ input[j].toNat

section CorrectnessAndComplexity

@[simp, grind =] theorem binarySearchLoop_eval_zero (key lo hi : Word w) (mem : Memory w) :
    (binarySearchLoop key 0 lo hi).evalM timeAndSpaceCost mem = (none (α := Word w), mem) := rfl

@[simp, grind =] theorem binarySearchLoop_cost_zero (key lo hi : Word w) (mem : Memory w) :
    (binarySearchLoop key 0 lo hi).costM timeAndSpaceCost mem = ((0 : RAMCost w), mem) := rfl

@[grind =] theorem binarySearchLoop_eval_succ (key lo hi : Word w) (fuel : Nat)
    (mem : Memory w) :
    (binarySearchLoop key (fuel + 1) lo hi).evalM timeAndSpaceCost mem =
      let mid := lo + ((hi - lo) >>> (1 : Word w).toNat)
      if mem mid = key then (some mid, mem)
      else if (mem mid).toNat < key.toNat then
        if mid = hi then (none, mem)
        else (binarySearchLoop key fuel (mid + 1) hi).evalM timeAndSpaceCost mem
      else if mid = lo then (none, mem)
      else (binarySearchLoop key fuel lo (mid - 1)).evalM timeAndSpaceCost mem := by
  simp only [binarySearchLoop, Prog.evalM_liftBind_state, natCost_evalQuery_state,
    timeAndSpaceCost_evalQuery, BinOp.eval, CmpOp.eval, decide_eq_true_eq]
  split <;> simp_all [CmpOp.eval]
  split <;> simp_all [CmpOp.eval]
  all_goals split <;> simp_all [BinOp.eval]

@[grind =] theorem binarySearchLoop_cost_succ (key lo hi : Word w) (fuel : Nat)
    (mem : Memory w) :
    (binarySearchLoop key (fuel + 1) lo hi).costM timeAndSpaceCost mem =
      let mid := lo + ((hi - lo) >>> (1 : Word w).toNat)
      if mem mid = key then (⟨5, {mid}⟩, mem)
      else if (mem mid).toNat < key.toNat then
        if mid = hi then (⟨7, {mid}⟩, mem)
        else
          let rest := (binarySearchLoop key fuel (mid + 1) hi).costM timeAndSpaceCost mem
          (⟨8, {mid}⟩ + rest.1, rest.2)
      else if mid = lo then (⟨7, {mid}⟩, mem)
      else
        let rest := (binarySearchLoop key fuel lo (mid - 1)).costM timeAndSpaceCost mem
        (⟨8, {mid}⟩ + rest.1, rest.2) := by
  simp only [binarySearchLoop, Prog.costM_liftBind_state, natCost_evalQuery_state,
    timeAndSpaceCost_evalQuery, BinOp.eval, CmpOp.eval, decide_eq_true_eq]
  split <;> simp_all [CmpOp.eval, ← Nat.add_assoc]
  split <;> simp_all [CmpOp.eval, ← Nat.add_assoc]
  all_goals split <;> simp_all [BinOp.eval, ← Nat.add_assoc]

/-- Word midpoint arithmetic agrees with the natural-number midpoint without overflow. -/
@[grind =] theorem wordAddress_mid (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < 2 ^ w) :
    BitVec.ofNat w lo + ((BitVec.ofNat w hi - BitVec.ofNat w lo) >>> (1 : Word w).toNat) =
      BitVec.ofNat w (lo + (hi - lo) / 2) := by
  rw [BitVec.ofNat_sub_ofNat_of_le hi lo (by omega) hlo, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases w with
  | zero => simp; omega
  | succ w =>
    have hd : hi - lo < 2 ^ (w + 1) := by omega
    have hh : (hi - lo) / 2 < 2 ^ (w + 1) := by omega
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hh]

@[grind =] theorem wordAddress_pred (i : Nat) (hi : i < 2 ^ w) (hpos : 0 < i) :
    BitVec.ofNat w i - 1 = BitVec.ofNat w (i - 1) := by
  exact BitVec.ofNat_sub_ofNat_of_le i 1 (by omega) hpos

theorem wordAddress_eq_iff (i j : Nat) (hi : i < 2 ^ w) (hj : j < 2 ^ w) :
    BitVec.ofNat w i = BitVec.ofNat w j ↔ i = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    grind
  · exact congrArg (BitVec.ofNat w)

/-- Search never writes to memory, regardless of its inputs or recursion budget. -/
theorem binarySearchLoop_memory (key lo hi : Word w) (fuel : Nat) (mem : Memory w) :
    ((binarySearchLoop key fuel lo hi).evalM timeAndSpaceCost mem).2 = mem := by
  induction fuel generalizing lo hi <;> grind

private theorem binarySearchLoop_correct (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input)
    (fuel lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < input.size) (hfuel : hi - lo < fuel) :
    match ((binarySearchLoop key fuel (BitVec.ofNat w lo) (BitVec.ofNat w hi)).evalM
        timeAndSpaceCost (arrayMemory input)).1 with
    | none => ∀ i, lo ≤ i → i ≤ hi → input[i]? ≠ some key
    | some addr => lo ≤ addr.toNat ∧ addr.toNat ≤ hi ∧ input[addr.toNat]? = some key := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    set mid := lo + (hi - lo) / 2 with hmid
    have hmlo : lo ≤ mid := by omega
    have hmhi : mid ≤ hi := by omega
    have hmw : mid < 2 ^ w := by omega
    rw [binarySearchLoop_eval_succ, wordAddress_mid lo hi hlo (by omega)]
    dsimp only
    rw [← hmid]
    simp only [arrayMemory_ofNat input hfits mid (by omega),
      wordAddress_eq_iff mid hi hmw (by omega), wordAddress_eq_iff mid lo hmw (by omega)]
    split_ifs with hfound hright hlast hfirst
    · clear ih
      grind
    · clear ih
      grind [SortedWords]
    · rw [show BitVec.ofNat w mid + 1 = BitVec.ofNat w (mid + 1) from wordAddress_succ mid]
      have ht := ih (mid + 1) hi (by omega) hhi (by omega)
      clear ih
      grind [SortedWords]
    · clear ih
      grind [SortedWords, BitVec.eq_of_toNat_eq]
    · rw [wordAddress_pred mid hmw (by omega)]
      have ht := ih lo (mid - 1) (by omega) (by omega) (by omega)
      clear ih
      grind [SortedWords, BitVec.eq_of_toNat_eq]

/-- On sorted input, a returned address contains the key, and failure certifies absence.
Duplicates are allowed; the algorithm can return any matching address. -/
theorem binarySearch_correct (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input) :
    match ((binarySearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none => key ∉ input
    | some addr => addr.toNat < input.size ∧ input[addr.toNat]? = some key := by
  by_cases hzero : input.size = 0
  · simp [binarySearch, Array.eq_empty_of_size_eq_zero hzero]
  · rw [binarySearch, if_neg hzero]
    have h := binarySearchLoop_correct input key hfits hsorted input.size 0
      (input.size - 1) (by omega) (by omega) (by omega)
    grind [Array.mem_iff_getElem?]

/-- Failure is equivalent to absence of the key. -/
theorem binarySearch_none_iff (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input) :
    ((binarySearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 = none ↔
      key ∉ input := by
  have h := binarySearch_correct input key hfits hsorted
  grind [Array.mem_iff_getElem?]

/-- A successful search returns an in-bounds address containing the key. -/
theorem binarySearch_of_some (input : Array (BitVec w)) (key addr : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input)
    (hfound : ((binarySearch input key hfits).evalM timeAndSpaceCost
      (arrayMemory input)).1 = some addr) :
    addr.toNat < input.size ∧ input[addr.toNat]? = some key := by
  have h := binarySearch_correct input key hfits hsorted
  grind

/-- Binary search preserves every memory cell. -/
theorem binarySearch_memory (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) (mem : Memory w) :
    ((binarySearch input key hfits).evalM timeAndSpaceCost mem).2 = mem := by
  unfold binarySearch
  split
  · rfl
  · exact binarySearchLoop_memory key 0 (BitVec.ofNat w (input.size - 1)) input.size mem

private theorem log2_half_bound (n k : Nat) (hn : 2 ≤ n) (hk : k ≤ n / 2) :
    k.log2 + 1 ≤ n.log2 := by
  have h : k.log2 ≤ (n / 2).log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hk
  rw [Nat.log2_def n, if_pos hn]
  omega

private theorem binarySearchLoop_time_le (key : Word w) (fuel lo hi : Nat)
    (mem : Memory w) (hlo : lo ≤ hi) (hhi : hi < 2 ^ w) :
    ((binarySearchLoop key fuel (BitVec.ofNat w lo) (BitVec.ofNat w hi)).costM
      timeAndSpaceCost mem).1.time ≤ 8 * (hi - lo + 1).log2 + 7 := by
  induction fuel generalizing lo hi with
  | zero => simp
  | succ fuel ih =>
    set mid := lo + (hi - lo) / 2 with hmid
    have hmlo : lo ≤ mid := by omega
    have hmhi : mid ≤ hi := by omega
    have hmw : mid < 2 ^ w := by omega
    rw [binarySearchLoop_cost_succ, wordAddress_mid lo hi hlo hhi]
    dsimp only
    rw [← hmid]
    simp only [wordAddress_eq_iff mid hi hmw hhi,
      wordAddress_eq_iff mid lo hmw (by omega)]
    split_ifs with hfound hright hlast hfirst
    · simp
    · simp
    · rw [show BitVec.ofNat w mid + 1 = BitVec.ofNat w (mid + 1) from wordAddress_succ mid]
      have ht := ih (mid + 1) hi (by omega) hhi
      have hl := log2_half_bound (hi - lo + 1) (hi - (mid + 1) + 1) (by omega) (by omega)
      simpa only [RAMCost.add_time] using (show 8 +
        ((binarySearchLoop key fuel (BitVec.ofNat w (mid + 1)) (BitVec.ofNat w hi)).costM
          timeAndSpaceCost mem).1.time ≤ 8 * (hi - lo + 1).log2 + 7 by omega)
    · simp
    · rw [wordAddress_pred mid hmw (by omega)]
      have ht := ih lo (mid - 1) (by omega) (by omega)
      have hl := log2_half_bound (hi - lo + 1) (mid - 1 - lo + 1) (by omega) (by omega)
      simpa only [RAMCost.add_time] using (show 8 +
        ((binarySearchLoop key fuel (BitVec.ofNat w lo) (BitVec.ofNat w (mid - 1))).costM
          timeAndSpaceCost mem).1.time ≤ 8 * (hi - lo + 1).log2 + 7 by omega)

/-- Tight worst-case query bound, with zero queries for an empty input. -/
def binarySearchTime (n : Nat) : Nat := if n = 0 then 0 else 8 * n.log2 + 7

/-- Binary search uses at most `8 * log₂ n + 7` queries on nonempty input.
This bound does not require sortedness and holds even when the array fills memory. -/
theorem binarySearch_time_le (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    ((binarySearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time ≤
      binarySearchTime input.size := by
  unfold binarySearch binarySearchTime
  split
  · simp_all
  · simpa only [BitVec.ofNat_eq_ofNat, Nat.sub_zero,
      Nat.sub_add_cancel (by omega : 1 ≤ input.size)] using
      binarySearchLoop_time_le key input.size 0 (input.size - 1) (arrayMemory input)
        (by omega) (by omega)

private theorem binarySearchLoop_addresses_subset (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) (fuel lo hi : Nat) (mem : Memory w)
    (hlo : lo ≤ hi) (hhi : hi < input.size) :
    ((binarySearchLoop key fuel (BitVec.ofNat w lo) (BitVec.ofNat w hi)).costM
      timeAndSpaceCost mem).1.addresses ⊆ inputRegion input := by
  induction fuel generalizing lo hi with
  | zero => simp
  | succ fuel ih =>
    set mid := lo + (hi - lo) / 2 with hmid
    have hmlo : lo ≤ mid := by omega
    have hmhi : mid ≤ hi := by omega
    have hmw : mid < 2 ^ w := by omega
    rw [binarySearchLoop_cost_succ, wordAddress_mid lo hi hlo (by omega)]
    dsimp only
    rw [← hmid]
    simp only [wordAddress_eq_iff mid hi hmw (by omega),
      wordAddress_eq_iff mid lo hmw (by omega)]
    have hm := ofNat_mem_inputRegion input mid (by omega)
    split_ifs with hfound hright hlast hfirst
    · exact Finset.singleton_subset_iff.mpr hm
    · exact Finset.singleton_subset_iff.mpr hm
    · rw [show BitVec.ofNat w mid + 1 = BitVec.ofNat w (mid + 1) from wordAddress_succ mid]
      exact Finset.union_subset (Finset.singleton_subset_iff.mpr hm)
        (ih (mid + 1) hi (by omega) hhi)
    · exact Finset.singleton_subset_iff.mpr hm
    · rw [wordAddress_pred mid hmw (by omega)]
      exact Finset.union_subset (Finset.singleton_subset_iff.mpr hm)
        (ih lo (mid - 1) (by omega) (by omega))

/-- Every load stays inside the input region. -/
theorem binarySearch_addresses_subset (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    ((binarySearch input key hfits).costM timeAndSpaceCost
      (arrayMemory input)).1.addresses ⊆ inputRegion input := by
  unfold binarySearch
  split
  · simp
  · exact binarySearchLoop_addresses_subset input key hfits input.size 0 (input.size - 1)
      (arrayMemory input) (by omega) (by omega)

/-- Auxiliary space in the accessed-memory model is zero: only input cells are accessed. -/
theorem binarySearch_auxiliarySpace (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    ((binarySearch input key hfits).costM timeAndSpaceCost
      (arrayMemory input)).1.auxiliarySpace (inputRegion input) = 0 := by
  unfold RAMCost.auxiliarySpace
  rw [Finset.sdiff_eq_empty_iff_subset.mpr (binarySearch_addresses_subset input key hfits)]
  rfl

/-- Total space including the input equals its length. -/
theorem binarySearch_totalSpace (input : Array (BitVec w)) (key : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    ((binarySearch input key hfits).costM timeAndSpaceCost
      (arrayMemory input)).1.totalSpace (inputRegion input) = input.size := by
  unfold RAMCost.totalSpace
  rw [Finset.union_eq_right.mpr (binarySearch_addresses_subset input key hfits)]
  exact inputRegion_card input hfits

private theorem arrayMemory_replicate_zero (n : Nat) :
    arrayMemory (Array.replicate n (0 : BitVec w)) = Memory.zero := by
  funext addr
  simp only [arrayMemory, Memory.zero, Array.getElem?_replicate]
  split <;> rfl

private theorem binarySearchLoop_worstCase (hw : 0 < w) (fuel lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi < 2 ^ w) (hfuel : hi - lo < fuel) :
    ((binarySearchLoop (1 : Word w) fuel (BitVec.ofNat w lo) (BitVec.ofNat w hi)).costM
      timeAndSpaceCost Memory.zero).1.time = 8 * (hi - lo + 1).log2 + 7 := by
  induction fuel generalizing lo hi with
  | zero => omega
  | succ fuel ih =>
    set mid := lo + (hi - lo) / 2 with hmid
    have hmlo : lo ≤ mid := by omega
    have hmhi : mid ≤ hi := by omega
    have hmw : mid < 2 ^ w := by omega
    rw [binarySearchLoop_cost_succ, wordAddress_mid lo hi hlo hhi]
    dsimp only
    rw [← hmid]
    simp only [Memory.zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_zero, BitVec.toNat_one hw,
      show 0#w ≠ 1#w by simp [ne_of_gt hw], Nat.zero_lt_one, ↓reduceIte,
      wordAddress_eq_iff mid hi hmw hhi]
    split_ifs with hlast
    · have hn : hi - lo + 1 = 1 := by omega
      simp [hn, Nat.log2_def]
    · rw [wordAddress_succ]
      have ht := ih (mid + 1) hi (by omega) hhi (by omega)
      simp only [BitVec.ofNat_eq_ofNat] at ht
      have hn : 2 ≤ hi - lo + 1 := by omega
      have hhalf : hi - (mid + 1) + 1 = (hi - lo + 1) / 2 := by omega
      have hl := Nat.log2_def (hi - lo + 1)
      rw [if_pos hn, ← hhalf] at hl
      change 8 + _ = _
      omega

/-- For every positive word width and representable length, zeros searched for one attain
exactly the upper bound. Each failed iteration follows the larger (right) half. -/
theorem binarySearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ((binarySearch (Array.replicate n (0 : BitVec w)) 1 (by simpa using hn)).costM
      timeAndSpaceCost (arrayMemory (Array.replicate n 0))).1.time = binarySearchTime n := by
  by_cases hzero : n = 0
  · simp [binarySearch, binarySearchTime, hzero]
  · simp only [binarySearch, Array.size_replicate, if_neg hzero, arrayMemory_replicate_zero,
      binarySearchTime]
    simpa only [BitVec.ofNat_eq_ofNat, Nat.sub_zero, if_neg hzero,
      Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      binarySearchLoop_worstCase hw n 0 (n - 1) (by omega) (by omega) (by omega)

/-- A sorted worst-case instance exists at every length that fits in memory. -/
theorem binarySearch_exists_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ∃ (input : Array (BitVec w)) (key : Word w) (hfits : input.size ≤ 2 ^ w),
      input.size = n ∧ SortedWords input ∧ key ∉ input ∧
      ((binarySearch input key hfits).costM timeAndSpaceCost (arrayMemory input)).1.time =
        binarySearchTime n := by
  refine ⟨Array.replicate n 0, 1, by simpa using hn, by simp, ?_, ?_,
    binarySearch_worstCase w n hw hn⟩
  · simp [SortedWords]
  · simp [ne_of_gt hw]

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
