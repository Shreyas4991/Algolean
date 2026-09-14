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

@[simp, grind =] private theorem loop_eval_zero (s : RAMState w 4) :
    (loop 0).evalM natCost s = (none (α := Register 4), s) := rfl

@[simp, grind =] private theorem loop_cost_zero (s : RAMState w 4) :
    (loop 0).costM natCost s = ((0 : Nat), s) := rfl

@[grind =] private theorem loop_eval_succ (n : Nat) (s : RAMState w 4) :
    (loop (n + 1)).evalM natCost s =
      let loaded := s.writeRegister value (s.Memory (s.Registers index))
      if s.Memory (s.Registers index) = s.Registers key then (some index, loaded)
      else (loop n).evalM natCost
        (loaded.writeRegister index (s.Registers index + s.Registers one)) := by
  by_cases h : s.Memory (s.Registers index) = s.Registers key <;>
    simp [loop, evalQuery, CmpOp.eval, index, value, key, one] at h ⊢ <;>
    simp_all [evalQuery, BinOp.eval]

@[grind =] private theorem loop_cost_succ (n : Nat) (s : RAMState w 4) :
    (loop (n + 1)).costM natCost s =
      let loaded := s.writeRegister value (s.Memory (s.Registers index))
      if s.Memory (s.Registers index) = s.Registers key then
        (2, loaded)
      else
        let rest := (loop n).costM natCost
          (loaded.writeRegister index (s.Registers index + s.Registers one))
        (3 + rest.1, rest.2) := by
  by_cases h : s.Memory (s.Registers index) = s.Registers key <;>
    simp [loop, evalQuery, CmpOp.eval, index, value, key, one,
      ← Nat.add_assoc] at h ⊢ <;> simp_all [evalQuery, BinOp.eval, ← Nat.add_assoc]

private theorem loop_memory (n : Nat) (s : RAMState w 4) :
    ((loop n).evalM natCost s).2.Memory = s.Memory := by
  induction n generalizing s <;> grind

private theorem loop_time_le (n : Nat) (s : RAMState w 4) :
    ((loop n).costM natCost s).1 ≤ 3 * n := by
  induction n generalizing s <;> grind

private theorem loop_time_of_none (n : Nat) (s : RAMState w 4)
    (hnone : ((loop n).evalM natCost s).1 = none) :
    ((loop n).costM natCost s).1 = 3 * n := by
  induction n generalizing s <;> grind

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

private theorem loop_correct (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (n start : Nat) (hbound : start + n ≤ input.size)
    (s : RAMState w 4) (hmem : s.Memory = arrayMemory input)
    (hindex : s.Registers index = BitVec.ofNat w start) (hkey : s.Registers key = target)
    (hone : s.Registers one = 1) :
    let result := (loop n).evalM natCost s
    match result.1 with
    | none => ∀ i, start ≤ i → i < start + n → input[i]? ≠ some target
    | some r => r = index ∧ start ≤ (result.2.Registers r).toNat ∧
        (result.2.Registers r).toNat < start + n ∧
        input[(result.2.Registers r).toNat]? = some target ∧
        ∀ i, start ≤ i → i < (result.2.Registers r).toNat → input[i]? ≠ some target := by
  induction n generalizing start s with
  | zero => simp; omega
  | succ n ih =>
    rw [loop_eval_succ]
    dsimp only
    have hi : start < input.size := by omega
    rw [hmem, hindex, hkey, arrayMemory_ofNat input hfits start hi]
    split_ifs with hfound
    · simp only [RAMState.writeRegister_registers]
      clear ih
      grind
    · rw [hone, wordAddress_succ]
      have ht := ih (start + 1) (by omega)
        ((s.writeRegister value input[start]).writeRegister index (BitVec.ofNat w (start + 1)))
        (by simp [hmem]) (by simp) (by simp [key, value, index, hkey])
        (by simp [one, value, index, hone])
      clear ih
      grind

private def initialized (s : RAMState w 4) : RAMState w 4 :=
  (s.writeRegister index 0).writeRegister one 1

@[grind =] private theorem linearSearch_eval (n : Nat) (s : RAMState w 4) :
    (linearSearch w n).evalM natCost s =
      (loop n).evalM natCost (initialized s) := by
  simp [linearSearch, initialized, evalQuery]

@[grind =] private theorem linearSearch_cost (n : Nat) (s : RAMState w 4) :
    (linearSearch w n).costM natCost s =
      let rest := (loop n).costM natCost (initialized s)
      (2 + rest.1, rest.2) := by
  simp [linearSearch, initialized, evalQuery, ← Nat.add_assoc]

/-- The returned register holds the first match; failure certifies absence of the key. -/
theorem linearSearch_correct (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    let result := (linearSearch w input.size).evalM natCost
      (linearSearchState input target)
    match result.1 with
    | none => target ∉ input
    | some r => r = index ∧ IsFirstMatch input target (result.2.Registers r) := by
  dsimp only
  rw [linearSearch_eval]
  have h := loop_correct input target hfits input.size 0 (by omega)
    (initialized (linearSearchState input target)) (by simp [initialized, linearSearchState])
    (by simp [initialized, index, one]) (by simp [initialized, linearSearchState, key, index, one])
    (by simp [initialized])
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- The search fails exactly when the key is absent. -/
theorem linearSearch_none_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    ((linearSearch w input.size).evalM natCost
      (linearSearchState input target)).1 = none ↔ target ∉ input := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Success identifies the index register, whose final contents are the first matching address. -/
theorem linearSearch_some_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (r : Register 4) :
    let result := (linearSearch w input.size).evalM natCost
      (linearSearchState input target)
    result.1 = some r ↔ r = index ∧ IsFirstMatch input target (result.2.Registers r) := by
  have h := linearSearch_correct input target hfits
  grind [IsFirstMatch, Array.mem_iff_getElem?]

/-- Register operations and loads preserve the entire memory. -/
theorem linearSearch_memory (n : Nat) (s : RAMState w 4) :
    ((linearSearch w n).evalM natCost s).2.Memory = s.Memory := by
  rw [linearSearch_eval, loop_memory]
  simp [initialized]

/-- Two setup instructions and at most three queries per input element. -/
theorem linearSearch_time_le (n : Nat) (s : RAMState w 4) :
    ((linearSearch w n).costM natCost s).1 ≤ 3 * n + 2 := by
  have h := loop_time_le n (initialized s)
  rw [linearSearch_cost]
  dsimp only
  omega

/-- A missing key forces all `n` iterations, in addition to two setup instructions. -/
theorem linearSearch_time_of_not_mem (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hnot : target ∉ input) :
    ((linearSearch w input.size).costM natCost
      (linearSearchState input target)).1 = 3 * input.size + 2 := by
  have hn := (linearSearch_none_iff input target hfits).mpr hnot
  rw [linearSearch_eval] at hn
  have ht := loop_time_of_none input.size (initialized (linearSearchState input target)) hn
  rw [linearSearch_cost]
  dsimp only
  omega

private theorem loop_time_of_some (n start : Nat) (hbound : start + n ≤ 2 ^ w)
    (s : RAMState w 4) (hindex : s.Registers index = BitVec.ofNat w start)
    (hone : s.Registers one = 1) (r : Register 4)
    (hfound : ((loop n).evalM natCost s).1 = some r) :
    ((loop n).costM natCost s).1 + 3 * start =
      3 * (((loop n).evalM natCost s).2.Registers r).toNat + 2 := by
  induction n generalizing start s with
  | zero => simp at hfound
  | succ n ih =>
    rw [loop_eval_succ] at hfound
    rw [loop_eval_succ, loop_cost_succ]
    dsimp only at hfound ⊢
    split_ifs with hmatch
    · simp only [if_pos hmatch, Option.some.injEq] at hfound
      subst r
      simp only [RAMState.writeRegister_registers]
      clear ih
      grind
    · simp only [if_neg hmatch] at hfound
      rw [hindex, hone, wordAddress_succ] at hfound ⊢
      have ht := ih (start + 1) (by omega)
        ((s.writeRegister value (s.Memory (BitVec.ofNat w start))).writeRegister index
          (BitVec.ofNat w (start + 1))) (by simp) (by simp [one, value, index, hone]) hfound
      dsimp only
      omega

/-- A first match at address `i` costs `3 * i + 4`, including register initialization. -/
theorem linearSearch_time_of_some (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (r : Register 4)
    (hfound : ((linearSearch w input.size).evalM natCost
      (linearSearchState input target)).1 = some r) :
    ((linearSearch w input.size).costM natCost
      (linearSearchState input target)).1 =
      3 * (((linearSearch w input.size).evalM natCost
        (linearSearchState input target)).2.Registers r).toNat + 4 := by
  rw [linearSearch_eval] at hfound
  have ht := loop_time_of_some input.size 0 (by omega)
    (initialized (linearSearchState input target)) (by simp [initialized, index, one])
    (by simp [initialized]) r hfound
  rw [linearSearch_cost, linearSearch_eval]
  dsimp only
  omega

/-- Memory cells occupied by the input array. -/
def inputRegion (input : Array (BitVec w)) : Finset (Word w) :=
  (Finset.range input.size).image (BitVec.ofNat w)

@[simp, grind ←] theorem ofNat_mem_inputRegion (input : Array (BitVec w)) (i : Nat)
    (hi : i < input.size) : BitVec.ofNat w i ∈ inputRegion input :=
  Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

@[grind =] private theorem loop_probes_succ (n : Nat) (s : RAMState w 4)
    (probed : Finset (Word w)) :
    (loop (n + 1)).evalM timeAndSpaceCost (s, probed) =
      let loaded := s.writeRegister value (s.Memory (s.Registers index))
      let accessed := probed ∪ {s.Registers index}
      if s.Memory (s.Registers index) = s.Registers key then (some index, (loaded, accessed))
      else (loop n).evalM timeAndSpaceCost
        (loaded.writeRegister index (s.Registers index + s.Registers one), accessed) := by
  by_cases h : s.Memory (s.Registers index) = s.Registers key <;>
    simp [loop, evalQuery, queryProbes, CmpOp.eval, index, value, key, one] at h ⊢ <;>
    simp_all [evalQuery, queryProbes, BinOp.eval]

private theorem loop_addresses_subset (input : Array (BitVec w)) (n start : Nat)
    (hbound : start + n ≤ input.size) (s : RAMState w 4)
    (hindex : s.Registers index = BitVec.ofNat w start) (hone : s.Registers one = 1)
    (probed : Finset (Word w)) (hp : probed ⊆ inputRegion input) :
    ((loop n).evalM timeAndSpaceCost (s, probed)).2.2 ⊆ inputRegion input := by
  induction n generalizing start s probed with
  | zero => exact hp
  | succ n ih =>
    rw [loop_probes_succ]
    dsimp only
    rw [hindex, hone, wordAddress_succ]
    have hm := ofNat_mem_inputRegion input start (by omega)
    have hp' := Finset.union_subset hp (Finset.singleton_subset_iff.mpr hm)
    split_ifs
    · exact hp'
    · exact ih (start + 1) (by omega) _ (by simp) (by simp [one, value, index, hone]) _ hp'

/-- The memory probes are confined to the input; all working words are in four registers. -/
theorem linearSearch_addresses_subset (input : Array (BitVec w)) (target : Word w) :
    ((linearSearch w input.size).evalM timeAndSpaceCost
      (linearSearchState input target, ∅)).2.2 ⊆ inputRegion input := by
  have h := loop_addresses_subset input input.size 0 (by omega)
    (initialized (linearSearchState input target)) (by simp [initialized, index, one])
    (by simp [initialized]) ∅ (Finset.empty_subset _)
  simpa only [linearSearch, Prog.evalM_liftBind_state, timeAndSpaceCost_evalQuery,
    evalQuery, queryProbes, Finset.union_empty, initialized] using h

/-- Auxiliary space is four register words, with no memory probes outside the input. -/
theorem linearSearch_auxiliarySpace (input : Array (BitVec w)) (target : Word w) :
    (RAMCost.ofRun ((linearSearch w input.size).costM timeAndSpaceCost
      (linearSearchState input target, ∅))).auxiliarySpace (inputRegion input) = 4 := by
  simp only [RAMCost.auxiliarySpace, RAMCost.ofRun, Prog.costM_state]
  rw [Finset.sdiff_eq_empty_iff_subset.mpr (linearSearch_addresses_subset input target)]
  rfl

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
    (RAMCost.ofRun ((linearSearch w input.size).costM timeAndSpaceCost
      (linearSearchState input target, ∅))).totalSpace (inputRegion input) = input.size + 4 := by
  simp only [RAMCost.totalSpace, RAMCost.ofRun, Prog.costM_state]
  rw [Finset.union_eq_right.mpr (linearSearch_addresses_subset input target),
    inputRegion_card input hfits]
  omega

/-- Every representable length has a worst-case instance, for a positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ((linearSearch w n).costM natCost
      (linearSearchState (Array.replicate n (0 : BitVec w)) 1)).1 = 3 * n + 2 := by
  simpa using linearSearch_time_of_not_mem (Array.replicate n (0 : BitVec w)) 1
    (by simpa using hn) (by simp [ne_of_gt hw])

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
