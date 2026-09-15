/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic

/-!
# Uniform word-RAM linear search

The program depends only on word width. The key, inclusive last address, and nonempty flag
are supplied in the initial machine state. Five registers suffice, with no auxiliary memory.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM

namespace LinearSearch

/-- Current address, and the result register on success. -/
abbrev index : Register 5 := 0
/-- Search key supplied by the initial machine state. -/
abbrev key : Register 5 := 1
/-- Scratch register for the loaded input word. -/
abbrev value : Register 5 := 2
/-- Constant one used to advance the index. -/
abbrev one : Register 5 := 3
/-- Inclusive last input address, supplied at runtime. -/
abbrev last : Register 5 := 4

/-- Inspect one cell, stopping at the first match or the inclusive last address. -/
def body (w : Nat) : Prog (WordRAM w 5) Unit := do
  load (w := w) value index
  cmp (w := w) .eq value key
  branch .eq (do clearFlag (w := w) (k := 5) .ult) (do
    cmp (w := w) .ult index last
    branch .ult (do binop (w := w) .add index index one) (pure ()))

/-- Initialize scratch registers without inspecting runtime input. -/
def setup (w : Nat) : Prog (WordRAM w 5) Unit := do
  clearFlag (w := w) (k := 5) .eq
  set (w := w) index 0
  set (w := w) one 1

end LinearSearch

/-- One fixed program for all representable input lengths at word width `w`. -/
def linearSearch (w : Nat) : Prog (WordRAM w 5) Unit := do
  LinearSearch.setup w
  whileₚ .ult do
    LinearSearch.body w

/-- A canonical witness of the runtime input representation, used in examples. -/
def linearSearchState (input : Array (Word w)) (target : Word w) : RAMState w 5 :=
  ⟨arrayMemory input,
    fun r => if r = LinearSearch.key then target
      else if r = LinearSearch.last then BitVec.ofNat w (input.size - 1) else 0,
    fun op => if op = .ult then decide (input.size ≠ 0) else false⟩

@[simp] theorem linearSearchState_represents (input : Array (Word w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    RepresentsBoundedSearchInput ⟨input, target⟩ LinearSearch.key LinearSearch.last
      (linearSearchState input target) :=
  ⟨⟨arrayMemory_represents input hfits, by simp [linearSearchState]⟩,
    by simp [linearSearchState, LinearSearch.last, LinearSearch.key],
    by simp [linearSearchState]⟩

section CorrectnessAndComplexity

open LinearSearch

attribute [local simp] index key value one last CmpOp.eval BinOp.eval wordAddress_toNat

@[simp] private def checked (s : RAMState w 5) (found active : Bool) : RAMState w 5 :=
  ((s.writeRegister value (s.Memory (s.Registers index))).writeFlag .eq found).writeFlag
    .ult active

private theorem body_found (s : RAMState w 5)
    (h : s.Memory (s.Registers index) = s.Registers key) :
    Completes (instructions (body w)) s ⟨3, {s.Registers index}⟩ (checked s true false) :=
  ⟨4, by simp [body, branch, runCode, step, h]⟩

private theorem body_advance (s : RAMState w 5)
    (h : s.Memory (s.Registers index) ≠ s.Registers key)
    (hlt : (s.Registers index).toNat < (s.Registers last).toNat) :
    Completes (instructions (body w)) s ⟨4, {s.Registers index}⟩
      ((checked s false true).writeRegister index (s.Registers index + s.Registers one)) :=
  ⟨6, by simp [body, branch, runCode, step, h, hlt]⟩

private theorem body_last (s : RAMState w 5)
    (h : s.Memory (s.Registers index) ≠ s.Registers key)
    (hlt : ¬(s.Registers index).toNat < (s.Registers last).toNat) :
    Completes (instructions (body w)) s ⟨3, {s.Registers index}⟩ (checked s false false) :=
  ⟨5, by simp [body, branch, runCode, step, h, hlt]⟩

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
        cost.time = 4 * n - 1

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
    have hsw : start < 2 ^ w := lt_of_lt_of_le hstart hmem.fits
    have hlw : input.size - 1 < 2 ^ w := by have := hmem.fits; lia
    have hread : s.Memory (s.Registers index) = input[start] := by rw [hi, hmem.read start hstart]
    have hprobe := ofNat_mem_inputRegion input start hstart
    by_cases heq : input[start] = target
    · have hb := body_found s (by simpa [hread, hk] using heq)
      have hr := completes_while_false .ult (body w) (checked s true false) (by simp)
      refine ⟨_, _, completes_while_true .ult (body w) ha hb hr, ?_⟩
      suffices ∀ j, start ≤ j → j < start → input[j]? ≠ some target by
        simpa [Summary, hi, Nat.mod_eq_of_lt hsw, hprobe, heq, hstart] using this
      intro j hj hj'
      lia
    · by_cases hn0 : n = 0
      · subst n
        have hlt : ¬(s.Registers index).toNat < (s.Registers last).toNat := by
          simp only [hi, hl, wordAddress_toNat start hsw,
            wordAddress_toNat (input.size - 1) hlw]
          lia
        have hb := body_last s (by simpa [hread, hk] using heq) hlt
        have hr := completes_while_false .ult (body w) (checked s false false) (by simp)
        refine ⟨_, _, completes_while_true .ult (body w) ha hb hr, ?_⟩
        simp only [Summary, checked, RAMState.writeFlag_memory, RAMState.writeRegister_memory,
          add_zero, Finset.singleton_subset_iff, hi, hprobe, true_and,
          RAMState.writeFlag_flags, ↓reduceIte]
        constructor
        · intro j hj hj'
          have : j = start := by lia
          subst j
          simpa [hstart] using heq
        · trivial
      · let next := (checked s false true).writeRegister index (BitVec.ofNat w (start + 1))
        have hb : Completes (instructions (body w)) s ⟨4, {BitVec.ofNat w start}⟩ next := by
          simpa only [next, hi, h1, wordAddress_succ] using body_advance s
            (by simpa [hread, hk] using heq)
            (by simp only [hi, hl, wordAddress_toNat start hsw,
                  wordAddress_toNat (input.size - 1) hlw]; lia)
        obtain ⟨cost, t, hr, hs⟩ := ih (start + 1) (by lia) (by lia) next
          (by simpa [next] using hmem) (by simp [next]) (by simp [next, hk])
          (by simp [next, h1]) (by simp [next, hl]) (by simp [next])
        refine ⟨_, t, completes_while_true .ult (body w) ha hb hr, ?_⟩
        simp only [Summary, next, checked, RAMState.writeRegister_memory,
          RAMState.writeFlag_memory, RAMCost.mk_add] at hs ⊢
        obtain ⟨hm, hp, hs⟩ := hs
        refine ⟨hm, Finset.union_subset (Finset.singleton_subset_iff.mpr hprobe) hp, ?_⟩
        split_ifs at hs ⊢ <;> simp_all only
        · grind
        · constructor
          · intro j hj hj'
            by_cases hj0 : j = start
            · subst j; simpa [hstart] using heq
            · exact hs.left j (by lia) (by lia)
          · have := hs.right; lia

/-- Maximum time, attained by a missing key when the word width is positive. -/
def linearSearchTime (n : Nat) : Nat := if n = 0 then 3 else 4 * n + 2

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

/-- Every representing input state has sufficient interpreter fuel for termination. -/
theorem linearSearch_terminates (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s) :
    ∃ fuel cost t, execute fuel (linearSearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) := by
  obtain ⟨cost, t, hc, _⟩ := search_spec input s hinput
  obtain ⟨fuel, hf⟩ := hc.execute
  exact ⟨fuel, cost, t, hf⟩

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

/-- Uniform linear search returns the first match, or certifies absence. -/
theorem linearSearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    Search.linearSearch.spec input (searchOutput index final.ram) :=
  (linearSearch_run_spec input s hinput hrun).left

/-- The equality flag is clear exactly when the key is absent. -/
theorem linearSearch_none_iff (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Flags .eq = false ↔ input.key ∉ input.data := by
  have h := linearSearch_correct_of_execute input s hinput hrun
  simpa [searchOutput] using Search.search_none_iff (Search.linearSearch_spec_search _ _ h)

/-- A set equality flag identifies the first matching address. -/
theorem linearSearch_some_iff (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Flags .eq = true ↔
      Search.IsFirstMatch input.data input.key (final.ram.Registers index).toNat := by
  simpa [searchOutput] using Search.linearSearch_some_iff
    (linearSearch_correct_of_execute input s hinput hrun) (final.ram.Registers index).toNat

/-- Loads and register operations preserve the entire input and background memory. -/
theorem linearSearch_memory (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    final.ram.Memory = s.Memory := (linearSearch_run_spec input s hinput hrun).right.left

/-- The exact time depends on the first match, or on the length when the key is absent. -/
theorem linearSearch_time (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time = linearSearchCost input.data.size (searchOutput index final.ram) :=
  (linearSearch_run_spec input s hinput hrun).right.right.right

/-- At most four primitive operations per unsuccessful cell, plus setup and exit costs. -/
theorem linearSearch_time_le (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time ≤ linearSearchTime input.data.size := by
  have hs := linearSearch_correct_of_execute input s hinput hrun
  rw [linearSearch_time input s hinput hrun]
  cases ho : searchOutput index final.ram with
  | none => exact Nat.le_refl _
  | some i =>
    simp only [ho, Search.linearSearch_spec_some, Search.IsFirstMatch] at hs
    simp only [linearSearchCost, linearSearchTime, if_neg (by lia : input.data.size ≠ 0)]
    lia

/-- An absent key attains the length-dependent upper bound. -/
theorem linearSearch_time_of_not_mem (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s) (hnot : input.key ∉ input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.time = linearSearchTime input.data.size := by
  have hf := (linearSearch_none_iff input s hinput hrun).mpr hnot
  simpa [hf, linearSearchCost] using linearSearch_time input s hinput hrun

/-- A first match at index `i` costs exactly `4 * i + 6`. -/
theorem linearSearch_time_of_some (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final))
    (hfound : final.ram.Flags .eq = true) :
    result.tell.time = 4 * (final.ram.Registers index).toNat + 6 := by
  simpa [hfound, linearSearchCost] using linearSearch_time input s hinput hrun

/-- Every probed address belongs to the input array. -/
theorem linearSearch_addresses_subset (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.addresses ⊆ inputRegion input.data :=
  (linearSearch_run_spec input s hinput hrun).right.right.left

/-- Only input memory is probed; registers do not count as auxiliary memory. -/
theorem linearSearch_auxiliarySpace (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.auxiliarySpace (inputRegion input.data) = 0 := by
  simp only [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr
    (linearSearch_addresses_subset input s hinput hrun), Finset.card_empty]

/-- Total memory is exactly the input footprint, including any unread input cells. -/
theorem linearSearch_totalSpace (input : Search.Input (Word w)) (s : RAMState w 5)
    (hinput : RepresentsBoundedSearchInput input key last s)
    {fuel : Nat} {result : AddWriter (RAMCost w 5) Unit} {final : ExecutionState w 5}
    (hrun : execute fuel (linearSearch w) s = some (result, final)) :
    result.tell.totalSpace (inputRegion input.data) = input.data.size := by
  simp only [RAMCost.totalSpace, Finset.union_eq_right.mpr
    (linearSearch_addresses_subset input s hinput hrun), inputRegion_card input.data hinput.fits]

/-- Total correctness of this fixed, runtime-size-independent program on every representing
state. The output remains in the machine's registers and flags. -/
theorem linearSearch_correct (w : Nat) :
    let problem := Search.linearSearch
    let repInput := fun input => RepresentsBoundedSearchInput input key last
    problem.Solves (linearSearch w) Executes repInput (RepresentsSearchOutput index) := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s ha hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨searchOutput index t, representsSearchOutput_searchOutput index t,
      linearSearch_correct_of_execute input s hi hr⟩

/-- Termination, the worst-case time bound, and zero auxiliary memory for every represented
input. Resource guarantees do not require sortedness. -/
theorem linearSearch_runsWithin (w : Nat) :
    let repInput := fun input => RepresentsBoundedSearchInput input key last
    let bound := fun (input : Search.Input (Word w)) (cost : RAMCost w 5) =>
      cost.time ≤ linearSearchTime input.data.size ∧
        cost.auxiliarySpace (inputRegion input.data) = 0
    Search.RunsWithin (linearSearch w) Executes repInput bound := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s _ hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨linearSearch_time_le input s hi hr, linearSearch_auxiliarySpace input s hi hr⟩

/-- Every fitting length has a worst-case instance at positive word width. -/
theorem linearSearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    let input := Array.replicate n (0 : Word w)
    let s := linearSearchState input 1
    ∃ fuel cost t, execute fuel (linearSearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) ∧
      cost.time = linearSearchTime n := by
  let input := Array.replicate n (0 : Word w)
  have hrep := linearSearchState_represents input 1 (by simpa [input] using hn)
  obtain ⟨fuel, cost, t, hr⟩ := linearSearch_terminates ⟨input, 1⟩ _ hrep
  refine ⟨fuel, cost, t, hr, ?_⟩
  simpa [input] using linearSearch_time_of_not_mem ⟨input, 1⟩ _ hrep
    (by simp [input, ne_of_gt hw]) hr

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
