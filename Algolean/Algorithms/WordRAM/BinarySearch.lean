/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Algolean.Models.WordRAMSyntax
public import Mathlib.Data.Nat.Log

/-!
# Binary search with six word-RAM registers

Adapted from https://github.com/Shreyas4991/Algolean/pull/89 to the register-only model.
Inclusive bounds support all `2 ^ w` input cells. The midpoint is `lo + (hi - lo) / 2`;
boundary comparisons prevent either endpoint from wrapping. All word computations are queries.
The program reads its bound from the initial upper register and loops on a machine flag.
Interpreter fuel is supplied only when executing the program.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

namespace BinarySearch

/-- Inclusive lower endpoint. -/
abbrev lower : Register 6 := 0
/-- Inclusive upper endpoint, supplied by the initial machine state. -/
abbrev upper : Register 6 := 1
/-- Midpoint, and result register on success. -/
abbrev middle : Register 6 := 2
/-- Word loaded at the midpoint. -/
abbrev value : Register 6 := 3
/-- Search key supplied in the initial state. -/
abbrev key : Register 6 := 4
/-- Constant one for shifts and endpoint updates. -/
abbrev one : Register 6 := 5

/-- One machine iteration, with its continuation indicated by the less-than flag. -/
def body (w : Nat) : Prog (WordRAM w 6) Unit := do [WordRAM w 6]
  middle ←ᵣ upper - lower
  middle ←ᵣ middle >>> one
  middle ←ᵣ lower + middle
  value ←ᵣ mem[middle]
  ifₚ test .eq value key then
    reset .ult
  else
    ifₚ test .ult value key then
      ifₚ test .ult middle upper then
        lower ←ᵣ middle + one
      else
        pure ()
    else
      ifₚ test .ult lower middle then
        upper ←ᵣ middle - one
      else
        pure ()

/-- Initialize the lower endpoint and increment constant; the upper endpoint is runtime input. -/
def setup (w : Nat) : Prog (WordRAM w 6) Unit := do [WordRAM w 6]
  lower ←ᵣ imm[0]
  one ←ᵣ imm[1]

end BinarySearch

/-- Uniform binary search: width determines code; memory, key, last address, and the
nonempty flag supply the runtime input. -/
def binarySearch (w : Nat) : Prog (WordRAM w 6) Unit := do [WordRAM w 6]
  reset .eq
  ifₚ flag .ult then
    BinarySearch.setup w
    whileₚ .ult do
      BinarySearch.body w
  else
    pure ()

/-- A canonical runtime input witness; proofs also apply to arbitrary representing states. -/
def binarySearchState (input : Array (Word w)) (target : Word w) : RAMState w 6 :=
  ⟨arrayMemory input,
    fun r => if r = BinarySearch.key then target
      else if r = BinarySearch.upper then BitVec.ofNat w (input.size - 1) else 0,
    fun op => if op = .ult then decide (input.size ≠ 0) else false⟩

@[simp] theorem binarySearchState_represents (input : Array (Word w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) :
    RepresentsBoundedSearchInput ⟨input, target⟩ BinarySearch.key BinarySearch.upper
      (binarySearchState input target) :=
  ⟨⟨arrayMemory_represents input hfits, by simp [binarySearchState]⟩,
    by simp [binarySearchState, BinarySearch.upper, BinarySearch.key],
    by simp [binarySearchState]⟩

section CorrectnessAndComplexity

open BinarySearch

attribute [local simp] lower upper middle value key one CmpOp.eval BinOp.eval wordAddress_toNat

/-- The word midpoint agrees with the natural midpoint, even when input fills memory. -/
@[grind =] theorem wordAddress_mid (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < 2 ^ w) :
    BitVec.ofNat w lo + ((BitVec.ofNat w hi - BitVec.ofNat w lo) >>> (1 : Word w).toNat) =
      BitVec.ofNat w (lo + (hi - lo) / 2) := by
  rw [BitVec.ofNat_sub_ofNat_of_le hi lo (by lia) hlo, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases w with
  | zero => simp; lia
  | succ w =>
    have hd : hi - lo < 2 ^ (w + 1) := by lia
    have hh : (hi - lo) / 2 < 2 ^ (w + 1) := by lia
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hh]

attribute [local simp] wordAddress_mid wordAddress_toNat

/-- Decrementing a positive representable address does not wrap. -/
@[grind =] theorem wordAddress_pred (i : Nat) (hi : i < 2 ^ w) (hpos : 0 < i) :
    BitVec.ofNat w i - 1 = BitVec.ofNat w (i - 1) :=
  BitVec.ofNat_sub_ofNat_of_le i 1 (by lia) hpos

/-- Equality of representable natural addresses is preserved by word conversion. -/
@[simp] theorem wordAddress_eq_iff (i j : Nat) (hi : i < 2 ^ w) (hj : j < 2 ^ w) :
    BitVec.ofNat w i = BitVec.ofNat w j ↔ i = j := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    grind
  · exact congrArg (BitVec.ofNat w)

private def midpoint (s : RAMState w 6) : Word w :=
  s.Registers lower + ((s.Registers upper - s.Registers lower) >>> (s.Registers one).toNat)

private def checked (s : RAMState w 6) (found active : Bool) : RAMState w 6 :=
  (((s.writeRegister middle (midpoint s)).writeRegister value (s.Memory (midpoint s))).writeFlag
    .eq found).writeFlag .ult active

@[simp, grind =] private theorem checked_memory (s : RAMState w 6) (found active : Bool) :
    (checked s found active).Memory = s.Memory := rfl

@[simp, grind =] private theorem checked_registers (s : RAMState w 6) (found active : Bool)
    (r : Register 6) : (checked s found active).Registers r =
      if r = value then s.Memory (midpoint s)
      else if r = middle then midpoint s else s.Registers r := by
  simp [checked]

@[simp, grind =] private theorem checked_flags (s : RAMState w 6) (found active : Bool)
    (op : CmpOp) : (checked s found active).Flags op =
      if op = .ult then active else found := by
  cases op <;> simp [checked]

private theorem body_found (s : RAMState w 6)
    (h : s.Memory (midpoint s) = s.Registers key) :
    Completes (instructions (body w)) s ⟨6, {midpoint s}⟩ (checked s true false) :=
by
  simp only [midpoint, lower, upper, key, one] at h
  exact ⟨7, by simp [body, checked, branch, runCode, step, midpoint, h]⟩

private theorem body_right (s : RAMState w 6)
    (h : s.Memory (midpoint s) ≠ s.Registers key)
    (hlt : (s.Memory (midpoint s)).toNat < (s.Registers key).toNat)
    (hb : (midpoint s).toNat < (s.Registers upper).toNat) :
    Completes (instructions (body w)) s ⟨8, {midpoint s}⟩
      ((checked s false true).writeRegister lower (midpoint s + s.Registers one)) :=
by
  simp only [midpoint, lower, upper, key, one,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight] at h hlt hb
  exact ⟨11, by simp [body, checked, branch, runCode, step, midpoint, h, hlt, hb]⟩

private theorem body_stop_right (s : RAMState w 6)
    (h : s.Memory (midpoint s) ≠ s.Registers key)
    (hlt : (s.Memory (midpoint s)).toNat < (s.Registers key).toNat)
    (hb : ¬(midpoint s).toNat < (s.Registers upper).toNat) :
    Completes (instructions (body w)) s ⟨7, {midpoint s}⟩
      (checked s false false) :=
by
  simp only [midpoint, lower, upper, key, one,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight] at h hlt hb
  exact ⟨10, by simp [body, checked, branch, runCode, step, midpoint, h, hlt, hb]⟩

private theorem body_left (s : RAMState w 6)
    (h : s.Memory (midpoint s) ≠ s.Registers key)
    (hlt : ¬(s.Memory (midpoint s)).toNat < (s.Registers key).toNat)
    (hb : (s.Registers lower).toNat < (midpoint s).toNat) :
    Completes (instructions (body w)) s ⟨8, {midpoint s}⟩
      ((checked s false true).writeRegister upper (midpoint s - s.Registers one)) :=
by
  simp only [midpoint, lower, upper, key, one,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight] at h hlt hb
  exact ⟨11, by simp [body, checked, branch, runCode, step, midpoint, h, hlt, hb]⟩

private theorem body_stop_left (s : RAMState w 6)
    (h : s.Memory (midpoint s) ≠ s.Registers key)
    (hlt : ¬(s.Memory (midpoint s)).toNat < (s.Registers key).toNat)
    (hb : ¬(s.Registers lower).toNat < (midpoint s).toNat) :
    Completes (instructions (body w)) s ⟨7, {midpoint s}⟩
      (checked s false false) :=
by
  simp only [midpoint, lower, upper, key, one,
    BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ushiftRight] at h hlt hb
  exact ⟨10, by simp [body, checked, branch, runCode, step, midpoint, h, hlt, hb]⟩


private theorem log2_half_bound (n k : Nat) (hn : 2 ≤ n) (hk : k ≤ n / 2) :
    k.log2 + 1 ≤ n.log2 := by
  have h : k.log2 ≤ (n / 2).log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hk
  rw [Nat.log2_def n, if_pos hn]
  lia

/-- One charged iteration plus a half-sized recursive search preserves the logarithmic bound. -/
private theorem step_time_bound {time size remaining : Nat}
    (ht : time ≤ 8 * remaining.log2 + 7) (hsize : 2 ≤ size) (hhalf : remaining ≤ size / 2) :
    8 + time ≤ 8 * size.log2 + 7 := by
  have := log2_half_bound size remaining hsize hhalf
  lia

private theorem pivot_bounds {lo hi : Nat} (h : lo ≤ hi) :
    lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 ≤ hi := by lia

@[simp, grind =] private theorem right_length {lo hi : Nat}
    (h : lo + (hi - lo) / 2 < hi) :
    hi - (lo + (hi - lo) / 2 + 1) + 1 = (hi - lo + 1) / 2 := by lia

@[simp, grind =] private theorem left_length {lo hi : Nat}
    (h : lo < lo + (hi - lo) / 2) :
    lo + (hi - lo) / 2 - 1 - lo + 1 = (hi - lo) / 2 := by lia

/-- On a nonempty right half, exactly one logarithmic level has been consumed. -/
private theorem right_log {lo hi : Nat}
    (h : lo + (hi - lo) / 2 < hi) :
    8 + (8 * (hi - (lo + (hi - lo) / 2 + 1) + 1).log2 + 7) =
      8 * (hi - lo + 1).log2 + 7 := by
  rw [right_length h, Nat.log2_def (hi - lo + 1), if_pos (by lia : 2 ≤ hi - lo + 1)]
  lia

private structure Summary (input : Array (Word w)) (target : Word w) (lo hi : Nat)
    (s t : RAMState w 6) (cost : RAMCost w 6) : Prop where
  memory : t.Memory = s.Memory
  addresses : cost.addresses ⊆ inputRegion input
  found : t.Flags .eq = true →
    let i := (t.Registers middle).toNat
    lo ≤ i ∧ i ≤ hi ∧ input[i]? = some target
  not_found : t.Flags .eq = false → SortedWords input →
    ∀ i, lo ≤ i → i ≤ hi → input[i]? ≠ some target
  time : cost.time ≤ 8 * (hi - lo + 1).log2 + 7
  worst : 0 < w → s.Memory = (fun _ => 0) → s.Registers key = 1 →
    cost.time = 8 * (hi - lo + 1).log2 + 7

private theorem loop_spec (input : Array (Word w)) (target : Word w) (n lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi < input.size) (hn : hi - lo < n) (s : RAMState w 6)
    (hmem : RepresentsArray input s.Memory)
    (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (hk : s.Registers key = target)
    (h1 : s.Registers one = 1) (ha : s.Flags .ult = true) :
    ∃ cost t, Completes (instructions (whileLoop .ult (body w))) s cost t ∧
      Summary input target lo hi s t cost := by
  induction n generalizing lo hi s with
  | zero => lia
  | succ n ih =>
    let pivot := lo + (hi - lo) / 2
    have hp := pivot_bounds hlo
    have hpi : pivot < input.size := by lia
    have hhw := hmem.index_lt hhi
    have hm : midpoint s = BitVec.ofNat w pivot := by
      simpa only [midpoint, hl, hh, h1] using wordAddress_mid lo hi hlo hhw
    have hread := hmem.read_of_eq hpi hm
    have hprobe := ofNat_mem_inputRegion input pivot hpi
    have hpn := hmem.toNat_of_eq hpi hm
    have hln := hmem.toNat_of_eq (by lia : lo < input.size) hl
    have hhn := hmem.toNat_of_eq hhi hh
    by_cases heq : input[pivot] = target
    · have heq' : s.Memory (midpoint s) = s.Registers key := by simpa only [hread, hk] using heq
      have hb := body_found s heq'
      refine ⟨_, _, hb.while_stop ha (by simp), ?_⟩
      constructor
      · simp
      · simpa only [add_zero, Finset.singleton_subset_iff, hm] using hprobe
      · intro _
        simpa [hpn, hpi, heq, pivot] using hp
      · simp
      · dsimp; lia
      · intro hw hz hk1
        have hbad : (0 : Word w) = 1 := by simpa [hz, hk1] using heq'
        simp [ne_of_gt hw] at hbad
    · have hne : s.Memory (midpoint s) ≠ s.Registers key := by simpa only [hread, hk] using heq
      by_cases hlt : input[pivot].toNat < target.toNat
      · have hcmp : (s.Memory (midpoint s)).toNat < (s.Registers key).toNat := by
          simpa only [hread, hk] using hlt
        by_cases hright : pivot < hi
        · let next := (checked s false true).writeRegister lower (BitVec.ofNat w (pivot + 1))
          have hb : Completes (instructions (body w)) s ⟨8, {BitVec.ofNat w pivot}⟩ next := by
            simpa only [next, hm, h1, wordAddress_succ] using body_right s hne hcmp
              (by simpa only [hpn, hhn] using hright)
          obtain ⟨cost, t, hr, hs⟩ := ih (pivot + 1) hi (by lia) hhi (by lia) next
            (by simpa [next] using hmem) (by simp [next]) (by simp [next, hh])
            (by simp [next, hk]) (by simp [next, h1]) (by simp [next])
          refine ⟨_, t, completes_while_true .ult (body w) ha hb hr, ?_⟩
          constructor
          · simpa [next] using hs.memory
          · exact Finset.union_subset (Finset.singleton_subset_iff.mpr hprobe) hs.addresses
          · intro hf
            obtain ⟨hi₁, hi₂, hm⟩ := hs.found hf
            exact ⟨by lia, hi₂, hm⟩
          · intro hf hsorted i hil hih
            by_cases hip : i ≤ pivot
            · exact hsorted.exclude_left hpi hlt i hip
            · exact hs.not_found hf hsorted i (by lia) hih
          · exact step_time_bound hs.time (by lia) (by simp [pivot, right_length hright])
          · intro hw hz hk1
            simpa only [RAMCost.mk_add, hs.worst hw (by simp [next, hz])
              (by simp [next, hk1])] using right_log hright
        · have hb := body_stop_right s hne hcmp (by simpa only [hpn, hhn] using hright)
          refine ⟨_, _, hb.while_stop ha (by simp), ?_⟩
          constructor
          · simp
          · simpa only [add_zero, Finset.singleton_subset_iff, hm] using hprobe
          · simp
          · intro _ hsorted i hil hih
            exact hsorted.exclude_left hpi hlt i (by lia)
          · dsimp; lia
          · intro _ _ _
            have hlen : hi - lo + 1 = 1 := by dsimp [pivot] at *; lia
            simp [hlen, Nat.log2_def]
      · have hcmp : ¬(s.Memory (midpoint s)).toNat < (s.Registers key).toNat := by
          simpa only [hread, hk] using hlt
        have hgt : target.toNat < input[pivot].toNat := by grind [BitVec.toNat_inj]
        by_cases hleft : lo < pivot
        · let next := (checked s false true).writeRegister upper (BitVec.ofNat w (pivot - 1))
          have hb : Completes (instructions (body w)) s ⟨8, {BitVec.ofNat w pivot}⟩ next := by
            simpa only [next, hm, h1, wordAddress_pred pivot (hmem.index_lt hpi) (by lia)] using
              body_left s hne hcmp (by simpa only [hln, hpn] using hleft)
          obtain ⟨cost, t, hr, hs⟩ := ih lo (pivot - 1) (by lia) (by lia) (by lia) next
            (by simpa [next] using hmem) (by simp [next, hl]) (by simp [next])
            (by simp [next, hk]) (by simp [next, h1]) (by simp [next])
          refine ⟨_, t, completes_while_true .ult (body w) ha hb hr, ?_⟩
          constructor
          · simpa [next] using hs.memory
          · exact Finset.union_subset (Finset.singleton_subset_iff.mpr hprobe) hs.addresses
          · intro hf
            obtain ⟨hi₁, hi₂, hm⟩ := hs.found hf
            exact ⟨hi₁, by lia, hm⟩
          · intro hf hsorted i hil hih
            by_cases hip : pivot ≤ i
            · exact hsorted.exclude_right hpi hgt i hip (by lia)
            · exact hs.not_found hf hsorted i hil (by lia)
          · apply step_time_bound hs.time (by lia)
            simpa only [pivot, left_length hleft] using
              Nat.div_le_div_right (by lia : hi - lo ≤ hi - lo + 1)
          · intro hw hz hk1
            simp [hz, hk1, BitVec.toNat_one hw] at hcmp
        · have hb := body_stop_left s hne hcmp (by simpa only [hln, hpn] using hleft)
          refine ⟨_, _, hb.while_stop ha (by simp), ?_⟩
          constructor
          · simp
          · simpa only [add_zero, Finset.singleton_subset_iff, hm] using hprobe
          · simp
          · intro _ hsorted i hil hih
            exact hsorted.exclude_right hpi hgt i (by lia) (by lia)
          · dsimp; lia
          · intro hw hz hk1
            simp [hz, hk1, BitVec.toNat_one hw] at hcmp

/-- Exact worst-case primitive count, including interval initialization. -/
def binarySearchTime (n : Nat) : Nat := if n = 0 then 1 else 8 * n.log2 + 10

@[simp] private def initialized (s : RAMState w 6) : RAMState w 6 :=
  (s.writeRegister lower 0).writeRegister one 1

private theorem setup_completes (s : RAMState w 6) :
    Completes (instructions (setup w)) s ⟨2, ∅⟩ (initialized s) :=
  ⟨2, by simp [setup, runCode, step]⟩

private structure ResultSpec (input : Search.Input (Word w))
    (s t : RAMState w 6) (cost : RAMCost w 6) : Prop where
  correct : SortedWords input.data → Search.search.spec input (searchOutput middle t)
  memory : t.Memory = s.Memory
  addresses : cost.addresses ⊆ inputRegion input.data
  time : cost.time ≤ binarySearchTime input.data.size
  worst : 0 < w → s.Memory = (fun _ => 0) → s.Registers key = 1 →
    cost.time = binarySearchTime input.data.size

private theorem search_spec (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) :
    ∃ cost t, Completes (instructions (binarySearch w)) s cost t ∧ ResultSpec input s t cost := by
  let start := s.writeFlag .eq false
  let rest : Prog (WordRAM w 6) Unit := do setup w; whileLoop .ult (body w)
  have hclear : Completes [.clearFlag .eq] s ⟨1, ∅⟩ start :=
    ⟨1, by simp [runCode, step, start]⟩
  have hactive := hinput.nonempty_eq
  have hlast := hinput.last_eq
  have hkey := hinput.key_eq
  by_cases hn : input.data.size = 0
  · have hb : Completes (instructions (branch .ult rest (pure ()))) start 0 start :=
      completes_branch (by simp [start, hactive, hn])
    have hc := hclear.append hb
    refine ⟨⟨1, ∅⟩ + 0, start, ?_, ?_⟩
    · simpa only [binarySearch, ifThenElse_flag, rest, instructions_lift_bind,
      List.singleton_append] using hc
    constructor
    · intro _
      simp only [searchOutput, start, RAMState.writeFlag_flags, ↓reduceIte,
        Bool.false_eq_true, Search.search_spec_none]
      grind [Array.mem_iff_getElem?]
    · simp [start]
    · simp
    · simp [binarySearchTime, hn]
    · intro _ _ _; simp [binarySearchTime, hn]
  · obtain ⟨cost, t, hr, hs⟩ := loop_spec input.data input.key input.data.size 0
      (input.data.size - 1) (by lia) (by lia) (by lia) (initialized start)
      (by simpa [start] using hinput.toRepresentsSearchInput.toRepresentsArray)
      (by simp) (by simp [start, hlast]) (by simp [start, hkey])
      (by simp) (by simp [start, hactive, hn])
    have hb : Completes (instructions (branch .ult rest (pure ()))) start (⟨2, ∅⟩ + cost) t :=
      completes_branch (by simpa [rest, start, hactive, hn] using (setup_completes start).append hr)
    have hc := hclear.append hb
    refine ⟨⟨1, ∅⟩ + (⟨2, ∅⟩ + cost), t, ?_, ?_⟩
    · simpa only [binarySearch, ifThenElse_flag, rest, instructions_lift_bind,
      List.singleton_append] using hc
    constructor
    · intro hsorted
      simp only [searchOutput]
      split_ifs with hf
      · obtain ⟨_, hbound, hmatch⟩ := hs.found hf
        exact ⟨by lia, hmatch⟩
      · have hnone := hs.not_found (by simpa using hf) hsorted
        simp only [Search.search_spec_none]
        grind [Array.mem_iff_getElem?]
    · simpa [start] using hs.memory
    · simpa using hs.addresses
    · have ht := hs.time
      have hlen : input.data.size - 1 - 0 + 1 = input.data.size := by lia
      simp only [RAMCost.mk_add, binarySearchTime, if_neg hn]
      rw [hlen] at ht
      lia
    · intro hw hz hk1
      have ht := hs.worst hw (by simp [start, hz]) (by simp [start, hk1])
      have hlen : input.data.size - 1 - 0 + 1 = input.data.size := by lia
      simp only [RAMCost.mk_add, binarySearchTime, if_neg hn]
      rw [hlen] at ht
      lia

/-- Binary search terminates on every representing state, even without sortedness. -/
theorem binarySearch_terminates (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) :
    ∃ fuel cost t, execute fuel (binarySearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) := by
  obtain ⟨cost, t, hc, _⟩ := search_spec input s hinput
  obtain ⟨fuel, hf⟩ := hc.execute
  exact ⟨fuel, cost, t, hf⟩

/-- Joint correctness and resource guarantees for a completed execution of the uniform program. -/
theorem binarySearch_run_spec (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    let t := final.ram
    let cost := result.tell
    (SortedWords input.data → Search.search.spec input (searchOutput middle t)) ∧
      t.Memory = s.Memory ∧ cost.addresses ⊆ inputRegion input.data ∧
      cost.time ≤ binarySearchTime input.data.size := by
  obtain ⟨cost, t, hc, hs⟩ := search_spec input s hinput
  obtain ⟨hcost, hstate⟩ := hc.unique (by simpa only [execute_eq_runCode] using hrun)
  simpa only [hcost, hstate] using ⟨hs.correct, hs.memory, hs.addresses, hs.time⟩

/-- On sorted input, binary search implements the abstract search problem. -/
theorem binarySearch_correct_of_execute (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    let problem := Search.binarySearch (fun a b : Word w => a.toNat ≤ b.toNat)
    problem.admissible input → problem.spec input (searchOutput middle final.ram) := by
  simpa using (binarySearch_run_spec input s hinput hrun).left

/-- A cleared equality flag characterizes absence on sorted input. -/
theorem binarySearch_none_iff (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) (hsorted : SortedWords input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    final.ram.Flags .eq = false ↔ input.key ∉ input.data := by
  simpa [searchOutput] using Search.search_none_iff
    (binarySearch_correct_of_execute input s hinput hrun (by simpa using hsorted))

/-- The middle register holds an in-bounds matching address when equality is set. -/
theorem binarySearch_of_some (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s) (hsorted : SortedWords input.data)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final))
    (hfound : final.ram.Flags .eq = true) :
    let i := (final.ram.Registers middle).toNat
    i < input.data.size ∧ input.data[i]? = some input.key := by
  simpa only [Search.binarySearch_spec, searchOutput_of_found middle _ hfound,
    Search.search_spec_some, Search.IsMatch] using
    binarySearch_correct_of_execute input s hinput hrun (by simpa using hsorted)

/-- Binary search preserves every memory cell. -/
theorem binarySearch_memory (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    final.ram.Memory = s.Memory := (binarySearch_run_spec input s hinput hrun).right.left

/-- The logarithmic time bound does not require sortedness. -/
theorem binarySearch_time_le (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.time ≤ binarySearchTime input.data.size :=
  (binarySearch_run_spec input s hinput hrun).right.right.right

/-- All memory probes belong to the input array. -/
theorem binarySearch_addresses_subset (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.addresses ⊆ inputRegion input.data :=
  (binarySearch_run_spec input s hinput hrun).right.right.left

/-- The six registers use no auxiliary memory cells. -/
theorem binarySearch_auxiliarySpace (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.auxiliarySpace (inputRegion input.data) = 0 := by
  simp only [RAMCost.auxiliarySpace, Finset.sdiff_eq_empty_iff_subset.mpr
    (binarySearch_addresses_subset input s hinput hrun), Finset.card_empty]

/-- The total footprint equals the input size, including unread input cells. -/
theorem binarySearch_totalSpace (input : Search.Input (Word w)) (s : RAMState w 6)
    (hinput : RepresentsBoundedSearchInput input key upper s)
    {fuel : Nat} {result : AddWriter (RAMCost w 6) Unit} {final : ExecutionState w 6}
    (hrun : execute fuel (binarySearch w) s = some (result, final)) :
    result.tell.totalSpace (inputRegion input.data) = input.data.size := by
  simp only [RAMCost.totalSpace, Finset.union_eq_right.mpr
    (binarySearch_addresses_subset input s hinput hrun), inputRegion_card input.data hinput.fits]

/-- Total correctness of this fixed, runtime-size-independent program on every representing
state. The output remains in the machine's registers and flags. -/
theorem binarySearch_correct (w : Nat) :
    let problem := (Search.binarySearch (fun a b : Word w => a.toNat ≤ b.toNat))
    let repInput := fun input => RepresentsBoundedSearchInput input key upper
    problem.Solves (binarySearch w) Executes repInput (RepresentsSearchOutput middle) := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s ha hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨searchOutput middle t, representsSearchOutput_searchOutput middle t,
      binarySearch_correct_of_execute input s hi hr ha⟩

/-- Termination, the worst-case time bound, and zero auxiliary memory for every represented
input. Resource guarantees do not require sortedness. -/
theorem binarySearch_runsWithin (w : Nat) :
    let repInput := fun input => RepresentsBoundedSearchInput input key upper
    let bound := fun (input : Search.Input (Word w)) (cost : RAMCost w 6) =>
      cost.time ≤ binarySearchTime input.data.size ∧
        cost.auxiliarySpace (inputRegion input.data) = 0
    Search.RunsWithin (binarySearch w) Executes repInput bound := by
  constructor
  · intro input s _ hi
    obtain ⟨cost, t, hc, _⟩ := search_spec input s hi
    exact ⟨cost, t, hc.executes⟩
  · intro input s _ hi cost t hr
    obtain ⟨fuel, remaining, hr⟩ := hr
    exact ⟨binarySearch_time_le input s hi hr, binarySearch_auxiliarySpace input s hi hr⟩

private theorem arrayMemory_replicate_zero (n : Nat) :
    arrayMemory (Array.replicate n (0 : Word w)) = fun _ => 0 := by
  funext addr
  simp only [arrayMemory, Array.getElem?_replicate]
  split <;> rfl

/-- Zeros searched for one attain the time bound at every fitting length and positive width. -/
theorem binarySearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    let input := Array.replicate n (0 : Word w)
    let s := binarySearchState input 1
    ∃ fuel cost t, execute fuel (binarySearch w) s = some (⟨(), cost⟩, ⟨t, 0⟩) ∧
      cost.time = binarySearchTime n := by
  let input := Array.replicate n (0 : Word w)
  have hrep := binarySearchState_represents input 1 (by simpa [input] using hn)
  obtain ⟨cost, t, hc, hs⟩ := search_spec ⟨input, 1⟩ _ hrep
  obtain ⟨fuel, hf⟩ := hc.execute
  refine ⟨fuel, cost, t, hf, ?_⟩
  simpa [input] using hs.worst hw (arrayMemory_replicate_zero n)
    (by simp [binarySearchState])

/-- Every fitting length has a sorted worst-case input for this same uniform program. -/
theorem binarySearch_exists_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ∃ (input : Array (Word w)) (target : Word w),
      input.size = n ∧ input.size ≤ 2 ^ w ∧ SortedWords input ∧ target ∉ input ∧
      ∃ fuel cost t,
        execute fuel (binarySearch w) (binarySearchState input target) =
          some (⟨(), cost⟩, ⟨t, 0⟩) ∧ cost.time = binarySearchTime n := by
  refine ⟨Array.replicate n 0, 1, by simp, by simpa using hn, ?_, ?_, ?_⟩
  · simp [SortedWords, Search.SortedBy]
  · simp [ne_of_gt hw]
  · exact binarySearch_worstCase w n hw hn

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
