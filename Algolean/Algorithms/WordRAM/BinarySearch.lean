/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Mathlib.Data.Nat.Log

/-!
# Binary search with six word-RAM registers

Adapted from https://github.com/Shreyas4991/Algolean/pull/89 to the register-only model.
Inclusive bounds support all `2 ^ w` input cells. The midpoint is `lo + (hi - lo) / 2`;
boundary comparisons prevent either endpoint from wrapping. All word computations are queries.
The structural recursion budget supplies control flow and is not itself charged.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

namespace BinarySearch

/-- Inclusive lower endpoint. -/
abbrev lower : Register 6 := 0
/-- Inclusive upper endpoint. -/
abbrev upper : Register 6 := 1
/-- Midpoint, and result register on success. -/
abbrev middle : Register 6 := 2
/-- Word loaded at the midpoint. -/
abbrev value : Register 6 := 3
/-- Search key supplied in the initial state. -/
abbrev key : Register 6 := 4
/-- Constant one for shifts and endpoint updates. -/
abbrev one : Register 6 := 5

/-- Search a nonempty inclusive interval held in the endpoint registers. -/
def loop (w : Nat) : Nat → Prog (WordRAM w 6) Unit
  | 0 => pure ()
  | fuel + 1 => do
    binop (w := w) .sub middle upper lower
    binop (w := w) .shr middle middle one
    binop (w := w) .add middle lower middle
    load (w := w) value middle
    cmp (w := w) .eq value key
    branch .eq (pure ()) (do
      cmp (w := w) .ult value key
      branch .ult (do
        cmp (w := w) .ult middle upper
        branch .ult (do
          binop (w := w) .add lower middle one
          loop w fuel) (pure ())) (do
        cmp (w := w) .ult lower middle
        branch .ult (do
          binop (w := w) .sub upper middle one
          loop w fuel) (pure ())))

end BinarySearch

/-- Search `n` cells, with the key preloaded in `BinarySearch.key`.
The result flag is cleared first; nonempty input also initializes the endpoints and constant one. -/
def binarySearch (w n : Nat) : Prog (WordRAM w 6) Unit := do
  clearFlag (w := w) (k := 6) .eq
  if n = 0 then return ()
  set (w := w) BinarySearch.lower 0
  set (w := w) BinarySearch.upper (BitVec.ofNat w (n - 1))
  set (w := w) BinarySearch.one 1
  BinarySearch.loop w n

/-- Input memory and key register, supplied before the charged search starts. -/
@[simps] def binarySearchState (input : Array (BitVec w)) (target : Word w) : RAMState w 6 :=
  ⟨arrayMemory input, fun r => if r = BinarySearch.key then target else 0, fun _ => false⟩

@[simp, grind =] theorem binarySearchState_memory (input : Array (BitVec w)) (target : Word w) :
    (binarySearchState input target).Memory = arrayMemory input := rfl

/-- Nondecreasing order on the unsigned values of input words; duplicates are permitted. -/
def SortedWords (input : Array (BitVec w)) : Prop :=
  ∀ i j, (hi : i < input.size) → (hj : j < input.size) →
    i ≤ j → input[i].toNat ≤ input[j].toNat

section CorrectnessAndComplexity

open BinarySearch

attribute [local simp] loop runQuery BinOp.eval CmpOp.eval
  lower upper middle value key one

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

@[simp] private def atMid (s : RAMState w 6) (pivot : Nat) : RAMState w 6 :=
  (((s.writeRegister middle (BitVec.ofNat w pivot)).writeRegister value
    (s.Memory (BitVec.ofNat w pivot))).writeFlag .eq false).writeFlag .ult true

private theorem loop_memory (fuel : Nat) (s : RAMState w 6) :
    (((loop w fuel).runStateM timeAndSpaceCost).run s).snd.Memory = s.Memory := by
  induction fuel generalizing s <;> simp_all
  split_ifs <;> simp_all

private theorem loop_correct_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (fuel lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi < input.size) (s : RAMState w 6)
    (hmem : s.Memory = arrayMemory input) (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (hk : s.Registers key = target)
    (h1 : s.Registers one = 1) (hflag : s.Flags .eq = false)
    (hresult : (((loop w fuel).runStateM timeAndSpaceCost).run s).snd.Flags .eq = true) :
    let result := ((loop w fuel).runStateM timeAndSpaceCost).run s
    let addr := result.snd.Registers middle
    lo ≤ addr.toNat ∧ addr.toNat ≤ hi ∧ input[addr.toNat]? = some target := by
  induction fuel generalizing lo hi s with
  | zero => simp_all
  | succ fuel ih =>
    let pivot := lo + (hi - lo) / 2
    have hp : lo ≤ pivot ∧ pivot ≤ hi := by dsimp [pivot]; lia
    have hpw : pivot < 2 ^ w := by lia
    have hlw : lo < 2 ^ w := by lia
    have hhw : hi < 2 ^ w := by lia
    have hlmod := Nat.mod_eq_of_lt hlw
    have hhmod := Nat.mod_eq_of_lt hhw
    have hpmod := Nat.mod_eq_of_lt hpw
    have hm := wordAddress_mid lo hi hlo (lt_of_lt_of_le hhi hfits)
    have hmnat := congrArg BitVec.toNat hm
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at hmnat
    have hr (hn : pivot < hi) := ih (pivot + 1) hi (by lia) hhi
      ((atMid s pivot).writeRegister lower (BitVec.ofNat w (pivot + 1)))
      (by simp [hmem]) (by simp) (by simp [hh])
      (by simp [hk]) (by simp [h1]) (by simp)
    have hleft (hn : lo < pivot) := ih lo (pivot - 1) (by lia) (by lia)
      ((atMid s pivot).writeRegister upper (BitVec.ofNat w (pivot - 1)))
      (by simp [hmem]) (by simp [hl]) (by simp)
      (by simp [hk]) (by simp [h1]) (by simp)
    clear ih
    simp_all
    split_ifs at hresult ⊢ <;> simp_all <;>
      grind only [wordAddress_eq_iff, = wordAddress_pred, = wordAddress_succ,
        = wordAddress_toNat, = arrayMemory_ofNat,
        Array.getElem?_eq_getElem, Nat.mod_eq_of_lt]

private theorem loop_correct_not_found (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input) (fuel lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi < input.size) (hfuel : hi - lo < fuel) (s : RAMState w 6)
    (hmem : s.Memory = arrayMemory input) (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (hk : s.Registers key = target)
    (h1 : s.Registers one = 1)
    (hresult : (((loop w fuel).runStateM timeAndSpaceCost).run s).snd.Flags .eq = false) :
    ∀ i, lo ≤ i → i ≤ hi → input[i]? ≠ some target := by
  induction fuel generalizing lo hi s with
  | zero => lia
  | succ fuel ih =>
    let pivot := lo + (hi - lo) / 2
    have hp : lo ≤ pivot ∧ pivot ≤ hi := by dsimp [pivot]; lia
    have hpw : pivot < 2 ^ w := by lia
    have hlw : lo < 2 ^ w := by lia
    have hhw : hi < 2 ^ w := by lia
    have hlmod := Nat.mod_eq_of_lt hlw
    have hhmod := Nat.mod_eq_of_lt hhw
    have hpmod := Nat.mod_eq_of_lt hpw
    have hm := wordAddress_mid lo hi hlo (lt_of_lt_of_le hhi hfits)
    have hmnat := congrArg BitVec.toNat hm
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at hmnat
    have hr (hn : pivot < hi) := ih (pivot + 1) hi (by lia) hhi (by lia)
      ((atMid s pivot).writeRegister lower (BitVec.ofNat w (pivot + 1)))
      (by simp [hmem]) (by simp) (by simp [hh])
      (by simp [hk]) (by simp [h1])
    have hleft (hn : lo < pivot) := ih lo (pivot - 1) (by lia) (by lia) (by lia)
      ((atMid s pivot).writeRegister upper (BitVec.ofNat w (pivot - 1)))
      (by simp [hmem]) (by simp [hl]) (by simp)
      (by simp [hk]) (by simp [h1])
    have heql := wordAddress_eq_iff pivot lo hpw (by lia)
    have heqh := wordAddress_eq_iff pivot hi hpw (by lia)
    have hpred (hpos : 0 < pivot) := wordAddress_pred pivot hpw hpos
    have hsucc := wordAddress_succ (w := w) pivot
    clear ih
    simp_all
    split_ifs at hresult <;> simp_all <;>
      grind only [SortedWords, = arrayMemory_ofNat, Array.getElem?_eq_getElem,
        BitVec.eq_of_toNat_eq]

private def initialized (s : RAMState w 6) (n : Nat) : RAMState w 6 :=
  (((s.writeFlag .eq false).writeRegister lower 0).writeRegister upper
    (BitVec.ofNat w (n - 1))).writeRegister one 1

attribute [local simp] binarySearch initialized

/-- The equality flag records success and the middle register holds a matching address. -/
theorem binarySearch_correct (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run
      (binarySearchState input target)
    let addr := result.snd.Registers middle
    if result.snd.Flags .eq then
      addr.toNat < input.size ∧ input[addr.toNat]? = some target
    else target ∉ input := by
  by_cases hn : input.size = 0
  · simp [Array.eq_empty_of_size_eq_zero hn]
  · have hnot := loop_correct_not_found input target hfits hsorted input.size 0 (input.size - 1)
      (by lia) (by lia) (by lia) (initialized (binarySearchState input target) input.size)
      (by simp) (by simp) (by simp) (by simp) (by simp)
    have hfound := loop_correct_found input target hfits input.size 0 (input.size - 1)
      (by lia) (by lia) (initialized (binarySearchState input target) input.size)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    simp only [initialized] at hnot hfound
    simp [hn]
    split <;> grind [Array.mem_iff_getElem?]

/-- Failure is equivalent to the key being absent from sorted input. -/
theorem binarySearch_none_iff (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run
      (binarySearchState input target)
    result.snd.Flags .eq = false ↔ target ∉ input := by
  have h := binarySearch_correct input target hfits hsorted
  grind [Array.mem_iff_getElem?]

/-- A successful search leaves an in-bounds matching address in the middle register. -/
theorem binarySearch_of_some (input : Array (BitVec w)) (target : Word w)
    (hfits : input.size ≤ 2 ^ w) (hsorted : SortedWords input)
    (hfound : (((binarySearch w input.size).runStateM timeAndSpaceCost).run
      (binarySearchState input target)).snd.Flags .eq = true) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run
      (binarySearchState input target)
    let addr := result.snd.Registers middle
    addr.toNat < input.size ∧ input[addr.toNat]? = some target := by
  have h := binarySearch_correct input target hfits hsorted
  grind

/-- All input and non-input memory is preserved. -/
theorem binarySearch_memory (n : Nat) (s : RAMState w 6) :
    let result := ((binarySearch w n).runStateM timeAndSpaceCost).run s
    result.snd.Memory = s.Memory := by
  by_cases hn : n = 0
  · simp [hn]
  · simpa [hn] using loop_memory n (initialized s n)

private theorem log2_half_bound (n k : Nat) (hn : 2 ≤ n) (hk : k ≤ n / 2) :
    k.log2 + 1 ≤ n.log2 := by
  have h : k.log2 ≤ (n / 2).log2 := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hk
  rw [Nat.log2_def n, if_pos hn]
  lia

private theorem loop_time_le (fuel lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < 2 ^ w)
    (s : RAMState w 6) (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (h1 : s.Registers one = 1) :
    (((loop w fuel).runStateM timeAndSpaceCost).run s).fst.tell.time ≤
      8 * (hi - lo + 1).log2 + 7 := by
  induction fuel generalizing lo hi s with
  | zero => simp
  | succ fuel ih =>
    let pivot := lo + (hi - lo) / 2
    have hp : lo ≤ pivot ∧ pivot ≤ hi := by dsimp [pivot]; lia
    have hpw : pivot < 2 ^ w := by lia
    have hlw : lo < 2 ^ w := by lia
    have hhw : hi < 2 ^ w := by lia
    have hlmod := Nat.mod_eq_of_lt hlw
    have hhmod := Nat.mod_eq_of_lt hhw
    have hpmod := Nat.mod_eq_of_lt hpw
    have hm := wordAddress_mid lo hi hlo hhi
    have hmnat := congrArg BitVec.toNat hm
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at hmnat
    have hr (hn : pivot < hi) := ih (pivot + 1) hi (by lia) hhi
      ((atMid s pivot).writeRegister lower (BitVec.ofNat w (pivot + 1)))
      (by simp) (by simp [hh]) (by simp [h1])
    have hleft (hn : lo < pivot) := ih lo (pivot - 1) (by lia) (by lia)
      ((atMid s pivot).writeRegister upper (BitVec.ofNat w (pivot - 1)))
      (by simp [hl]) (by simp) (by simp [h1])
    have hrl (hn : pivot < hi) := log2_half_bound (hi - lo + 1) (hi - (pivot + 1) + 1)
      (by lia) (by dsimp [pivot]; lia)
    have hll (hn : lo < pivot) := log2_half_bound (hi - lo + 1) (pivot - 1 - lo + 1)
      (by lia) (by dsimp [pivot]; lia)
    clear ih
    simp_all
    split_ifs <;> simp_all <;>
      grind only [wordAddress_eq_iff, = wordAddress_pred, = wordAddress_succ]

/-- Exact worst-case query count: four setup queries, then up to eight per halving step. -/
def binarySearchTime (n : Nat) : Nat := if n = 0 then 1 else 8 * n.log2 + 11

/-- The logarithmic time bound holds without sortedness, including a full address space. -/
theorem binarySearch_time_le (n : Nat) (hfits : n ≤ 2 ^ w) (s : RAMState w 6) :
    let result := ((binarySearch w n).runStateM timeAndSpaceCost).run s
    result.fst.tell.time ≤ binarySearchTime n := by
  by_cases hn : n = 0
  · simp [hn, binarySearchTime]
  · have ht := loop_time_le n 0 (n - 1) (by lia) (by lia) (initialized s n)
      (by simp) (by simp) (by simp)
    have hn1 : n - 1 + 1 = n := by lia
    simp_all [binarySearchTime]
    lia

private theorem loop_addresses_subset (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (fuel lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi < input.size)
    (s : RAMState w 6) (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (h1 : s.Registers one = 1) :
    (((loop w fuel).runStateM timeAndSpaceCost).run s).fst.tell.addresses ⊆ inputRegion input := by
  induction fuel generalizing lo hi s with
  | zero => simp
  | succ fuel ih =>
    let pivot := lo + (hi - lo) / 2
    have hp : lo ≤ pivot ∧ pivot ≤ hi := by dsimp [pivot]; lia
    have hpw : pivot < 2 ^ w := by lia
    have hlw : lo < 2 ^ w := by lia
    have hhw : hi < 2 ^ w := by lia
    have hlmod := Nat.mod_eq_of_lt hlw
    have hhmod := Nat.mod_eq_of_lt hhw
    have hpmod := Nat.mod_eq_of_lt hpw
    have hm := wordAddress_mid lo hi hlo (lt_of_lt_of_le hhi hfits)
    have hmnat := congrArg BitVec.toNat hm
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at hmnat
    have hmem := ofNat_mem_inputRegion input pivot (by lia)
    have hr (hn : pivot < hi) := ih (pivot + 1) hi (by lia) hhi
      ((atMid s pivot).writeRegister lower (BitVec.ofNat w (pivot + 1)))
      (by simp) (by simp [hh]) (by simp [h1])
    have hleft (hn : lo < pivot) := ih lo (pivot - 1) (by lia) (by lia)
      ((atMid s pivot).writeRegister upper (BitVec.ofNat w (pivot - 1)))
      (by simp [hl]) (by simp) (by simp [h1])
    clear ih
    simp_all
    split_ifs <;> simp_all <;>
      grind only [wordAddress_eq_iff, = wordAddress_pred, = wordAddress_succ,
        Finset.insert_subset_iff]

/-- All probed cells belong to the input region. -/
theorem binarySearch_addresses_subset (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (s : RAMState w 6) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run s
    result.fst.tell.addresses ⊆ inputRegion input := by
  by_cases hn : input.size = 0
  · simp [hn]
  · simpa [hn] using loop_addresses_subset input hfits input.size 0 (input.size - 1)
      (by lia) (by lia) (initialized s input.size) (by simp) (by simp) (by simp)

/-- Six register words suffice; no memory outside the input is accessed. -/
theorem binarySearch_auxiliarySpace (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (s : RAMState w 6) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run s
    result.fst.tell.auxiliarySpace (inputRegion input) = 6 := by
  simp only [RAMCost.auxiliarySpace,
    Finset.sdiff_eq_empty_iff_subset.mpr (binarySearch_addresses_subset input hfits s),
    Finset.card_empty, Nat.add_zero]

/-- Total storage includes the input and the six registers. -/
theorem binarySearch_totalSpace (input : Array (BitVec w))
    (hfits : input.size ≤ 2 ^ w) (s : RAMState w 6) :
    let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run s
    result.fst.tell.totalSpace (inputRegion input) = input.size + 6 := by
  simp only [RAMCost.totalSpace,
    Finset.union_eq_right.mpr (binarySearch_addresses_subset input hfits s),
    inputRegion_card input hfits, Nat.add_comm]

private theorem arrayMemory_replicate_zero (n : Nat) :
    arrayMemory (Array.replicate n (0 : BitVec w)) = fun _ => 0 := by
  funext addr
  simp only [arrayMemory, Array.getElem?_replicate]
  split <;> rfl

private theorem loop_worstCase (hw : 0 < w) (fuel lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi < 2 ^ w) (hfuel : hi - lo < fuel) (s : RAMState w 6)
    (hmem : s.Memory = fun _ => 0) (hl : s.Registers lower = BitVec.ofNat w lo)
    (hh : s.Registers upper = BitVec.ofNat w hi) (hk : s.Registers key = 1)
    (h1 : s.Registers one = 1) :
    (((loop w fuel).runStateM timeAndSpaceCost).run s).fst.tell.time =
      8 * (hi - lo + 1).log2 + 7 := by
  induction fuel generalizing lo hi s with
  | zero => lia
  | succ fuel ih =>
    let pivot := lo + (hi - lo) / 2
    have hp : lo ≤ pivot ∧ pivot ≤ hi := by dsimp [pivot]; lia
    have hpw : pivot < 2 ^ w := by lia
    have hlw : lo < 2 ^ w := by lia
    have hhw : hi < 2 ^ w := by lia
    have hlmod := Nat.mod_eq_of_lt hlw
    have hhmod := Nat.mod_eq_of_lt hhw
    have hpmod := Nat.mod_eq_of_lt hpw
    have hm := wordAddress_mid lo hi hlo hhi
    have hmnat := congrArg BitVec.toNat hm
    simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub,
      BitVec.toNat_ofNat] at hmnat
    have hr (hn : pivot < hi) := ih (pivot + 1) hi (by lia) hhi (by lia)
      ((atMid s pivot).writeRegister lower (BitVec.ofNat w (pivot + 1)))
      (by simp [hmem]) (by simp) (by simp [hh])
      (by simp [hk]) (by simp [h1])
    have hhalf (hn : pivot < hi) : hi - (pivot + 1) + 1 = (hi - lo + 1) / 2 := by
      dsimp [pivot] at *; lia
    have hlog := Nat.log2_def (hi - lo + 1)
    clear ih
    simp_all [BitVec.toNat_one hw, ne_of_gt hw]
    split_ifs <;> simp_all <;>
      grind only [wordAddress_eq_iff, = wordAddress_pred, = wordAddress_succ]

/-- Zeros searched for one attain the time bound at every representable length and
positive word width. Every unsuccessful iteration follows the larger, right half. -/
theorem binarySearch_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    let input := Array.replicate n (0 : BitVec w)
    let result := ((binarySearch w n).runStateM timeAndSpaceCost).run (binarySearchState input 1)
    result.fst.tell.time = binarySearchTime n := by
  by_cases hzero : n = 0
  · simp [hzero, binarySearchTime]
  · have ht := loop_worstCase hw n 0 (n - 1) (by lia) (by lia) (by lia)
      (initialized (binarySearchState (Array.replicate n 0) 1) n)
      (arrayMemory_replicate_zero n) (by simp) (by simp)
      (by simp) (by simp)
    have hn1 : n - 1 + 1 = n := by lia
    simp_all [binarySearchTime]
    lia

/-- A sorted worst-case instance exists at every length fitting in positive-width memory. -/
theorem binarySearch_exists_worstCase (w n : Nat) (hw : 0 < w) (hn : n ≤ 2 ^ w) :
    ∃ (input : Array (BitVec w)) (target : Word w),
      let result := ((binarySearch w input.size).runStateM timeAndSpaceCost).run
        (binarySearchState input target)
      input.size = n ∧ input.size ≤ 2 ^ w ∧ SortedWords input ∧ target ∉ input ∧
        result.fst.tell.time = binarySearchTime n := by
  refine ⟨Array.replicate n 0, 1, by simp, by simpa using hn, ?_, ?_, ?_⟩
  · simp [SortedWords]
  · simp [ne_of_gt hw]
  · simpa using binarySearch_worstCase w n hw hn

end CorrectnessAndComplexity

end Algolean.Algorithms.WordRAM
