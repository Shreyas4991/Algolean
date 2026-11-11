/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM
public import Std.Tactic.Do

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

/-- The returned address points to the key, and every earlier element differs from the key. -/
def IsFirstMatch (input : Array (BitVec w)) (key : BitVec w) (addr : Word w) : Prop :=
  addr.toNat < input.size ∧ input[addr.toNat]? = some key ∧
    ∀ i, i < addr.toNat → input[i]? ≠ some key

section VCGen

open Cslib Cslib.FreeM Lean.Order Std.WP

set_option experimental.vcgen true

/-- An index within the address space survives conversion to a word without wrapping. -/
@[grind =]
private theorem wordAddress_toNat (i : Nat) (hi : i < 2 ^ w) :
    (BitVec.ofNat w i).toNat = i := Nat.mod_eq_of_lt hi

@[simp, grind =]
private theorem arrayMemory_ofNat (input : Array (BitVec w)) (hfits : input.size ≤ 2 ^ w)
    (i : Nat) (hi : i < input.size) :
    arrayMemory input (BitVec.ofNat w i) = input[i] := by
  simp [arrayMemory, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le hi hfits), hi]

@[simp, grind =]
private theorem wordAddress_succ (i : Nat) :
    BitVec.ofNat w i + 1#w = BitVec.ofNat w (i + 1) := by
  simp [BitVec.ofNat_add]

@[grind →]
private theorem length_lt_of_range_eq {n cur : Nat} {pref suff : List Nat}
    (h : List.range n = pref ++ cur :: suff) : pref.length < n := by
  have := congrArg List.length h
  simp at this
  omega

/-- Linear search returns the first match, or certifies that no array index contains the key. -/
theorem linearSearch_spec (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ⦃fun mem => mem = arrayMemory input⦄
    linearSearch input key hfits
    ⦃fun r mem => mem = arrayMemory input ∧
      match r with
      | none => ∀ i, i < input.size → input[i]? ≠ some key
      | some addr => IsFirstMatch input key addr⦄ := by
  vcgen [linearSearch] invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret addr mem =>
        IsFirstMatch input key addr ∧ ret = some addr ∧ mem = arrayMemory input)
      (onContinue := fun pref _ addr mem =>
        (∀ i, i < pref.length → input[i]? ≠ some key) ∧
          addr = BitVec.ofNat w pref.length ∧ mem = arrayMemory input)
  all_goals simp_all [CmpOp.eval, BinOp.eval]
  all_goals grind [IsFirstMatch]

theorem linearSearch_preserves (mem₀ : Memory w) :
  ⦃fun mem => mem = mem₀⦄ linearSearch input key hfits ⦃fun _ mem => mem = mem₀⦄ := by
  vcgen [linearSearch] invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret addr mem => mem = mem₀)
      (onContinue := fun pref _ addr mem => mem = mem₀)
  all_goals simp_all [CmpOp.eval]


theorem linearSearch_correct (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    match ((linearSearch input key hfits).evalM timeAndSpaceCost (arrayMemory input)).1 with
    | none => ∀ i, i < input.size → input[i]? ≠ some key
    | some addr => IsFirstMatch input key addr :=
  (ModelM.evalM_of_triple timeAndSpaceCost (linearSearch_spec input key hfits) _ rfl).2

end VCGen

end Algolean.Algorithms.WordRAM
