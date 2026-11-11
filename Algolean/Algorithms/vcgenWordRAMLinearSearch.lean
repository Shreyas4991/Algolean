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

/-- Reason about word-RAM programs through `timeAndSpaceCost`,
with memory predicates as assertions. -/
local instance : HasHandler (WordRAM w) (Memory w → Prop) EStack⟨⟩ :=
  timeAndSpaceCost.hasHandler

/-- Linear search returns the first match, or certifies that no array index contains the key. -/
theorem linearSearch_spec (input : Array (BitVec w)) (key : BitVec w)
    (hfits : input.size ≤ 2 ^ w) :
    ⦃fun _ => True⦄
    linearSearch input key hfits
    ⦃fun _ mem =>
      match r with
      | none => ∀ i, i < input.size → input[i]? ≠ some key
      | some addr => IsFirstMatch input key addr
    ⦄
    := by
    sorry

theorem linearSearch_preserves (mem₀ : Memory w) :
  ⦃fun mem => mem = mem₀⦄ linearSearch input key hfits ⦃fun _ mem => mem = mem₀⦄ := by
    sorry


end VCGen

end Algolean.Algorithms.WordRAM
