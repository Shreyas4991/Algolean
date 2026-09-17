/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Algolean.Models.WordRAMSyntax

/-!
# Binary search in the word-RAM model

The program searches a sorted array using six registers and no extra memory.
The initial state supplies the search key, the last array address, and a flag indicating
whether the array is nonempty. The same program handles every input size that fits in
memory at word width `w`, including arrays that use all `2 ^ w` cells.

The midpoint is `lo + (hi - lo) / 2`. Bounds checks prevent address arithmetic from wrapping.

Adapted from https://github.com/Shreyas4991/Algolean/pull/89.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

namespace BinarySearch

/-- Register holding the first address still to search. -/
abbrev lower : Register 6 := 0
/-- Register holding the last address still to search. -/
abbrev upper : Register 6 := 1
/-- Register holding the midpoint address, or a matching address when found. -/
abbrev middle : Register 6 := 2
/-- Register holding the word loaded from the midpoint address. -/
abbrev value : Register 6 := 3
/-- Register holding the search key. -/
abbrev key : Register 6 := 4
/-- Register holding the constant one. -/
abbrev one : Register 6 := 5

/-- One machine iteration, with its continuation indicated by the less-than flag. -/
def body (w : Nat) : Prog (WordRAM w 6) Unit := do [WordRAM w 6]
  middle ←ᵣ upper - lower
  middle ←ᵣ middle >>> one
  middle ←ᵣ lower + middle
  value ←ᵣ mem[middle]
  ifₚ value =ᵣ key then
    reset .ult
  else
    ifₚ value <ᵣ key then
      ifₚ middle <ᵣ upper then
        lower ←ᵣ middle + one
      else
        nop
    else
      ifₚ lower <ᵣ middle then
        upper ←ᵣ middle - one
      else
        nop

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
    nop

/-- Store the input array and search key, and initialize the bounds and flags for binary search. -/
def binarySearchState (input : Array (Word w)) (target : Word w) : RAMState w 6 :=
  ⟨arrayMemory input,
    fun r => if r = BinarySearch.key then target
      else if r = BinarySearch.upper then BitVec.ofNat w (input.size - 1) else 0,
    fun op => if op = .ult then decide (input.size ≠ 0) else false⟩

end Algolean.Algorithms.WordRAM
