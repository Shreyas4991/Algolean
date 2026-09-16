/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Algolean.Models.WordRAMSyntax

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

end Algolean.Algorithms.WordRAM
