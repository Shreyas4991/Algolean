/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.Basic
public import Algolean.Models.WordRAMSyntax

/-!
# Linear search in the word-RAM model

The program uses five registers and no extra memory. The initial state supplies the search
key, the last array address, and a flag indicating whether the array is nonempty.
The same program handles every input size that fits in memory at word width `w`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

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
def body (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  value ←ᵣ mem[index]
  ifₚ test .eq value key then
    reset .ult
  else
    ifₚ test .ult index last then
      index ←ᵣ index + one
    else
      pure ()

/-- Initialize scratch registers without inspecting runtime input. -/
def setup (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  reset .eq
  index ←ᵣ imm[0]
  one ←ᵣ imm[1]

end LinearSearch

/-- One fixed program for all representable input lengths at word width `w`. -/
def linearSearch (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  LinearSearch.setup w
  whileₚ .ult do
    LinearSearch.body w

/-- A canonical witness of the runtime input representation, used in examples. -/
def linearSearchState (input : Array (Word w)) (target : Word w) : RAMState w 5 :=
  ⟨arrayMemory input,
    fun r => if r = LinearSearch.key then target
      else if r = LinearSearch.last then BitVec.ofNat w (input.size - 1) else 0,
    fun op => if op = .ult then decide (input.size ≠ 0) else false⟩

end Algolean.Algorithms.WordRAM
