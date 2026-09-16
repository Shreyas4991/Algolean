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

The program uses five registers and no extra memory. Memory cell `0` stores the array size
`n`, and cells `1` through `n` store its elements. The initial state supplies the search key
in its register. The program initializes the other registers and flags, starts searching
at address `1`, and converts a found address to a zero-based array index.
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
/-- Register holding the constant one. -/
abbrev one : Register 5 := 3
/-- Inclusive last input address, loaded from the size header. -/
abbrev last : Register 5 := 4

/-- Inspect one cell, stopping at the first match or the inclusive last address. -/
def body (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  value ←ᵣ mem[index]
  ifₚ value =ᵣ key then
    reset .ult
  else
    ifₚ index <ᵣ last then
      index ←ᵣ index + one
    else
      nop

/-- Read the size header and initialize the search at address one. -/
def setup (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  reset .eq
  index ←ᵣ imm[0]
  last ←ᵣ mem[index]
  cmp (w := w) .ult index last
  one ←ᵣ imm[1]
  index ←ᵣ imm[1]

/-- Convert a found memory address to a zero-based array index. -/
def finish (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  ifₚ flag .eq then
    index ←ᵣ index - one
  else
    nop

end LinearSearch

/-- One fixed program for all representable input lengths at word width `w`. -/
def linearSearch (w : Nat) : Prog (WordRAM w 5) Unit := do [WordRAM w 5]
  LinearSearch.setup w
  whileₚ .ult do
    LinearSearch.body w
  LinearSearch.finish w

/-- Store the size header, array, and search key. The program initializes its other registers. -/
def linearSearchState (input : Array (Word w)) (target : Word w) : RAMState w 5 :=
  ⟨sizedArrayMemory input, fun r => if r = LinearSearch.key then target else 0, fun _ => false⟩

end Algolean.Algorithms.WordRAM
