/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.WordRAM.Search
public import Algolean.Models.WordRAMSyntax

/-!
# Linear search on the strict WordRAM

The fixed five-register program reads a size-prefixed array and stops at the first match.
It uses an inclusive last address so that even the largest fitting input cannot wrap its cursor.
The equality flag reports success; the index register then holds the zero-based matching index.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

open scoped WordRAM Prog

namespace LinearSearch

/-- Current address, converted to a zero-based index on success. -/
abbrev index : Register 4 := 0
/-- Search key, supplied by the input state. -/
abbrev key : Register 4 := 1
/-- Scratch register for the current array element. -/
abbrev value : Register 4 := 2
/-- Inclusive last array address. -/
abbrev last : Register 4 := 3

/-- Inspect a cell, stop on a match, and advance only before the last address. -/
def body (w : Nat) : Prog (WordRAM w 4) Unit := do [WordRAM w 4]
  value ←ᵣ mem[index]
  ifₚ value =ᵣ key then
    reset .ult
  else
    ifₚ index <ᵣ last then
      inc index
    else
      nop

/-- Read the runtime length and initialize the cursor, constant, and flags. -/
def setup (w : Nat) : Prog (WordRAM w 4) Unit := do [WordRAM w 4]
  reset .eq
  index ←ᵣ imm[0]
  last ←ᵣ mem[index]
  cmp (w := w) .ult index last
  index ←ᵣ imm[1]

/-- Convert a successful address into a zero-based index. -/
def finish (w : Nat) : Prog (WordRAM w 4) Unit := do [WordRAM w 4]
  ifₚ flag .eq then
    dec index
  else
    nop

end LinearSearch

/-- One program for every input length representable at this word width. -/
def linearSearch (w : Nat) : Prog (WordRAM w 4) Unit := do [WordRAM w 4]
  LinearSearch.setup w
  whileₚ .ult do
    LinearSearch.body w
  LinearSearch.finish w

end Algolean.Algorithms.WordRAM
