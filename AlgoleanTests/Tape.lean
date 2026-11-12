/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Tape
public import Mathlib.Logic.Encodable.Basic

/-!
# Comparing complete tape contents in execution tests

`tapeView` records the current cell and both sides of a tape as lists of symbol numbers.
The execution tests use this representation to check all stored cells with decidable equality.
-/

@[expose] public section

namespace AlgoleanTests.Tape

open Cslib.Turing

/-- This records every stored tape cell using lists with decidable equality. -/
def tapeView {Symbol : Type} [Encodable Symbol] (contents : BiTape Symbol) :
    Option Nat × List (Option Nat) × List (Option Nat) :=
  (contents.head.map Encodable.encode, contents.left.toList.map (Option.map Encodable.encode),
    contents.right.toList.map (Option.map Encodable.encode))

end AlgoleanTests.Tape
