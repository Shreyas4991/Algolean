/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Algorithms.RandomQuicksort

/-!
# Executable randomized quicksort examples

The list interpreter explores every possible sequence of pivot choices. These checks also
exercise compiled execution: no `noncomputable` definitions are used in the executable models.
-/

@[expose] public section

namespace AlgoleanTests.RandomQuicksortExamples

open Algolean.Algorithms Algolean.Algorithms.Models

/-- Explore every legal pivot, charging only for comparisons. -/
def allPivots : ModelM UniformSample List Nat :=
  UniformSample.model (fun n => List.finRange (n + 1)) 0

/-- Collect the results from every possible pivot sequence. -/
def outcomes (xs : List α) (le : α → α → Bool) : List (List α) :=
  (randomQuicksort xs).evalM (randomQuicksortModel le allPivots)

/-- Every pivot sequence must succeed and return the expected list, with at least one outcome. -/
def checks [BEq α] (xs expected : List α) (le : α → α → Bool) : Bool :=
  let results := outcomes xs le
  !results.isEmpty && results.all (· == expected)

#guard checks ([] : List Nat) [] (· ≤ ·)
#guard checks [7] [7] (· ≤ ·)
#guard checks [3, 1, 2, 1, 3] [1, 1, 2, 3, 3] (· ≤ ·)
#guard checks [3, 1, 2, 1, 3] [3, 3, 2, 1, 1] (· ≥ ·)
#guard checks [4, 4, 4] [4, 4, 4] (· ≤ ·)

/-- A payload type deliberately lacking an `Ord` instance. -/
structure Entry where
  key : Nat
  payload : String
  deriving BEq, Repr

#guard checks ([⟨2, "b"⟩, ⟨1, "a"⟩, ⟨3, "c"⟩] : List Entry)
    [⟨3, "c"⟩, ⟨2, "b"⟩, ⟨1, "a"⟩] (fun a b => a.key ≥ b.key)

-- The middle pivot takes two comparisons; either end pivot takes three. Finite draws are free.
#guard (randomQuicksort [1, 2, 3]).costM (randomQuicksortModel (· ≤ ·) allPivots) ==
  [3, 3, 2, 3, 3]
#guard (randomQuicksort [7]).costM (randomQuicksortModel (· ≤ ·) allPivots) == [0]

end AlgoleanTests.RandomQuicksortExamples
