/-
Copyright (c) 2026 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
module

public import Algolean.Algorithms.RandomQuicksort
public meta import Algolean.Algorithms.RandomQuicksort
public meta import Algolean.ModelM

/-!
# Executable randomized quicksort examples

The list interpreter explores every possible sequence of pivot choices. These checks also
exercise compiled execution: no `noncomputable` definitions are used in the executable models.
-/

@[expose] public section

-- These tests intentionally run compiled checks.
set_option linter.hashCommand false

namespace AlgoleanTests.RandomQuicksortExamples

open Algolean.Algorithms Algolean.Algorithms.Models

/-- Explore every legal pivot, charging only for comparisons. -/
def allPivots : ModelM UniformSample List Nat :=
  UniformSample.model (fun n => List.finRange (n + 1)) 0

/-- Collect the results from every possible pivot sequence. -/
def outcomes (xs : Array α) (le : α → α → Bool) : List (Array α) :=
  (randomQuicksort xs).evalM (randomQuicksortModel le allPivots)

/-- Every pivot sequence must succeed and return the expected array, with at least one outcome. -/
def checks [BEq α] (xs expected : Array α) (le : α → α → Bool) : Bool :=
  let results := outcomes xs le
  !results.isEmpty && results.all (· == expected)

#guard checks (#[] : Array Nat) #[] (· ≤ ·)
#guard checks #[7] #[7] (· ≤ ·)
#guard checks #[3, 1, 2, 1, 3] #[1, 1, 2, 3, 3] (· ≤ ·)
#guard checks #[3, 1, 2, 1, 3] #[3, 3, 2, 1, 1] (· ≥ ·)
#guard checks #[4, 4, 4] #[4, 4, 4] (· ≤ ·)

/-- A payload type deliberately lacking an `Ord` instance. -/
structure Entry where
  key : Nat
  payload : String
  deriving BEq, Repr

#guard checks (#[⟨2, "b"⟩, ⟨1, "a"⟩, ⟨3, "c"⟩] : Array Entry)
    #[⟨3, "c"⟩, ⟨2, "b"⟩, ⟨1, "a"⟩] (fun a b => a.key ≥ b.key)

/-- Inspect the recursive views, which exclude the selected pivot. -/
def partitionOutcomes (xs : Array α) (pivotIndex : Fin xs.size) (le : α → α → Bool) :
    List (Array α × Array α) :=
  (fun p => (p.left.toArray, p.right.toArray)) <$>
    (hoarePartition xs pivotIndex).evalM (randomQuicksortModel le allPivots)

#guard partitionOutcomes #[2] 0 (· ≤ ·) == [(#[], #[])]
#guard partitionOutcomes #[2, 1] 0 (· ≤ ·) == [(#[1], #[])]
#guard partitionOutcomes #[2, 3] 0 (· ≤ ·) == [(#[], #[3])]
#guard partitionOutcomes #[2, 2] 0 (· ≤ ·) == [(#[], #[2])]
#guard partitionOutcomes #[3, 1, 2, 3, 2, 4, 2] 6 (· ≤ ·) == [(#[2, 1], #[2, 3, 3, 4])]
#guard partitionOutcomes #[3, 1, 2, 3, 2, 4, 2] 6 (· ≥ ·) == [(#[3, 4, 2, 3], #[2, 1])]
-- A middle pivot is reserved by swapping; every other input element is retained.
#guard partitionOutcomes #[3, 1, 2, 3, 2, 4] 2 (· ≤ ·) == [(#[2, 1], #[4, 3, 3])]
#guard (hoarePartition #[3, 1, 2, 3, 2, 4] 2).costM
    (randomQuicksortModel (· ≤ ·) allPivots) == [5]
#guard (hoarePartition #[7] 0).costM (randomQuicksortModel (· ≤ ·) allPivots) == [0]

-- Equal keys stop both scans; the selected payload is excluded from both views.
#guard partitionOutcomes (#[⟨2, "pivot"⟩, ⟨2, "a"⟩, ⟨2, "b"⟩] : Array Entry)
    0 (fun a b => a.key ≤ b.key) == [(#[⟨2, "a"⟩], #[⟨2, "b"⟩])]

-- Even and odd intervals split evenly for every choice of an equivalent pivot.
#guard (List.range 33).all fun n =>
  (List.finRange (n + 1)).all fun i =>
    partitionOutcomes (Array.replicate (n + 1) 4) ⟨i.val, by simpa using i.isLt⟩ (· ≤ ·) ==
      [(Array.replicate (n / 2) 4, Array.replicate ((n + 1) / 2) 4)]

-- The middle pivot takes two comparisons; either end pivot takes three.
#guard (randomQuicksort #[1, 2, 3]).costM (randomQuicksortModel (· ≤ ·) allPivots) ==
  [3, 3, 2, 3, 3]
#guard (randomQuicksort #[7]).costM (randomQuicksortModel (· ≤ ·) allPivots) == [0]

-- Every pivot gives a balanced split for all-equal inputs: 3 + 0 + 1 comparisons.
#guard (randomQuicksort #[4, 4, 4, 4]).costM (randomQuicksortModel (· ≤ ·) allPivots) ==
  List.replicate 8 4

end AlgoleanTests.RandomQuicksortExamples
