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

-- Each `Ordering` uses both comparisons, including when the first answer is false.
#guard (queryCmp 1 2).evalM (randomQuicksortModel (· ≤ ·) allPivots) == [.lt]
#guard (queryCmp 2 2).evalM (randomQuicksortModel (· ≤ ·) allPivots) == [.eq]
#guard (queryCmp 2 1).evalM (randomQuicksortModel (· ≤ ·) allPivots) == [.gt]
#guard (queryCmp 2 1).costM (randomQuicksortModel (· ≤ ·) allPivots) == [2]

/-- Inspect the three groups without their erased permutation proof. -/
def partitionOutcomes (pivot : α) (xs : List α) (le : α → α → Bool) :
    List (List α × List α × List α) :=
  (fun p => (p.lt, p.eq, p.gt)) <$>
    (partition3 pivot xs).evalM (randomQuicksortModel le allPivots)

#guard partitionOutcomes 2 [3, 1, 2, 3, 2, 4] (· ≤ ·) == [([1], [2, 2], [3, 3, 4])]
#guard partitionOutcomes 2 [3, 1, 2, 3, 2, 4] (· ≥ ·) == [([3, 3, 4], [2, 2], [1])]
#guard partitionOutcomes 2 [] (· ≤ ·) == [([], [], [])]
#guard (partition3 2 [3, 1, 2, 3, 2, 4]).costM
    (randomQuicksortModel (· ≤ ·) allPivots) == [12]

-- Equivalence depends on the comparison key, not on equality of the payload.
#guard partitionOutcomes (⟨2, "pivot"⟩ : Entry)
    [⟨2, "a"⟩, ⟨1, "low"⟩, ⟨2, "b"⟩, ⟨3, "high"⟩] (fun a b => a.key ≤ b.key) ==
  [([⟨1, "low"⟩], [⟨2, "a"⟩, ⟨2, "b"⟩], [⟨3, "high"⟩])]

-- The middle pivot takes four comparisons; either end pivot takes six. Finite draws are free.
#guard (randomQuicksort [1, 2, 3]).costM (randomQuicksortModel (· ≤ ·) allPivots) ==
  [6, 6, 4, 6, 6]
#guard (randomQuicksort [7]).costM (randomQuicksortModel (· ≤ ·) allPivots) == [0]

-- All equivalent elements are emitted together: every pivot costs just 2 * (n - 1).
#guard (randomQuicksort [4, 4, 4, 4]).costM (randomQuicksortModel (· ≤ ·) allPivots) ==
  [6, 6, 6, 6]

end AlgoleanTests.RandomQuicksortExamples
