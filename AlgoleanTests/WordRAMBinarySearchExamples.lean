/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.BinarySearch

/-! # Executable word-RAM binary search examples -/

@[expose] public section

namespace AlgoleanTests.WordRAMBinarySearchExamples

open Algolean.Algorithms Algolean.Algorithms.WordRAM

/-- A sorted input with a duplicate key. -/
def input : Array (BitVec 8) := #[3, 7, 7, 12, 42, 99]

def search (key : BitVec 8) : Prog (WordRAM 8) (Option (Word 8)) :=
  binarySearch input key (by decide)

-- Immediate match, left branch, and repeated right branches.
example : ((search 7).evalM timeAndSpaceCost (arrayMemory input)).1 = some 2 := by decide
example : ((search 3).evalM timeAndSpaceCost (arrayMemory input)).1 = some 0 := by decide
example : ((search 99).evalM timeAndSpaceCost (arrayMemory input)).1 = some 5 := by decide
example : ((search 7).costM timeAndSpaceCost (arrayMemory input)).1.time = 5 := by decide
example : ((search 3).costM timeAndSpaceCost (arrayMemory input)).1.time = 13 := by decide
example : ((search 99).costM timeAndSpaceCost (arrayMemory input)).1.time = 21 := by decide

-- Misses below, between, and above the stored values.
example : ((search 0).evalM timeAndSpaceCost (arrayMemory input)).1 = none := by decide
example : ((search 8).evalM timeAndSpaceCost (arrayMemory input)).1 = none := by decide
example : ((search 100).evalM timeAndSpaceCost (arrayMemory input)).1 = none := by decide
example : ((search 100).costM timeAndSpaceCost (arrayMemory input)).1.time = 23 := by decide

-- Empty inputs execute no queries.
example : ((binarySearch (#[] : Array (BitVec 8)) 42 (by decide)).evalM
    timeAndSpaceCost Memory.zero).1 = none := by decide
example : ((binarySearch (#[] : Array (BitVec 8)) 42 (by decide)).costM
    timeAndSpaceCost Memory.zero).1.time = 0 := by decide

-- A two-bit RAM can search all four of its cells without wrapping an endpoint.
example : ((binarySearch (#[0, 1, 2, 3] : Array (BitVec 2)) 3 (by decide)).evalM
    timeAndSpaceCost (arrayMemory #[0, 1, 2, 3])).1 = some 3 := by decide
example : ((binarySearch (Array.replicate 4 (0 : BitVec 2)) 1 (by decide)).costM
    timeAndSpaceCost (arrayMemory (Array.replicate 4 0))).1.time = 23 := by decide

-- The degenerate zero-bit RAM still supports its single cell.
example : ((binarySearch (#[0] : Array (BitVec 0)) 0 (by decide)).evalM
    timeAndSpaceCost (arrayMemory #[0])).1 = some 0 := by decide

-- The general space theorems apply for every choice of key.
example (key : BitVec 8) : ((search key).costM timeAndSpaceCost
    (arrayMemory input)).1.auxiliarySpace (inputRegion input) = 0 :=
  binarySearch_auxiliarySpace input key (by decide)

example (key : BitVec 8) : ((search key).costM timeAndSpaceCost
    (arrayMemory input)).1.totalSpace (inputRegion input) = 6 :=
  binarySearch_totalSpace input key (by decide)

-- Worst-case witnesses exist for every length, including a completely full byte-addressed RAM.
example (n : Nat) (hn : n ≤ 256) :
    ((binarySearch (Array.replicate n (0 : BitVec 8)) 1 (by simpa using hn)).costM
      timeAndSpaceCost (arrayMemory (Array.replicate n 0))).1.time = binarySearchTime n :=
  binarySearch_worstCase 8 n (by decide) hn

end AlgoleanTests.WordRAMBinarySearchExamples
