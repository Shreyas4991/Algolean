/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.BinarySearch

/-!
# Register-based binary search examples

The key starts in its designated register. Only the test harness reads the resulting address.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMBinarySearchExamples

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM

/-- Execute a search and expose the joint result to the test harness. -/
def search (input : Array (BitVec w)) (target : Word w) :=
  ((binarySearch w input.size).runM timeAndSpaceCost).run (binarySearchState input target)

def input : Array (BitVec 8) := #[1, 3, 5, 7, 9, 11, 13]

-- A midpoint hit takes the three setup instructions and five loop instructions.
example : (search input 7).fst.ret = some BinarySearch.middle := by decide

example : (search input 7).snd.Registers BinarySearch.middle = 3 := by decide

example : (search input 7).fst.tell.time = 8 := by decide

example : (search input 7).fst.tell.addresses = {3} := by decide

example : (search input 7).fst.tell.space = 7 := by decide

-- Both directions recurse; searches can reach either endpoint or miss beyond it.
example : (search input 1).snd.Registers BinarySearch.middle = 0 := by decide

example : (search input 13).snd.Registers BinarySearch.middle = 6 := by decide

example : (search input 0).fst.ret = none := by decide

example : (search input 14).fst.ret = none := by decide

example : (search input 6).fst.ret = none := by decide

-- Duplicates are allowed: correctness does not require the first matching position.
example : (search (#[2, 2, 2, 4] : Array (BitVec 3)) 2).fst.ret =
    some BinarySearch.middle := by decide

example : (search (#[2, 2, 2, 4] : Array (BitVec 3)) 2).snd.Registers
    BinarySearch.middle = 1 := by decide

-- An empty input performs no queries or memory probes.
example : (search (#[] : Array (BitVec 8)) 42).fst.ret = none := by decide

example : (search (#[] : Array (BitVec 8)) 42).fst.tell.time = 0 := by decide

example : (search (#[] : Array (BitVec 8)) 42).fst.tell.addresses = ∅ := by decide

-- Inclusive bounds allow an input occupying every addressable cell.
example : (search (#[0, 1, 2, 3] : Array (BitVec 2)) 3).fst.ret =
    some BinarySearch.middle := by decide

example : (search (#[0, 1, 2, 3] : Array (BitVec 2)) 3).snd.Registers
    BinarySearch.middle = 3 := by decide

example : (search (#[0, 1, 2, 3] : Array (BitVec 2)) 0).snd.Registers
    BinarySearch.middle = 0 := by decide

example : (search (#[0] : Array (BitVec 0)) 0).fst.ret =
    some BinarySearch.middle := by decide

example : (search (#[0] : Array (BitVec 0)) 0).fst.tell.time = 8 := by decide

-- Worst-case execution follows the right half, including the final singleton.
example : (search (Array.replicate 8 (0 : BitVec 4)) 1).fst.tell.time = 34 := by decide +kernel

example : (search (Array.replicate 8 (0 : BitVec 4)) 1).fst.tell.addresses =
    {3, 5, 6, 7} := by decide +kernel

-- The general theorems apply to arbitrary keys and account for all six registers.
example (target : Word 8) : (search input target).fst.tell.time ≤ 26 :=
  binarySearch_time_le input.size (by decide) (binarySearchState input target)

example (target : Word 8) : (search input target).fst.tell.auxiliarySpace
    (inputRegion input) = 6 :=
  binarySearch_auxiliarySpace input (by decide) (binarySearchState input target)

example (target : Word 8) : (search input target).fst.tell.totalSpace
    (inputRegion input) = 13 :=
  binarySearch_totalSpace input (by decide) (binarySearchState input target)

example (target : Word 8) : (search input target).fst.ret = none ↔ target ∉ input :=
  binarySearch_none_iff input target (by decide) (by
    intro i j hi hj hij
    have hi' : i < 7 := hi
    have hj' : j < 7 := hj
    interval_cases i <;> interval_cases j <;> simp_all [input])

end AlgoleanTests.WordRAMBinarySearchExamples
