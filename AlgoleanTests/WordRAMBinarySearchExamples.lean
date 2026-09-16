/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.BinarySearch.Correctness
public import Algolean.Algorithms.WordRAM.BinarySearch.Complexity

/-! # Uniform binary search on runtime-represented arrays -/

@[expose] public section

namespace AlgoleanTests.WordRAMBinarySearchExamples

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM

def input : Array (Word 8) := #[1, 3, 5, 7, 9, 11, 13]

private theorem input_sorted : SortedWords input := by
  intro i j hi hj hij
  have hi' : i < 7 := hi
  have hj' : j < 7 := hj
  interval_cases i <;> interval_cases j <;> simp_all [input]

def searchExample : Prog (WordRAM 8 6) Unit := binarySearch 8

example : (execute 50 searchExample (binarySearchState input 7)).map (fun r =>
    (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time, r.fst.tell.addresses)) =
      some (some 3, 9, {3}) := by decide

example : (execute 50 searchExample (binarySearchState input 13)).map (fun r =>
    (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time, r.fst.tell.addresses)) =
      some (some 6, 25, {3, 5, 6}) := by decide

example : (execute 50 searchExample (binarySearchState input 0)).map (fun r =>
    (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time, r.fst.tell.addresses)) =
      some (none, 26, {0, 1, 3}) := by decide

example : (execute 50 searchExample (binarySearchState input 20)).map (fun r =>
    (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time,
      r.fst.tell.auxiliarySpace (inputRegion input), r.fst.tell.totalSpace (inputRegion input))) =
      some (none, 26, 0, 7) := by decide

-- Every address is available: no sentinel cell is reserved.
example : (execute 50 (binarySearch 2) (binarySearchState #[0, 1, 2, 3] 3)).map
    (fun r => searchOutput BinarySearch.middle r.snd.ram) = some (some 3) := by decide

example : (execute 50 (binarySearch 2) (binarySearchState (Array.replicate 4 0) 1)).map
    (fun r => (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time)) =
      some (none, binarySearchTime 4) := by decide

-- The nonempty flag distinguishes the two possible input lengths at word width zero.
example : (execute 13 (binarySearch 0) (binarySearchState #[0] 0)).map
    (fun r => (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time)) =
      some (some 0, 9) := by decide

example : (execute 2 (binarySearch 0) ((binarySearchState #[] 0).writeFlag .eq true)).map
    (fun r => (searchOutput BinarySearch.middle r.snd.ram, r.fst.tell.time)) =
      some (none, 1) := by decide

example : execute 12 (binarySearch 0) (binarySearchState #[0] 0) = none := rfl

def representingState (target junk : Word 8) : RAMState 8 6 :=
  ⟨fun addr => if addr.toNat < input.size then arrayMemory input addr else junk,
    fun r => if r = BinarySearch.key then target
      else if r = BinarySearch.upper then 6 else 255, fun _ => true⟩

private theorem representingState_input (target junk : Word 8) :
    RepresentsBoundedSearchInput ⟨input, target⟩ BinarySearch.key BinarySearch.upper
      (representingState target junk) := by
  have hfits : input.size ≤ 2 ^ 8 := by decide
  refine ⟨⟨⟨hfits, ?_⟩, by simp [representingState]⟩,
    by simp [representingState, BinarySearch.upper, BinarySearch.key, input],
    by simp [representingState, input]⟩
  intro i hi
  have hiw : i < 2 ^ 8 := by have : input.size = 7 := rfl; lia
  simpa only [representingState, wordAddress_toNat i hiw, if_pos hi] using
    arrayMemory_ofNat input (by decide) i hi

example (target junk : Word 8) :
    ∃ fuel cost t, execute fuel searchExample (representingState target junk) =
      some (⟨(), cost⟩, ⟨t, 0⟩) :=
  binarySearch_terminates ⟨input, target⟩ _ (representingState_input target junk)

example (target junk : Word 8) (fuel : Nat) (result : AddWriter (RAMCost 8 6) Unit)
    (final : ExecutionState 8 6)
    (hr : execute fuel searchExample (representingState target junk) = some (result, final)) :
    Search.search.spec ⟨input, target⟩ (searchOutput BinarySearch.middle final.ram) ∧
      result.tell.time ≤ binarySearchTime input.size ∧
      result.tell.auxiliarySpace (inputRegion input) = 0 :=
  ⟨binarySearch_correct_of_execute _ _ (representingState_input target junk) hr
      (by simpa using input_sorted),
    binarySearch_time_le _ _ (representingState_input target junk) hr,
    binarySearch_auxiliarySpace _ _ (representingState_input target junk) hr⟩

example : (execute 50 searchExample (representingState 7 173)).map
    (fun r => (searchOutput BinarySearch.middle r.snd.ram, r.snd.ram.Memory 200)) =
      some (some 3, 173) := by decide

example (n : Nat) (hn : n ≤ 2 ^ 8) :
    ∃ (data : Array (Word 8)) (target : Word 8),
      data.size = n ∧ data.size ≤ 2 ^ 8 ∧ SortedWords data ∧ target ∉ data ∧
      ∃ fuel cost t, execute fuel searchExample (binarySearchState data target) =
        some (⟨(), cost⟩, ⟨t, 0⟩) ∧ cost.time = binarySearchTime n :=
  binarySearch_exists_worstCase 8 n (by decide) hn

-- The contracts provide termination, correctness and both resource guarantees together.
example (target junk : Word 8) :
    ∃ cost t output, Executes searchExample (representingState target junk) cost t ∧
      RepresentsSearchOutput BinarySearch.middle output t ∧
      (Search.binarySearch (fun a b : Word 8 => a.toNat ≤ b.toNat)).spec
        ⟨input, target⟩ output ∧
      cost.time ≤ binarySearchTime input.size ∧ cost.auxiliarySpace (inputRegion input) = 0 := by
  have hi := representingState_input target junk
  have ha : (Search.binarySearch (fun a b : Word 8 => a.toNat ≤ b.toNat)).admissible
      ⟨input, target⟩ := by
    simpa using input_sorted
  obtain ⟨cost, t, hr⟩ := (binarySearch_correct 8).terminates _ _ ha hi
  obtain ⟨output, ho, hs⟩ := (binarySearch_correct 8).correct _ _ ha hi cost t hr
  exact ⟨cost, t, output, hr, ho, hs,
    (binarySearch_runsWithin 8).bounded _ _ trivial hi cost t hr⟩

end AlgoleanTests.WordRAMBinarySearchExamples
