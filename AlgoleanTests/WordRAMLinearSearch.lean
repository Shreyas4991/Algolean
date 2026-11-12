/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Complexity

/-!
# Strict WordRAM linear-search tests

Check empty and maximal inputs, duplicate keys, stale working state, exact costs, unread input
space, and interpreter fuel boundaries. Setup also composes through the shared VCGen handler.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMLinearSearch

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM
open LinearSearch Cslib
open scoped WordRAM.Spec

def observe (fuel : Nat) (s : RAMState w 5) :
    Option (Option Nat × Nat × Finset (Word w) × Nat) :=
  (execute fuel (linearSearch w) s).map fun r =>
    (searchOutput index r.2.machine, r.1.tell.time, r.1.tell.addresses, r.2.fuel)

example : observe (w := 8) 9 (linearSearchState #[] 42 key) =
    some (none, 7, {0}, 0) := by decide

example : observe (w := 0) 9 (linearSearchState #[] 0 key) =
    some (none, 7, {0}, 0) := by decide

example : observe (w := 8) 14 (linearSearchState #[42] 42 key) =
    some (some 0, 10, {0, 1}, 0) := by decide

example : execute 13 (linearSearch 8) (linearSearchState #[42] 42 key) = none := by decide

example : observe (w := 8) 16 (linearSearchState #[42] 7 key) =
    some (none, 11, {0, 1}, 0) := by decide

-- Stop at the first duplicate and retain spare interpreter fuel.
example : observe (w := 8) 40 (linearSearchState #[7, 5, 5] 5 key) =
    some (some 1, 14, {0, 1, 2}, 19) := by decide

-- The size header can equal the key without being mistaken for an array element.
example : observe (w := 2) 30 (linearSearchState #[0, 0, 0] 3 key) =
    some (none, 19, {0, 1, 2, 3}, 0) := by decide

-- A match at the last representable address is converted back to index two.
example : observe (w := 2) 28 (linearSearchState #[0, 0, 3] 3 key) =
    some (some 2, 18, {0, 1, 2, 3}, 0) := by decide

def dirtyEmpty : RAMState 8 5 :=
  ⟨fun addr => if addr = 0 then 0 else 77, fun _ => 255, fun _ => true⟩

example : observe 9 dirtyEmpty = some (none, 7, {0}, 0) := by decide

-- Total space includes the header and unread final element after an early match.
example : (execute 21 (linearSearch 8) (linearSearchState #[7, 5, 5] 5 key)).map
    (fun r => (r.1.tell.auxiliarySpace (sizedInputRegion #[7, 5, 5]),
      r.1.tell.totalSpace (sizedInputRegion #[7, 5, 5]))) = some (0, 4) := by decide

-- The verified fuel budget guarantees a successful run for every representing initial state.
example (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) :
    ∃ result final, execute (7 * input.data.size + 9) (linearSearch w) s = some (result, final) ∧
      SolvesInput input s.Memory final.machine := by
  simpa only [Nat.add_zero] using
    WordRAM.Spec.execute (linearSearch_correct input s h 0) ⟨rfl, rfl⟩

end AlgoleanTests.WordRAMLinearSearch
