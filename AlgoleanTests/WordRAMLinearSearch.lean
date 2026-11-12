/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch.Complexity
public import Algolean.Models.WordRAM.Verification

/-!
# Strict WordRAM linear-search tests

Check empty and maximal inputs, duplicate keys, stale working state, exact costs, unread input
space, and interpreter fuel boundaries. Setup also composes through the shared VCGen handler.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMLinearSearch

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM
open LinearSearch Cslib Std.WP
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

set_option experimental.vcgen true

example (input : Search.Input (Word w)) (s : RAMState w 5)
    (h : RepresentsSizedSearchInput input key s) (initial : RAMCost w) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 6⟩ ⦄ (setup w)
      ⦃ fun _ cost final => cost = initial + ⟨6, {0}⟩ ∧
        final.machine.Registers last = BitVec.ofNat w input.data.size ∧
        final.machine.Registers index = 1 ∧ final.machine.Registers one = 1 ∧
        final.machine.Flags .eq = false ∧
        final.machine.Flags .ult = decide (0 < input.data.size) ∧ final.fuel = fuel;
        fun _ => False ⦄ := by
  have hh : s.Memory (BitVec.ofNat w 0) = BitVec.ofNat w input.data.size := h.header
  have hn : (BitVec.ofNat w input.data.size).toNat = input.data.size := Nat.mod_eq_of_lt h.fits
  vcgen [setup]
  all_goals simp_all [CmpOp.eval, add_assoc]

end AlgoleanTests.WordRAMLinearSearch
