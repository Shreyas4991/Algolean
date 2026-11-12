/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Decrement

/-!
# Testing whether a binary counter equals one

* `testOne` reads a binary counter whose most significant digit comes first. It records whether
  the value is one in the finite control, preserves the tape, and restores the head.
* Leading zeros are allowed, so the test also works after subtraction.

This is a machine template. Its digit meaning one and its three distinct control states are
fixed once when the containing machine is constructed.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private noncomputable def oneTable (one : Γ) (zeroFlag oneFlag manyFlag : tm.State) :
    ScanTable tm where
  states := Fintype.elems.toList
  symbols := Fintype.elems.toList
  next label symbol :=
    if label = zeroFlag then (if symbol = one then oneFlag else zeroFlag) else manyFlag
  mem_states label := Finset.mem_toList.mpr (Fintype.complete label)
  mem_symbols symbol := Finset.mem_toList.mpr (Fintype.complete symbol)

private theorem oneTable_result (zero one : Γ) (hne : zero ≠ one)
    (zeroFlag oneFlag manyFlag : tm.State) (hfirst : zeroFlag ≠ oneFlag)
    (hlast : zeroFlag ≠ manyFlag) (bits : List Bool) :
    (bits.map (fun bit => if bit then one else zero)).foldl
      (oneTable one zeroFlag oneFlag manyFlag).next zeroFlag =
        if binaryValue bits.reverse = 0 then zeroFlag
        else if binaryValue bits.reverse = 1 then oneFlag else manyFlag := by
  induction bits using List.reverseRecOn with
  | nil => simp
  | append_singleton bits bit ih =>
    simp only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih, List.reverse_append, List.reverse_singleton, List.singleton_append]
    cases bit <;> simp only [binaryValue, Bool.false_eq_true, ↓reduceIte, oneTable]
    all_goals
      split_ifs <;> simp_all

/--
This machine template tests whether the counter equals one, allowing leading zeros. It leaves
all tape cells unchanged and returns to the first counter cell. The three control states are
fixed independently of the counter value and input length.
-/
noncomputable def testOne (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (one : Γ) (zeroFlag oneFlag manyFlag : tm.State) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ zeroFlag
  scan (oneTable one zeroFlag oneFlag manyFlag)
  seekLeftEnd tm

/-- The test distinguishes zero, one, and larger values in two moves per digit plus two moves. -/
@[spec] theorem testOne_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroFlag oneFlag manyFlag : tm.State) (hfirst : zeroFlag ≠ oneFlag)
    (hlast : zeroFlag ≠ manyFlag) (bits : List Bool) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      testOne tm one zeroFlag oneFlag manyFlag
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroFlag
          else if binaryValue bits.reverse = 1 then oneFlag else manyFlag),
          BiTape.segment StackTape.nil (bits.map (fun bit => if bit then one else zero)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 2 * bits.length + 2 ⦄ := by
  vcgen [testOne,
    scan_spec (oneTable one zeroFlag oneFlag manyFlag) StackTape.nil tail
      (bits.map (fun bit => if bit then one else zero)) zeroFlag origin elapsed,
    seekLeftEnd_segment_spec StackTape.nil tail
      (bits.map (fun bit => if bit then one else zero)).reverse []
      (some ((bits.map (fun bit => if bit then one else zero)).foldl
        (oneTable one zeroFlag oneFlag manyFlag).next zeroFlag))
      (origin + bits.length) (elapsed + bits.length)]
  all_goals
    simp_all [oneTable_result zero one hne zeroFlag oneFlag manyFlag hfirst hlast]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
