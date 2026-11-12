/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.EarlierWords

/-!
# Crossing several words on one tape

* `leftRegions` moves to the beginning of an earlier word.
* `rightRegions` moves to the beginning of a later word.
* The programs preserve every cell and control state. Their bounds count the crossed words
  and their separating blanks, including empty words.

These are machine templates. The number of words to cross is fixed before execution. Their
contents and lengths are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This machine template crosses a fixed number of preceding words and preserves the tape. -/
def leftRegions (tm : SingleTapeTM Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    previousRegion tm
    leftRegions tm count

/-- This machine template crosses a fixed number of following words and preserves the tape. -/
def rightRegions (tm : SingleTapeTM Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    rightRegions tm count
    nextRegion tm

/-- Moving left reaches an earlier word while preserving arbitrary data farther left. -/
@[spec] theorem leftRegions_from_spec (left : StackTape Γ) (first : List Γ)
    (near : List (List Γ)) (current : List Γ) (tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label,
        BiTape.segment (earlierLeft left first near) current tail⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      leftRegions tm (near.length + 1)
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.cons none left) first (counterRight near current tail)⟩ ∧
        final.headPos = origin -
          (first.length + (near.map List.length).sum + near.length + 1 : Nat) ∧
        cost.steps ≤ elapsed + first.length +
          (near.map List.length).sum + 3 * near.length + 3 ⦄ := by
  induction near generalizing current tail origin elapsed with
  | nil =>
    simp only [List.length_nil, leftRegions]
    vcgen [previousRegion_le_spec (tm := tm) left
      first current tail label origin elapsed]
    all_goals simp_all [earlierLeft, counterRight]
  | cons word near ih =>
    have hr := ih word (StackTape.prepend current (StackTape.cons none tail))
      (origin - (word.length + 1 : Nat)) (elapsed + word.length + 3)
    simp only [List.length_cons]
    rw [leftRegions]
    vcgen [previousRegion_le_spec (tm := tm) ((earlierLeft left first near).tail)
      word current tail label origin elapsed, hr]
    all_goals
      simp_all [earlierLeft, counterRight, List.reverse_cons]
      all_goals lia

/-- Moving left reaches the first word and preserves all neighboring words. -/
@[spec] theorem leftRegions_spec (first : List Γ) (near : List (List Γ)) (current : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label,
        BiTape.segment (counterLeft first near) current tail⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      leftRegions tm (near.length + 1)
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil first (counterRight near current tail)⟩ ∧
        final.headPos = origin -
          (first.length + (near.map List.length).sum + near.length + 1 : Nat) ∧
        cost.steps ≤ elapsed + first.length +
          (near.map List.length).sum + 3 * near.length + 3 ⦄ := by
  have hleft : earlierLeft StackTape.nil first near = counterLeft first near := by
    simpa [counterLeft] using earlierLeft_counterLeft ([] : List Γ) first [] near
  simpa [hleft] using leftRegions_from_spec (tm := tm) StackTape.nil first near current tail
    label origin elapsed

/-- Moving right reaches the later word and preserves all neighboring words. -/
@[spec] theorem rightRegions_spec (first : List Γ) (near : List (List Γ)) (current : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config =
        ⟨label, BiTape.segment StackTape.nil first (counterRight near current tail)⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      rightRegions tm (near.length + 1)
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (counterLeft first near) current tail⟩ ∧
        final.headPos = origin +
          (first.length + (near.map List.length).sum + near.length + 1 : Nat) ∧
        cost.steps ≤ elapsed + first.length + (near.map List.length).sum + near.length + 1 ⦄ := by
  induction near generalizing current tail origin elapsed with
  | nil =>
    simp only [List.length_nil, rightRegions]
    vcgen [nextRegion_le_spec (tm := tm) StackTape.nil first current tail label origin elapsed]
    all_goals simp_all [counterLeft, counterRight]
  | cons word near ih =>
    have hr := ih word (StackTape.prepend current (StackTape.cons none tail)) origin elapsed
    simp only [List.length_cons]
    rw [rightRegions]
    vcgen [hr, nextRegion_le_spec (tm := tm) (counterLeft first near) word current tail label
      (origin + (first.length + (near.map List.length).sum + near.length + 1 : Nat))
      (elapsed + first.length + (near.map List.length).sum + near.length + 1)]
    all_goals
      simp_all [counterLeft, counterRight, List.reverse_cons]
      all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
