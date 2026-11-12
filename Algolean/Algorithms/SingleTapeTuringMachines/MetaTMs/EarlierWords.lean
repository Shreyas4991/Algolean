/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CounterVisits

/-!
# Visiting an earlier word while preserving the intervening words

* `onEarlierWord_spec` describes the existing `onCounter` program when the visited word has
  other data farther left. The action may change that data and the tape beyond the current word.
* The visited word, intervening words, current word, and starting head position are preserved.

The containing machine fixes the action and number of intervening words once. Their lengths
and contents are read from the tape by the same finite program on every input.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the visited word and its left neighbor, followed by the reversed intervening words. -/
@[expose] def earlierLeft (left : StackTape Γ) (word : List Γ) : List (List Γ) → StackTape Γ
  | [] => StackTape.cons none (StackTape.prepend word.reverse (StackTape.cons none left))
  | next :: near =>
    StackTape.cons none (StackTape.prepend next.reverse (earlierLeft left word near))

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- A blank separates the current word from all earlier words. -/
@[simp, grind =] theorem earlierLeft_head (left : StackTape Γ) (word : List Γ)
    (near : List (List Γ)) : (earlierLeft left word near).head = none := by
  cases near <;> simp [earlierLeft]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- The visited word can itself follow a binary counter and further preserved words. -/
@[simp, grind =] theorem earlierLeft_counterLeft (counter word : List Γ)
    (before near : List (List Γ)) :
    earlierLeft (counterLeft counter before).tail word near =
      counterLeft counter (near ++ word :: before) := by
  induction near with
  | nil => simp [earlierLeft, counterLeft]
  | cons next near ih =>
    simpa [earlierLeft, counterLeft] using
      congrArg (fun left => StackTape.cons none (StackTape.prepend next.reverse left)) ih

/--
The action runs at the earlier word and may change the tape on either side of the preserved
words. The bound counts the action and both crossings of every intervening word.
-/
@[spec] theorem onEarlierWord_spec (action : Prog (TMQuery tm) Unit)
    (left resultLeft : StackTape Γ) (word : List Γ) (near : List (List Γ)) (current : List Γ)
    (tail resultTail : StackTape Γ) (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost machineState => machineState.config =
          ⟨label, BiTape.segment (StackTape.cons none left) word (counterRight near current tail)⟩ ∧
          machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config =
          ⟨result, BiTape.segment (StackTape.cons none resultLeft) word
            (counterRight near current resultTail)⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost machineState => machineState.config =
        ⟨label, BiTape.segment (earlierLeft left word near) current tail⟩ ∧
        machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onCounter tm action near.length
    ⦃ fun _ cost final => final.config =
        ⟨result, BiTape.segment (earlierLeft resultLeft word near) current resultTail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 * word.length +
          2 * (near.map List.length).sum + 4 * near.length + 4 ⦄ := by
  induction near generalizing current tail resultTail origin elapsed with
  | nil =>
    apply Std.WP.Triple.intro
    rintro initial machineState ⟨hcfg, hpos, hcost⟩
    simp only [List.length_nil, onCounter]
    vcgen [previousRegion_spec (tm := tm) left word current tail label origin initial.steps,
      haction (origin - (word.length + 1 : Nat)) (initial.steps + word.length + 3),
      nextRegion_le_spec (tm := tm) (StackTape.cons none resultLeft) word current resultTail result
        (origin - (word.length + 1 : Nat)) (initial.steps + word.length + 3 + bound)]
    all_goals
      simp_all [earlierLeft, counterRight]
      all_goals lia
  | cons next near ih =>
    apply Std.WP.Triple.intro
    rintro initial machineState ⟨hcfg, hpos, hcost⟩
    have ha (position : ℤ) (steps : Nat) := haction position steps
    have hr := ih next (StackTape.prepend current (StackTape.cons none tail))
      (StackTape.prepend current (StackTape.cons none resultTail))
      (by simpa [counterRight, List.reverse_cons, StackTape.separateWords_append] using ha)
      (origin - (next.length + 1 : Nat)) (initial.steps + next.length + 3)
    simp only [List.length_cons, onCounter]
    vcgen [previousRegion_spec (tm := tm) ((earlierLeft left word near).tail) next current tail
        label origin initial.steps,
      hr,
      nextRegion_le_spec (tm := tm) (earlierLeft resultLeft word near)
        next current resultTail result
        (origin - (next.length + 1 : Nat))
        (initial.steps + next.length + 3 + bound + 2 * word.length +
          2 * (near.map List.length).sum + 4 * near.length + 4)]
    all_goals
      simp_all [counterRight, earlierLeft]
      all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
