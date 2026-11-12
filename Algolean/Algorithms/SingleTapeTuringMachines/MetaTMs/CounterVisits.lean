/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions

/-!
# Visiting a counter before several other words

* `onCounter` runs a fixed program on the leftmost word and then returns to the current word.
  A fixed number of other words may separate the two.
* The counter may grow to the left. The intervening words and the current word stay at the
  same tape positions, and the head returns to its starting cell.
* The program run on the counter may also change the tape beyond the current word.

This is a machine template. The number of intervening words and the counter program are
fixed before execution. Their contents and lengths are read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This is the tape to the left of the current word. `near` lists intervening words from nearest
to farthest. The counter comes before all of them, with blank cells farther left.
-/
@[expose] def counterLeft (counter : List Γ) : List (List Γ) → StackTape Γ
  | [] => StackTape.cons none (StackTape.mapSome counter.reverse)
  | word :: near => StackTape.cons none (StackTape.prepend word.reverse (counterLeft counter near))

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- A blank separates the current word from every earlier word, including the counter. -/
@[simp, grind =] theorem counterLeft_head (counter : List Γ) (near : List (List Γ)) :
    (counterLeft counter near).head = none := by
  cases near <;> simp [counterLeft]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- An empty counter before the first word does not add any occupied cells to the tape. -/
@[simp, grind =] theorem counterLeft_append_singleton (first : List Γ)
    (near : List (List Γ)) :
    counterLeft [] (near ++ [first]) = counterLeft first near := by
  induction near <;> simp_all [counterLeft]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
/-- Crossing separated words stores them in reverse order to the left of the head. -/
@[simp, grind =] theorem counterLeft_reverse (words : List (List Γ)) :
    words.foldl (fun left word => StackTape.cons none (StackTape.prepend word.reverse left))
      StackTape.nil = counterLeft [] words.reverse := by
  induction words using List.reverseRecOn with
  | nil => simp [counterLeft]
  | append_singleton words word ih =>
    simp [List.foldl_append, List.reverse_append, ih, counterLeft]

/--
This machine template visits the counter beyond `count` intervening words and restores the
head. Its action must keep the counter's right boundary fixed so the other words do not move.
-/
@[expose] def onCounter (tm : SingleTapeTM Γ) (action : Prog (TMQuery tm) Unit) :
    Nat → Prog (TMQuery tm) Unit
  | 0 => do [TMQuery tm]
    previousRegion tm
    action
    nextRegion tm
  | count + 1 => do [TMQuery tm]
    previousRegion tm
    onCounter tm action count
    nextRegion tm

/-- These are the intervening words, current word, and remaining tape as seen from the counter. -/
@[expose] def counterRight (near : List (List Γ)) (current : List Γ) (tail : StackTape Γ) :
    StackTape Γ :=
  StackTape.separateWords (near.reverse ++ [current]) tail

/--
The visit changes the counter and the tape beyond the current word as specified by the action.
All intervening words and the starting head position are preserved. The bound counts the
action and both crossings of every intervening word.
-/
@[spec] theorem onCounter_spec (action : Prog (TMQuery tm) Unit)
    (input output : List Γ) (near : List (List Γ)) (current : List Γ)
    (tail resultTail : StackTape Γ) (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost machineState => machineState.config = ⟨label,
          BiTape.segment StackTape.nil input (counterRight near current tail)⟩ ∧
          machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result,
          BiTape.segment StackTape.nil output (counterRight near current resultTail)⟩ ∧
          final.headPos = origin + input.length - output.length ∧
          cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost machineState => machineState.config =
        ⟨label, BiTape.segment (counterLeft input near) current tail⟩ ∧
        machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onCounter tm action near.length
    ⦃ fun _ cost final => final.config =
        ⟨result, BiTape.segment (counterLeft output near) current resultTail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + input.length + output.length +
          2 * (near.map List.length).sum + 4 * near.length + 4 ⦄ := by
  induction near generalizing current tail resultTail origin elapsed with
  | nil =>
    apply Std.WP.Triple.intro
    rintro initial machineState ⟨hcfg, hpos, hcost⟩
    simp only [List.length_nil, onCounter]
    vcgen [previousRegion_spec (tm := tm) StackTape.nil input current tail label origin
        initial.steps,
      haction (origin - (input.length + 1 : Nat)) (initial.steps + input.length + 3),
      nextRegion_le_spec (tm := tm) StackTape.nil output current resultTail result
        (origin - (output.length + 1 : Nat)) (initial.steps + input.length + 3 + bound)]
    all_goals
      simp_all [counterLeft, counterRight]
      all_goals lia
  | cons word near ih =>
    apply Std.WP.Triple.intro
    rintro initial machineState ⟨hcfg, hpos, hcost⟩
    have ha (position : ℤ) (steps : Nat) := haction position steps
    have hr := ih word (StackTape.prepend current (StackTape.cons none tail))
      (StackTape.prepend current (StackTape.cons none resultTail))
      (by simpa [counterRight, List.reverse_cons, StackTape.separateWords_append] using ha)
      (origin - (word.length + 1 : Nat)) (initial.steps + word.length + 3)
    simp only [List.length_cons, onCounter]
    vcgen [previousRegion_spec (tm := tm) ((counterLeft input near).tail) word current tail
        label origin initial.steps,
      hr,
      nextRegion_le_spec (tm := tm) (counterLeft output near) word current resultTail result
        (origin - (word.length + 1 : Nat))
        (initial.steps + word.length + 3 + bound + input.length + output.length +
          2 * (near.map List.length).sum + 4 * near.length + 4)]
    all_goals
      simp_all [counterLeft, counterRight]
      all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
