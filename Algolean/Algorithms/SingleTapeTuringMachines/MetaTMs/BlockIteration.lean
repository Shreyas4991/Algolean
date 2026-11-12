/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryIteration

/-!
# Repeating a program at each position in a unary word

* `forBlocks` runs the same program once for each repetition of a fixed, nonempty word.
  Each repetition represents one unit of the count. The loop temporarily erases its first
  symbol so the program can find that position again.
* The action restores that position and preserves the repeated word. It may change the tape
  on either side of the word. The loop restores the word and returns to its first cell.
* Cells farther left may contain other data. This allows one loop to run inside another.

This is a machine template. The repeated word and action are fixed when constructing the
containing machine. The number of repetitions is read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def blockLoop (tick : Γ) (unitTail : List Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ none
    action
    tape ←ₜ some tick
    moveCells tm .Right (unitTail.length + 1)

private theorem return_spec (left tail : StackTape Γ) (word : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.prepend word.reverse (StackTape.cons none left)) [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      seekLeftEnd tm
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.cons none left) word tail⟩ ∧
        final.headPos = origin - word.length ∧ cost.steps ≤ elapsed + word.length + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [seekLeftEnd_segment_spec left tail word.reverse [] label origin initial.steps]
  all_goals
    simp_all

/--
This machine template visits each repetition of `tick :: unitTail`. The action starts and
finishes on its temporarily erased first cell. The containing machine fixes both the repeated
word and action; neither depends on the number of repetitions on the tape.
-/
def forBlocks (tm : SingleTapeTM Γ) (tick : Γ) (unitTail : List Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  blockLoop tick unitTail action
  seekLeftEnd tm

/--
At iteration `index`, the action sees the preceding repetitions to its left and the remaining
repetitions to its right. It preserves those repetitions and returns to the erased cell. Its changes
to other cells are described by `lefts` and `tails` before and after the iteration.
-/
@[expose] def BlockAction (tick : Γ) (unitTail : List Γ) (count : Nat)
    (lefts tails : Nat → StackTape Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat) : Prop :=
  ∀ index rest, index + rest + 1 = count → ∀ (origin : ℤ) (elapsed : Nat),
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (unaryWord (tick :: unitTail) index).reverse
            (StackTape.cons none (lefts index)))
          [] (StackTape.prepend (unitTail ++ unaryWord (tick :: unitTail) rest)
            (StackTape.cons none (tails index)))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (unaryWord (tick :: unitTail) index).reverse
            (StackTape.cons none (lefts (index + 1))))
          [] (StackTape.prepend (unitTail ++ unaryWord (tick :: unitTail) rest)
            (StackTape.cons none (tails (index + 1))))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄

private theorem blockLoop_spec (tick : Γ) (unitTail : List Γ) (count : Nat)
    (lefts tails : Nat → StackTape Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat)
    (haction : BlockAction tick unitTail count lefts tails label action bound)
    (index rest : Nat) (hcount : index + rest = count) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (unaryWord (tick :: unitTail) index).reverse
            (StackTape.cons none (lefts index)))
          (unaryWord (tick :: unitTail) rest) (tails index)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      blockLoop tick unitTail action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (unaryWord (tick :: unitTail) count).reverse
            (StackTape.cons none (lefts count)))
          [] (tails count)⟩ ∧
        final.headPos = origin + (rest * (unitTail.length + 1) : Nat) ∧
        cost.steps ≤ elapsed + rest * (bound + unitTail.length + 1) ⦄ := by
  induction rest generalizing index origin elapsed with
  | zero =>
    have hi : index = count := by lia
    subst index
    unfold blockLoop
    vcgen [Spec.while_false_spec]
    simp_all [unaryWord, BiTape.segment]
  | succ rest ih =>
    have haction' := haction index rest (by lia) origin elapsed
    have hsource := unaryWord_succ (tick :: unitTail) rest
    have hm := moveCells_right_segment_spec (tm := tm)
      (StackTape.prepend (unaryWord (tick :: unitTail) index).reverse
            (StackTape.cons none (lefts (index + 1))))
      (tails (index + 1)) (tick :: unitTail) (unaryWord (tick :: unitTail) rest)
      label origin (elapsed + bound)
    norm_num only [List.length_cons] at hm
    unfold blockLoop
    vcgen [Spec.while_step_spec (loop := blockLoop tick unitTail action) (hloop := rfl),
      haction',
      hm,
      ih (index + 1) (by lia) (origin + (unitTail.length + 1 : Nat))
        (elapsed + bound + unitTail.length + 1)]
    all_goals
      simp_all [BlockAction, BiTape.segment, BiTape.write, TMState.write,
        List.reverse_append, StackTape.prepend_append]
      all_goals ring_nf at *
      all_goals lia

/--
The loop calls the same action at every repetition and preserves the repeated word.
It restores the starting head position. The final tape beyond the word is
`tails count`. The bound counts every action, every crossed cell, and the return scan.
-/
@[spec] theorem forBlocks_spec (tick : Γ) (unitTail : List Γ) (count : Nat)
    (lefts tails : Nat → StackTape Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat)
    (haction : BlockAction tick unitTail count lefts tails label action bound)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none (lefts 0)) (unaryWord (tick :: unitTail) count)
          (tails 0)⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forBlocks tm tick unitTail action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none (lefts count)) (unaryWord (tick :: unitTail) count)
          (tails count)⟩ ∧ final.headPos = origin ∧
        cost.steps ≤ elapsed + count * (bound + 2 * (unitTail.length + 1)) + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  have hloop := blockLoop_spec tick unitTail count lefts tails label action bound haction
    0 count (by simp) origin initial.steps
  vcgen [forBlocks, hloop,
    return_spec (lefts count) (tails count) (unaryWord (tick :: unitTail) count) label
      (origin + (count * (unitTail.length + 1) : Nat))
      (initial.steps + count * (bound + unitTail.length + 1))]
  all_goals
    simp_all [unaryWord, List.length_flatten]
    all_goals ring_nf at *
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
