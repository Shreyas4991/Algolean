/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions

/-!
# Visiting the word after a selected cell

* `onFollowingWord` starts at a blank that temporarily marks a selected cell. It crosses the
  rest of that word and runs a fixed program at the next word.
* The action preserves both words and may change the later tape. The head then returns to
  the selected blank.

This is a machine template. The containing machine fixes its action independently of every
word length and input.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This template visits the next word after a selected blank and returns to that blank. -/
def onFollowingWord (tm : SingleTapeTM Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  nextRegion tm
  action
  previousRegion tm
  moveₜ .Left

/-- The visit preserves both words and the selected blank and adds only linear travel time. -/
@[spec] theorem onFollowingWord_spec (action : Prog (TMQuery tm) Unit)
    (left : StackTape Γ) (remaining word : List Γ) (tail resultTail : StackTape Γ)
    (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment
          (StackTape.cons none (StackTape.prepend remaining.reverse (StackTape.cons none left)))
          word tail⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment
          (StackTape.cons none (StackTape.prepend remaining.reverse (StackTape.cons none left)))
          word resultTail⟩ ∧ final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment left [] (StackTape.separateWords [remaining, word] tail)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onFollowingWord tm action
    ⦃ fun _ cost final => final.config =
        ⟨result, BiTape.segment left [] (StackTape.separateWords [remaining, word] resultTail)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound + 2 * remaining.length + 6 ⦄ := by
  vcgen [onFollowingWord,
    nextRegion_le_spec (tm := tm) (StackTape.cons none left) remaining word tail label
      (origin + 1) (elapsed + 1),
    haction (origin + (remaining.length + 2 : Nat)) (elapsed + remaining.length + 2),
    previousRegion_le_spec (tm := tm) left remaining word resultTail result
      (origin + (remaining.length + 2 : Nat)) (elapsed + remaining.length + 2 + bound)]
  all_goals
    simp_all [TMState.move, TMState.moveCost, StackTape.separateWords]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
