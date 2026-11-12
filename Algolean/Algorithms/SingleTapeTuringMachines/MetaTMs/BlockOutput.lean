/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockIteration
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryWriting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FollowingWord

/-!
# Composing unary loops that append output

* `forBlocks_append_spec` describes a unary loop whose fixed action appends one output word
  for each selected index. It preserves the unary source and every other source word.
* `onFollowingBlocks_append_spec` runs such a loop on the word after a selected cell and
  then returns to that cell. This lets several unary loops run inside one another.

The functions describing the appended words occur only in the specifications. The programs
remain the existing fixed `forBlocks` and `onFollowingWord` templates.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
The loop appends the specified words in increasing index order. Its fixed action preserves
all source words, and the source is restored with the head at its first cell.
-/
theorem forBlocks_append_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (count : Nat) (near parts : List (List Γ)) (output : List Γ) (piece : Nat → List Γ)
    (label : Option tm.State) (bound : Nat)
    (haction : ∀ index rest, index + rest + 1 = count → ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          markedUnaryTape near (List.replicate index tick) (List.replicate rest tick :: parts)
            (output ++ (List.range index).flatMap piece)⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label,
          markedUnaryTape near (List.replicate index tick) (List.replicate rest tick :: parts)
            (output ++ (List.range (index + 1)).flatMap piece)⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (counterLeft [] near) (List.replicate count tick)
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forBlocks tm tick [] action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (counterLeft [] near) (List.replicate count tick)
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (List.range count).flatMap piece)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + count * (bound + 2) + 2 ⦄ := by
  let tails := fun index => StackTape.separateWords parts
    (StackTape.mapSome (output ++ (List.range index).flatMap piece))
  have ha : BlockAction tick [] count (fun _ => (counterLeft [] near).tail) tails
      label action bound := by
    intro index rest hcount position steps
    simpa [markedUnaryTape, tails] using haction index rest hcount position steps
  vcgen [forBlocks_spec tick [] count (fun _ => (counterLeft [] near).tail) tails
    label action bound ha origin elapsed]
  all_goals simp_all [tails]

/--
The selected cell and both unary words are preserved while the following word's loop appends
its output. The head returns to the selected cell, with only linear extra travel time.
-/
theorem onFollowingBlocks_append_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (near : List (List Γ)) (crossed : List Γ) (remaining count : Nat)
    (parts : List (List Γ)) (output : List Γ) (piece : Nat → List Γ)
    (label : Option tm.State) (bound : Nat)
    (haction : ∀ index rest, index + rest + 1 = count → ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          markedUnaryTape (List.replicate remaining tick :: crossed :: near)
            (List.replicate index tick) (List.replicate rest tick :: parts)
            (output ++ (List.range index).flatMap piece)⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label,
          markedUnaryTape (List.replicate remaining tick :: crossed :: near)
            (List.replicate index tick) (List.replicate rest tick :: parts)
            (output ++ (List.range (index + 1)).flatMap piece)⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        markedUnaryTape near crossed
          (List.replicate remaining tick :: List.replicate count tick :: parts) output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      onFollowingWord tm (forBlocks tm tick [] action)
    ⦃ fun _ cost final => final.config = ⟨label,
        markedUnaryTape near crossed
          (List.replicate remaining tick :: List.replicate count tick :: parts)
          (output ++ (List.range count).flatMap piece)⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + count * (bound + 2) +
          2 * remaining + 8 ⦄ := by
  let left := StackTape.prepend crossed.reverse (counterLeft [] near)
  let inside := List.replicate remaining tick :: crossed :: near
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let resultTail := StackTape.separateWords parts
    (StackTape.mapSome (output ++ (List.range count).flatMap piece))
  have ha (position : ℤ) (steps : Nat) := forBlocks_append_spec tick action count inside
    parts output piece label bound haction position steps
  have hr := onFollowingWord_spec (tm := tm) (forBlocks tm tick [] action) left
    (List.replicate remaining tick) (List.replicate count tick) tail resultTail label label
    (count * (bound + 2) + 2) (by
      simpa [inside, counterLeft, left, tail, resultTail, Nat.add_assoc] using ha) origin elapsed
  vcgen [hr]
  all_goals
    simp_all [markedUnaryTape, left, tail, resultTail, StackTape.separateWords]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
