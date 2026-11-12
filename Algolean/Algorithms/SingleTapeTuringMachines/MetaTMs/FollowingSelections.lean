/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.BlockOutput

/-!
# Visiting choices in several following unary words

* `forFollowingSelections` chooses one cell from each of a fixed number of following words.
  It visits every combination of choices. Each word repeats one fixed symbol, and a temporarily
  erased cell records the current choice. The program restores all words before returning.
* Its specification composes one fixed action over those combinations in order. The source
  lengths and chosen indices occur only in the specification and are read from the tape.

These are machine templates. The containing machine fixes the number of loops and the action
before execution. The number of cells in each loop is determined by its unary word.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This visits a fixed number of following unary words, nesting their loops in tape order. -/
def forFollowingSelections (tm : SingleTapeTM Γ) (tick : Γ)
    (action : Prog (TMQuery tm) Unit) : Nat → Prog (TMQuery tm) Unit
  | 0 => action
  | depth + 1 => do [TMQuery tm]
    onFollowingWord tm (forBlocks tm tick [] (forFollowingSelections tm tick action depth))

/-- This describes the tape with one temporarily erased cell in each word already visited. -/
@[expose] def selectionTape (tick : Γ) (earlier : List (Nat × Nat)) (current : Nat × Nat)
    (following : List Nat) (input output : List Γ) : BiTape Γ :=
  markedUnaryTape (earlier.flatMap fun pair =>
      [List.replicate pair.2 tick, List.replicate pair.1 tick]) (List.replicate current.1 tick)
    (List.replicate current.2 tick :: following.map (fun count => List.replicate count tick) ++
      [input]) output

/-- This describes the tape after temporarily erasing one chosen cell in every following word. -/
@[expose] def selectedTape (tick : Γ) (earlier : List (Nat × Nat)) (current : Nat × Nat) :
    List (Nat × Nat) → List Γ → List Γ → BiTape Γ
  | [], input, output => selectionTape tick earlier current [] input output
  | pair :: rest, input, output => selectedTape tick (current :: earlier) pair rest input output

/-- This concatenates one word for every combination of indices, in their loop order. -/
@[expose] def selectionWord (piece : List Nat → List Γ) : List Nat → List Γ
  | [] => piece []
  | count :: rest => (List.range count).flatMap fun index =>
    selectionWord (fun indices => piece (index :: indices)) rest

/-- This bounds the nested loops using one upper bound on their word lengths and action costs. -/
@[expose] def selectionMoves (size bound : Nat) : Nat → Nat
  | 0 => bound
  | depth + 1 => size * (selectionMoves size bound depth + 2) + 2 * size + 8

/--
This composes the action's specification over every choice. The action preserves the selected
cells, and the loop restores all following words and the original head position.
-/
theorem forFollowingSelections_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (earlier : List (Nat × Nat)) (current : Nat × Nat) (following : List Nat)
    (input output : List Γ) (piece : List Nat → List Γ) (label : Option tm.State)
    (base size bound : Nat) (hrest : current.2 ≤ size)
    (hcounts : ∀ count ∈ following, count ≤ size)
    (hleaf : ∀ selected, List.Forall₂ (fun pair count => pair.1 + pair.2 + 1 = count)
        selected following → ∀ written,
      base + (written ++ piece (selected.map Prod.fst)).length ≤ size →
      ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost initial => initial.config =
          ⟨label, selectedTape tick earlier current selected input written⟩ ∧
          initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config =
          ⟨label, selectedTape tick earlier current selected input
            (written ++ piece (selected.map Prod.fst))⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (hsize : base + (output ++ selectionWord piece following).length ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config =
        ⟨label, selectionTape tick earlier current following input output⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forFollowingSelections tm tick action following.length
    ⦃ fun _ cost final => final.config = ⟨label,
        selectionTape tick earlier current following input
          (output ++ selectionWord piece following)⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + selectionMoves size bound following.length ⦄ := by
  induction following generalizing earlier current output piece origin elapsed with
  | nil =>
    simpa [forFollowingSelections, selectedTape, selectionWord, selectionMoves] using
      hleaf [] .nil output hsize origin elapsed
  | cons count following ih =>
    let next := fun index => selectionWord (fun indices => piece (index :: indices)) following
    have ha (index rest : Nat) (hcount : index + rest + 1 = count)
        (position : ℤ) (steps : Nat) := ih (current :: earlier) (index, rest)
      (output ++ (List.range index).flatMap next) (fun indices => piece (index :: indices))
      (by have := hcounts count (by simp); lia)
      (by intro n hn; exact hcounts n (by simp [hn]))
      (by
        intro selected hselected written hbound origin elapsed
        simpa [selectedTape] using hleaf ((index, rest) :: selected)
          (.cons hcount hselected) written hbound origin elapsed)
      (by
        have hp := ((List.range_sublist.mpr (show index + 1 ≤ count by lia)).flatMap next).length_le
        have hout : ((output ++ (List.range index).flatMap next) ++ next index).length ≤
            (output ++ selectionWord piece (count :: following)).length := by
          simpa [selectionWord, next, List.range_succ, List.length_append, Nat.add_assoc] using
            Nat.add_le_add_left hp output.length
        simpa only [next, List.append_assoc] using
          (show base + ((output ++ (List.range index).flatMap next) ++ next index).length ≤
            size by lia)) position steps
    have hr := onFollowingBlocks_append_spec tick
      (forFollowingSelections tm tick action following.length)
      (earlier.flatMap fun pair => [List.replicate pair.2 tick, List.replicate pair.1 tick])
      (List.replicate current.1 tick) current.2 count
      (following.map (fun n => List.replicate n tick) ++ [input]) output next label
      (selectionMoves size bound following.length) (by
        intro index rest hcount position steps
        simpa [selectionTape, next, List.range_succ, List.append_assoc] using
          ha index rest hcount position steps) origin elapsed
    have hwork : count * (selectionMoves size bound following.length + 2) +
        2 * current.2 + 8 ≤ selectionMoves size bound (count :: following).length := by
      simp only [List.length_cons, selectionMoves]
      gcongr
      exact hcounts count (by simp)
    simp only [List.length_cons, forFollowingSelections]
    vcgen [hr]
    all_goals simp_all [selectionTape, selectionWord, next]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
