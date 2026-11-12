/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading

/-!
# Temporarily marking the first cell of a word

* `withCell` temporarily replaces any known cell and restores it after its fixed action.
* `markFirst` replaces a known first symbol by a blank, runs a fixed program at that blank,
  and restores the symbol when the program returns.
* `restoreFirst` performs the inverse operation, allowing a selected unary word to be read again.
* The action starts and finishes on the same cell. These wrappers add no head moves.

This is a machine template. The containing machine fixes the symbol and action once,
independently of the input and its length.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This template replaces a known current cell while its fixed action runs, then restores it.
The containing machine fixes both cell values and the action independently of every input.
-/
def withCell (tm : SingleTapeTM Γ) (original replacement : Option Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ replacement
  action
  tape ←ₜ original

/-- Restoring a known cell adds no head moves and preserves the action's changes elsewhere. -/
@[spec] theorem withCell_spec (original replacement : Option Γ)
    (action : Prog (TMQuery tm) Unit) (left right resultLeft resultRight : StackTape Γ)
    (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, ⟨replacement, left, right⟩⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result, ⟨replacement, resultLeft, resultRight⟩⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, ⟨original, left, right⟩⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      withCell tm original replacement action
    ⦃ fun _ cost final => final.config = ⟨result, ⟨original, resultLeft, resultRight⟩⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄ := by
  vcgen [withCell, haction origin elapsed]
  all_goals simp_all [TMState.write, BiTape.write]

/-- This template marks a known first symbol, runs a fixed action, and restores that symbol. -/
def markFirst (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  withCell tm (some tick) none action

/-- Marking and restoring the first symbol preserves the action's head position and time bound. -/
@[spec] theorem markFirst_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (left : StackTape Γ) (rest : List Γ) (tail resultTail : StackTape Γ)
    (label : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment left [] (StackTape.prepend rest (StackTape.cons none tail))⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨label,
          BiTape.segment left [] (StackTape.prepend rest (StackTape.cons none resultTail))⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment left (tick :: rest) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      markFirst tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment left (tick :: rest) resultTail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄ := by
  have ha := withCell_spec (tm := tm) (some tick) none action left
    (StackTape.prepend rest (StackTape.cons none tail)) left
    (StackTape.prepend rest (StackTape.cons none resultTail)) label label bound
    (by simpa [BiTape.segment] using haction) origin elapsed
  vcgen [markFirst, ha]
  all_goals simp_all [BiTape.segment]

/--
This template restores a known first symbol while its fixed action runs, then marks it again.
The action can therefore revisit a whole unary word whose first cell was temporarily erased.
-/
def restoreFirst (tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  withCell tm none (some tick) action

/-- Restoring and marking the first cell preserves the action's time bound and later changes. -/
@[spec] theorem restoreFirst_spec (tick : Γ) (action : Prog (TMQuery tm) Unit)
    (left : StackTape Γ) (rest : List Γ) (tail resultTail : StackTape Γ)
    (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment left (tick :: rest) tail⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config =
          ⟨result, BiTape.segment left (tick :: rest) resultTail⟩ ∧
          final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment left [] (StackTape.prepend rest (StackTape.cons none tail))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      restoreFirst tick action
    ⦃ fun _ cost final => final.config = ⟨result,
        BiTape.segment left [] (StackTape.prepend rest (StackTape.cons none resultTail))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄ := by
  have ha := withCell_spec (tm := tm) none (some tick) action left
    (StackTape.prepend rest (StackTape.cons none tail)) left
    (StackTape.prepend rest (StackTape.cons none resultTail)) label result bound
    (by simpa [BiTape.segment] using haction) origin elapsed
  vcgen [restoreFirst, ha]
  all_goals simp_all [BiTape.segment]


end Algolean.Algorithms.SingleTapeTuringMachines
