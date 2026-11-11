/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Verification
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Scanning

/-!
# Checking the verification rules for single-tape programs

* A loop changes the control state without moving the head and still finishes.
* A scan crosses a word of arbitrary length and records its exact time and final position.
* A move records the additional space, including the case where its destination was visited.
-/

public section

namespace AlgoleanTests.SingleTapeTMVerification

open Algolean.Algorithms Cslib Cslib.Turing TMQuery SingleTapeTuringMachines
open scoped TMQuery TMQuery.Spec

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This machine uses Boolean symbols and two control labels. -/
abbrev control : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This program leaves the loop after changing its control label from false to true. -/
def finishLoop : Prog (TMQuery control) Unit := do [TMQuery control]
  whileₜ (state =ₜ some false) do
    state ←ₜ true

/-- A loop can terminate by changing its control state while making no head moves. -/
theorem state_loop_correct (s : TMState control) (hstate : s.config.state = some false) :
    ∃ cost final, Completes finishLoop s cost final ∧ final.config.state = some true ∧
      final.config.BiTape = s.config.BiTape ∧ final.headPos = s.headPos ∧ cost.steps = 0 := by
  apply Spec.completes
  vcgen [finishLoop, Spec.while_spec (rank := fun current : TMState control =>
    if current.config.state = some false then 1 else 0)] invariants
  · fun cost current => cost = 0 ∧ current.config.BiTape = s.config.BiTape ∧
      current.headPos = s.headPos ∧
      (current.config.state = some false ∨ current.config.state = some true)
  all_goals simp_all [TMCondition.eval]
  all_goals grind


/-- The loop rule proves the exact tape, head position, and time of a scan over any word. -/
theorem scan_correct (left right : List Γ) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekRightBlank tm) s (cursor (right.reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  apply Spec.runs
  vcgen [seekRightBlank, Spec.while_spec (rank := fun current : TMState tm =>
    (s.headPos + right.length - current.headPos).toNat)] invariants
  · fun cost current => ∃ crossed remaining : List Γ,
      right = crossed ++ remaining ∧
      current.config = ⟨s.config.state, cursor (crossed.reverse ++ left) remaining⟩ ∧
      current.headPos = s.headPos + crossed.length ∧ cost.steps = crossed.length
  case vc1 =>
    rename_i cost current h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨[], right, by simp, ?_, by simp, by simp⟩
    cases hcfg : current.config
    simp_all
  case vc2 =>
    simp only [TMCondition.eval] at *
    grind [cursor_head, List.head?_eq_none_iff]
  case vc3 =>
    rename_i initial original hstart n cost current h
    rcases h with ⟨⟨crossed, remaining, heq, hcfg, hpos, hcost⟩, hguard, hrank⟩
    cases remaining with
    | nil => simp [TMCondition.eval, hcfg] at hguard
    | cons bit remaining =>
      refine ⟨⟨crossed ++ [bit], remaining, by simpa using heq, ?_, ?_, ?_⟩, ?_⟩
      · simp [TMState.move, hcfg, List.reverse_append]
      · simp [TMState.move, hpos]
        lia
      · simp [hcost, TMState.moveCost]
      · have hbefore : s.headPos + right.length - current.headPos =
            (remaining.length + 1 : Nat) := by
          rw [hpos, heq]
          simp only [List.length_append, List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
        have hafter : s.headPos + right.length - (current.move .Right).headPos =
            (remaining.length : Int) := by
          simp only [TMState.move_headPos, Dir.offset]
          lia
        rw [hbefore, Int.toNat_natCast] at hrank
        rw [hafter, Int.toNat_natCast]
        lia


/-- The cost and final tape range both record whether the move reaches a new cell. -/
theorem move_tracks_space (s : TMState tm) :
    ∃ cost final, Completes (do [TMQuery tm] moveₜ .Right) s cost final ∧
      final.headPos = s.headPos + 1 ∧ cost.steps = 1 ∧
      cost.cellsAllocated = (if s.headPos + 1 ∈ s.cellsAllocated then 0 else 1) ∧
      final.cellsAllocated = insert (s.headPos + 1) s.cellsAllocated := by
  apply Spec.completes
  vcgen
  simp_all [TMState.moveCost]

end AlgoleanTests.SingleTapeTMVerification
