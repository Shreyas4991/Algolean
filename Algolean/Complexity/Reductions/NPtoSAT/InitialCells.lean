/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.PositionIteration
public import Algolean.Complexity.Reductions.NPToTMSAT.ChoiceIteration

/-!
# Writing the initial tape cells in order

The program selects time zero and visits every recorded tape position. At each position it
runs the containing machine's fixed cell writer. It restores every bound and the head position.

The action and control state are fixed when constructing the containing machine. The width,
state count, original input, and selected positions are read from the tape.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.InitialCells

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines
open NPToTMSAT NPToTMSAT.HeadChoices PositionIteration
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This selects time zero and runs the same fixed cell writer at every recorded position. -/
def writeCells (tm : SingleTapeTM Γ) (tick : Γ) (label : tm.State)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ label
  markFirst tick (forSelectedTimePositions tm tick action)

/-- The program joins the cell writer's outputs and restores every source word and the head. -/
@[spec] theorem writeCells_spec (tick : Γ) (label : tm.State)
    (action : Prog (TMQuery tm) Unit) (time positions states : Nat)
    (hpositions : 0 < positions) (hstates : 0 < states) (input output : List Γ)
    (piece : Nat → List Γ) (size bound : Nat)
    (hleaf : PositionSpec tick 0 time positions states input piece (some label) action size bound)
    (hsize : time + 2 * positions + 2 * states + input.length +
      (output ++ (List.range positions).flatMap piece).length + 32 ≤ size)
    (initial : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨initial,
        ChoiceIteration.layout tick (time + 1) positions states input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeCells tm tick label action
    ⦃ fun _ cost final => final.config = ⟨some label,
        ChoiceIteration.layout tick (time + 1) positions states input
          (output ++ (List.range positions).flatMap piece)⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + positionIterationMoves size bound ⦄ := by
  let parts := [List.replicate positions tick, List.replicate states tick,
    List.replicate positions tick, List.replicate states tick, input]
  have hi (position : ℤ) (steps : Nat) := forSelectedTimePositions_spec tick action 0 time
    positions states hpositions hstates input output piece (some label) size bound hleaf
    (by simpa only [Nat.zero_add] using hsize) position steps
  have hm := markFirst_spec (tm := tm) tick (forSelectedTimePositions tm tick action)
    StackTape.nil (List.replicate time tick)
    (StackTape.separateWords parts (StackTape.mapSome output))
    (StackTape.separateWords parts
      (StackTape.mapSome (output ++ (List.range positions).flatMap piece)))
    (some label) (positionIterationMoves size bound) (by
      intro position steps
      simpa [selectionTape, markedUnaryTape, counterLeft, parts] using hi position steps)
    origin elapsed
  vcgen [writeCells, hm]
  all_goals simp_all [ChoiceIteration.layout, parts, List.replicate_succ]

end Algolean.Algorithms.NPToSAT.InitialCells
