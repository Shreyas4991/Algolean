/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.Frame
public import Algolean.Models.SingleTapeTM.Composition.Relabel
public import Algolean.Models.SingleTapeTM.Composition.While
public import AlgoleanTests.SingleTapeTMExamples

/-!
# Single-tape composition examples

These examples compose verified components while retaining tape history, reuse them at a
different head origin, and relabel finite control inside a loop and a branch.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMComposition

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery

/-- Reuse the Boolean control alphabet of the interpreter examples. -/
abbrev machine := SingleTapeTMExamples.machine

/-- Visit the next cell and return to the starting position. -/
def excursion : Prog (TMQuery machine) Unit := do
  FreeM.lift (.move .Right)
  FreeM.lift (.move .Left)

/-- Sequential composition proves the tape and head are restored with exactly two moves. -/
theorem excursion_runs (s : TMState machine) :
    Runs excursion s s.config.BiTape s.headPos 2 := by
  refine ⟨_, _, (completes_move s .Right).seq (completes_move (s.move .Right) .Left),
    ?_, ?_, ?_⟩
  · simp [TMState.move]
  · simp
  · simp [TMState.moveCost]

/-- A verified identity transformation that physically visits one neighboring cell. -/
def excursionComputer : Computer machine id (fun _ => 2) where
  program := excursion
  correct input s hs := by
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := excursion_runs s
    exact ⟨cost, final, hc, by simpa [hs] using ht, hp, hm.le⟩

-- Repeating a component adds time while charging the newly reached cell only once.
example :
    (execute 4 (EncodedComputer.seq excursionComputer excursionComputer).program
      (TMState.init machine [])).map
      (fun (result, final) => (final.machine.headPos, result.tell.steps,
        result.tell.cellsAllocated, final.machine.cellsAllocated.card, final.fuel)) =
      some (0, 4, 1, 2, 0) := by decide

-- Both procedures retain the existing storage and the nonzero starting head position.
example :
    let initial : TMState machine := {TMState.init machine [true, false] with
      headPos := 37
      cellsAllocated := Finset.Icc 35 41
      cellsVisited := {37}}
    (execute 4 (EncodedComputer.seq excursionComputer excursionComputer).program initial).map
      (fun (result, final) => (final.machine.headPos, result.tell.steps,
        result.tell.cellsAllocated, final.machine.cellsAllocated.card)) =
      some (37, 4, 0, 7) := by decide

-- The composed specification records the state between the two procedures and each one's cost.
example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ (a : TMCost) (middle : TMState machine) (b : TMCost) (final : TMState machine),
      Completes (do excursion; excursion) s (a + b) final ∧
      middle.headPos = s.headPos ∧ final.headPos = middle.headPos := by
  let composed := excursionComputer.andThen excursionComputer id
    (by intro _ _ _ _ _ h; exact h.1 ▸ rfl)
  obtain ⟨cost, final, hc, a, middle, b, rfl, ha, hb⟩ := composed.correct input s hs
  exact ⟨a, middle, b, final, hc, ha.2.1, hb.2.1⟩

/-- Exit a loop by setting the fixed control label to `true`. -/
def finishLoop : Prog (TMQuery machine) Unit :=
  whileLoop (.stateIs (some false)) (FreeM.lift (.update true))

theorem finishLoop_completes (s : TMState machine) (h : s.config.state = some false) :
    Completes finishLoop s 0 {s with config.state := some true} := by
  simpa [finishLoop] using (completes_update s true).while_step
    (by simp [TMCondition.eval, h])
    (completes_while_false (tm := machine) (.stateIs (some false)) (FreeM.lift (.update true))
      {s with config.state := some true} (by simp))

-- Branch contracts select the excursion using the current machine state.
example (s : TMState machine) (h : s.config.state = some false) :
    Runs (branch (.stateIs (some false)) excursion (pure ())) s s.config.BiTape s.headPos 2 :=
  Runs.branch (by simpa [TMCondition.eval, h] using excursion_runs s)

/-- A larger finite control alphabet for an independently relabeled execution. -/
abbrev target : SingleTapeTM Bool where
  State := Bool × Bool
  q₀ := (false, false)
  tr _ symbol := (⟨symbol, none⟩, none)

/-- Embed the original labels in one half of the target's control alphabet. -/
def embed (label : machine.State) : target.State := (label, false)

theorem embed_injective : Function.Injective embed := fun _ _ h => congrArg Prod.fst h

-- Relabeling preserves a proved loop contract, its exact cost, and the tape history.
example (s : TMState machine) (h : s.config.state = some false) :
    Completes (finishLoop.reduceProg (relabelReduction (target := target) embed))
      (s.relabel embed) 0
      (({s with config.state := some true} : TMState machine).relabel embed) :=
  (finishLoop_completes s h).relabel embed embed_injective

-- Labels inside both structured constructs must be mapped, as well as the update itself.
example :
    (execute 5 (Prog.reduceProg (do
      finishLoop
      branch (.stateIs (some true)) (FreeM.lift (.move .Right)) (FreeM.lift (.move .Left)))
        (relabelReduction (target := target) embed))
      ((TMState.init machine []).relabel embed)).map
        (fun (result, final) => (final.machine.config.state, final.machine.headPos,
          result.tell.steps, result.tell.cellsAllocated, final.fuel)) =
      some (some (true, false), 1, 1, 1, 0) := by decide +kernel

end AlgoleanTests.SingleTapeTMComposition
