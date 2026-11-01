/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic

/-!
# Verified single-tape machine components

A component bundles one existing query program with a total correctness contract. There is no
new instruction language or interpreter. The logical parameter of the contract is quantified
after the program has been fixed: it is not an argument to the executable program.

`Computer tm f time` specializes this interface to word transformations. It accepts arbitrary
control states, head origins, allocated storage, and visits, preserves the control state, and
returns the head to the first output cell. Scans can use the general `Component` interface.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State]

/-- One fixed program and a total contract, indexed by logical specification data only. -/
structure Component {ι : Type} (pre : ι → TMState tm → Prop)
    (post : ι → TMState tm → TMCost → TMState tm → Prop) where
  /-- Fixed executable code; neither the input nor its length is an argument. -/
  program : Prog (TMQuery tm) Unit
  /-- Termination, resource accounting, and the specified final state on every valid input. -/
  correct : ∀ i s, pre i s → ∃ cost final,
    Completes program s cost final ∧ post i s cost final

/-- A verified transformation between encoded data. Encodings and the final absolute head
position are specification data; the default preserves the supplied head origin. -/
abbrev EncodedComputer {α β : Type} (inputEncoding : α → List Symbol)
    (outputEncoding : β → List Symbol) (f : α → β) (time : α → ℕ)
    (headPosition : α → ℤ → ℤ := fun _ origin => origin) :=
  Component tm (fun input s => s.config.BiTape = BiTape.mk₁ (inputEncoding input))
    (fun input s cost final =>
      final.config = {s.config with BiTape := BiTape.mk₁ (outputEncoding (f input))} ∧
      final.headPos = headPosition input s.headPos ∧ cost.steps ≤ time input)

/-- A verified word transformation, preserving control state and restoring the head origin. -/
abbrev Computer (f : List Symbol → List Symbol) (time : List Symbol → ℕ) :=
  EncodedComputer tm id id f time

namespace Component

variable {tm} {ι : Type} {pre : ι → TMState tm → Prop}
variable {post : ι → TMState tm → TMCost → TMState tm → Prop}

/-- Run a component through the existing model, retaining the entire supplied machine state. -/
def execute (machine : Component tm pre post) (fuel : ℕ) (s : TMState tm) :=
  TMQuery.execute fuel machine.program s

/-- A component's contract also bounds additional tape storage by its actual head-move cost. -/
theorem space (machine : Component tm pre post) (i : ι) (s : TMState tm) (h : pre i s) :
    ∃ cost final, Completes machine.program s cost final ∧ post i s cost final ∧
      cost.cellsAllocated ≤ cost.steps ∧
      final.cellsAllocated.card = s.cellsAllocated.card + cost.cellsAllocated := by
  obtain ⟨cost, final, hc, hp⟩ := machine.correct i s h
  exact ⟨cost, final, hc, hp, hc.space_le_time, hc.space_eq⟩

end Component

end Algolean.Algorithms
