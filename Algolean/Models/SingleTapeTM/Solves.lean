/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Basic
public import Algolean.Problems.Basic

/-!
# Correctness, time, and space for one fixed program

`TMSolves` requires one Query program to finish on every input with an allowed final
configuration. Time counts move instructions, including stationary moves. Space counts every
initial input cell and every cell reached during execution, with at least one cell for empty
input. Erasing a cell does not remove it from this count.

The program is fixed before the statement quantifies over input words. Its input is read from
the initialized tape. Lean arguments used to construct the program must therefore be chosen
independently of that input and its length. The program's type alone does not enforce this.

`TMQuery.ComputesWithin` requires the complete output word under the final head, as in CSLib's
function computation interface. `TMQuery.DecidesWithin` instead observes a fixed tape or state
condition when the program finishes. It permits other tape contents to remain. The condition
uses the machine's finite test syntax, so observing the answer cannot perform an arbitrary
Lean computation.

These predicates use the existing `Completes` execution relation. Completion means that the
Query program finishes; it does not require the underlying control label to be `none`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State]

/--
One fixed program finishes on every input in an allowed configuration, within the given time
and total space bounds. Both bounds are functions of input length. The specification describes
the required result; it is not an instruction evaluated by the running machine.
-/
def TMSolves (program : Prog (TMQuery tm) Unit) (spec : List Symbol → Set tm.Cfg)
    (time space : ℕ → ℕ) : Prop :=
  ∀ input, ∃ cost final, TMQuery.Completes program (TMState.init tm input) cost final ∧
    final.config ∈ spec input ∧ cost.steps ≤ time input.length ∧
      final.spaceUsed ≤ space input.length

namespace TMSolves

variable {tm} {program : Prog (TMQuery tm) Unit} {spec spec' : List Symbol → Set tm.Cfg}
variable {time space time' space' : ℕ → ℕ}

/-- Increasing either resource bound preserves the correctness statement. -/
theorem mono (h : TMSolves tm program spec time space)
    (htime : ∀ n, time n ≤ time' n) (hspace : ∀ n, space n ≤ space' n) :
    TMSolves tm program spec time' space' := by
  intro input
  obtain ⟨cost, final, hc, hs, ht, hb⟩ := h input
  exact ⟨cost, final, hc, hs, ht.trans (htime _), hb.trans (hspace _)⟩

/-- Allowing more final configurations preserves correctness and both resource bounds. -/
theorem consequence (h : TMSolves tm program spec time space)
    (hpost : ∀ input, spec input ⊆ spec' input) : TMSolves tm program spec' time space := by
  intro input
  obtain ⟨cost, final, hc, hs, ht, hb⟩ := h input
  exact ⟨cost, final, hc, hpost input hs, ht, hb⟩

/--
A time bound also gives a total space bound: the initial input occupies `max 1 n` cells, and
each charged move reaches at most one new cell. The result and program are unchanged.
-/
theorem of_time_bound
    (h : ∀ input, ∃ cost final, TMQuery.Completes program (TMState.init tm input) cost final ∧
      final.config ∈ spec input ∧ cost.steps ≤ time input.length) :
    TMSolves tm program spec time (fun n => max 1 n + time n) := by
  intro input
  obtain ⟨cost, final, hc, hs, ht⟩ := h input
  refine ⟨cost, final, hc, hs, ht, ?_⟩
  change final.cellsAllocated.card ≤ _
  rw [hc.space_eq]
  change (TMState.init tm input).spaceUsed + cost.cellsAllocated ≤ _
  rw [TMState.spaceUsed_init]
  exact Nat.add_le_add_left (hc.space_le_time.trans ht) _

/-- Total space includes the input and at least the initial head cell, even without any moves. -/
theorem space_lower_bound (h : TMSolves tm program spec time space) (input : List Symbol) :
    max 1 input.length ≤ space input.length := by
  obtain ⟨cost, final, hc, _, _, hb⟩ := h input
  have heq := hc.space_eq
  change final.cellsAllocated.card ≤ _ at hb
  rw [heq] at hb
  have hi := TMState.spaceUsed_init tm input
  dsimp only [TMState.spaceUsed] at hi
  lia

end TMSolves

namespace TMQuery

variable {tm}

/--
The program computes the specified function on every input within the time and total space
bounds. The final tape contains exactly the output word, with the head at its first cell.
The absolute head coordinate and final control label are unrestricted.
-/
abbrev ComputesWithin (program : Prog (TMQuery tm) Unit) (f : List Symbol → List Symbol)
    (time space : ℕ → ℕ) : Prop :=
  TMSolves tm program (fun input => {cfg | cfg.BiTape = BiTape.mk₁ (f input)}) time space

/--
The program finishes on every word within the time and total space bounds. The chosen machine
condition is true at completion exactly on words in the language. Other tape cells may retain
their contents. The condition is fixed for the language and every input length.
-/
abbrev DecidesWithin (program : Prog (TMQuery tm) Unit) (language : Language Symbol)
    (accept : TMCondition tm) (time space : ℕ → ℕ) : Prop :=
  TMSolves tm program (fun input => {cfg | accept.eval cfg = true ↔ input ∈ language}) time space

end TMQuery

end Algolean.Algorithms
