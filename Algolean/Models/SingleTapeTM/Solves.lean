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

`TMSolves` requires one Query program to finish on every input with an allowed output word.
The tape must contain exactly that word, with the head at its first cell and blanks everywhere
outside the word. This is CSLib's output convention. The head need not return to its starting cell.
Time counts move instructions, including stationary moves. Space counts every
initial input cell and every cell reached during execution, with at least one cell for empty
input. Erasing a cell does not remove it from this count.

The program is fixed before the statement quantifies over input words. Its input is read from
the initialized tape. Lean arguments used to construct the program must therefore be chosen
independently of that input and its length. The program's type alone does not enforce this.

`TMQuery.ComputesWithin` specifies one output for each input. `TMQuery.DecidesWithin` requires
the output to equal a fixed acceptance word exactly on inputs in the language. Rejection may
produce any other complete word. Both use CSLib's clean-output convention. Internal components
that report answers in control states or retain temporary regions use `Component` and `Runs`.

These predicates use the existing `Completes` execution relation. Completion means that the
Query program finishes; it does not require the underlying control label to be `none`.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable (tm : SingleTapeTM Symbol) [DecidableEq Symbol] [DecidableEq tm.State]

/--
One fixed program finishes on every input with an allowed output word on an otherwise blank
tape, with the head at its first cell. Time and total space are bounded by functions of input
length. The specification describes the output; the running machine does not evaluate it.
-/
def TMSolves (program : Prog (TMQuery tm) Unit) (spec : List Symbol → Set (List Symbol))
    (time space : ℕ → ℕ) : Prop :=
  ∀ input, ∃ output cost final, TMQuery.Completes program (TMState.init tm input) cost final ∧
    final.config.BiTape = BiTape.mk₁ output ∧ output ∈ spec input ∧ cost.steps ≤ time input.length ∧
      final.spaceUsed ≤ space input.length

namespace TMSolves

variable {tm} {program : Prog (TMQuery tm) Unit} {spec spec' : List Symbol → Set (List Symbol)}
variable {time space time' space' : ℕ → ℕ}

/-- Increasing either resource bound preserves the correctness statement. -/
theorem mono (h : TMSolves tm program spec time space)
    (htime : ∀ n, time n ≤ time' n) (hspace : ∀ n, space n ≤ space' n) :
    TMSolves tm program spec time' space' := by
  intro input
  obtain ⟨output, cost, final, hc, ho, hs, ht, hb⟩ := h input
  exact ⟨output, cost, final, hc, ho, hs, ht.trans (htime _), hb.trans (hspace _)⟩

/-- Allowing more output words preserves correctness and both resource bounds. -/
theorem consequence (h : TMSolves tm program spec time space)
    (hpost : ∀ input, spec input ⊆ spec' input) : TMSolves tm program spec' time space := by
  intro input
  obtain ⟨output, cost, final, hc, ho, hs, ht, hb⟩ := h input
  exact ⟨output, cost, final, hc, ho, hpost input hs, ht, hb⟩

/--
A time bound also gives a total space bound: the initial input occupies `max 1 n` cells, and
each charged move reaches at most one new cell. The result and program are unchanged.
-/
theorem of_time_bound
    (h : ∀ input, ∃ output cost final,
      TMQuery.Completes program (TMState.init tm input) cost final ∧
      final.config.BiTape = BiTape.mk₁ output ∧ output ∈ spec input ∧
        cost.steps ≤ time input.length) :
    TMSolves tm program spec time (fun n => max 1 n + time n) := by
  intro input
  obtain ⟨output, cost, final, hc, ho, hs, ht⟩ := h input
  refine ⟨output, cost, final, hc, ho, hs, ht, ?_⟩
  change final.cellsAllocated.card ≤ _
  rw [hc.space_eq]
  change (TMState.init tm input).spaceUsed + cost.cellsAllocated ≤ _
  rw [TMState.spaceUsed_init]
  exact Nat.add_le_add_left (hc.space_le_time.trans ht) _

/-- Total space includes the input and at least the initial head cell, even without any moves. -/
theorem space_lower_bound (h : TMSolves tm program spec time space) (input : List Symbol) :
    max 1 input.length ≤ space input.length := by
  obtain ⟨output, cost, final, hc, _, _, _, hb⟩ := h input
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
  TMSolves tm program (fun input => {f input}) time space

/--
The program finishes on every input with a complete output word on an otherwise blank tape,
with the head at its first cell. Its output equals the fixed acceptance word exactly when the
input belongs to the language. Rejection may produce any other complete word.
-/
abbrev DecidesWithin (program : Prog (TMQuery tm) Unit) (language : Language Symbol)
    (accept : List Symbol) (time space : ℕ → ℕ) : Prop :=
  TMSolves tm program (fun input => {output | output = accept ↔ input ∈ language}) time space

end TMQuery

end Algolean.Algorithms
