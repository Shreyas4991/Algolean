/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Search

/-!
# Problem specification and resource contract tests

Examples for abstract search specifications and the termination, correctness, and resource
guarantees required by `Problem.Solves` and `Problem.RunsWithin`.
-/

@[expose] public section

namespace AlgoleanTests.Problems

open Algolean

/-- Any positive number at most the input is an acceptable witness. -/
def positiveWitness : Problem Nat Nat where
  admissible n := 0 < n
  spec n output := 0 < output ∧ output ≤ n

example : positiveWitness.admissible 3 := by simp [positiveWitness]

example : ¬positiveWitness.admissible 0 := by simp [positiveWitness]

-- The output relation permits multiple valid answers for the same input.
example : positiveWitness.spec 3 1 ∧ positiveWitness.spec 3 2 := by simp [positiveWitness]

example : ¬positiveWitness.spec 3 4 := by simp [positiveWitness]

-- Restriction retains the original precondition and adds the new one.
example : ¬(positiveWitness.restrict (· ≤ 10)).admissible 0 := by simp [positiveWitness]

example : ¬(positiveWitness.restrict (· ≤ 10)).admissible 11 := by simp [positiveWitness]

example (P : Problem Input Output) (precondition : Input → Prop) (input : Input) :
    (P.restrict precondition).admissible input ↔ P.admissible input ∧ precondition input := by
  simp

example (P : Problem Input Output) (p q : Input → Prop) (input : Input) (output : Output) :
    ((P.restrict p).restrict q).spec input output ↔ P.spec input output := by
  simp

-- First-match and arbitrary-match search differ on duplicate keys.
example : Search.linearSearch.spec ⟨#[4, 1, 4], 4⟩ (some 0) := by
  simp [Search.IsFirstMatch]

example : ¬Search.linearSearch.spec ⟨#[4, 1, 4], 4⟩ (some 2) := by
  intro h
  exact h.right.right 0 (by decide) rfl

example : Search.search.spec ⟨#[4, 1, 4], 4⟩ (some 2) := by
  simp [Search.IsMatch]

example : Search.linearSearch.spec ⟨#[], (7 : Nat)⟩ none := by simp

example : ¬Search.search.spec ⟨#[4, 1, 4], 4⟩ none := by simp

example : ¬Search.search.spec ⟨#[4], 4⟩ (some 1) := by
  simp [Search.IsMatch]

-- An arbitrary-match answer alone does not certify the binary-search precondition.
example : ¬(Search.binarySearch Nat.le).admissible ⟨#[2, 1], 1⟩ := by
  intro h
  have hs := (Search.binarySearch_admissible _ _).mp h
  exact (by decide : ¬2 ≤ 1) (hs 0 1 (by decide) (by decide) (by decide))

example (data : Array α) (key : α) (i j : Nat)
    (hi : Search.IsFirstMatch data key i) (hj : Search.IsFirstMatch data key j) : i = j :=
  hi.unique hj

-- A fixed program is verified directly; the input is supplied only to its execution relation.
private def identityRun (_ : Unit) (s cost t : Nat) : Prop := cost = 1 ∧ t = s

private theorem identity_solves :
    positiveWitness.Solves () identityRun Eq Eq := by
  constructor
  · intro input s _ _
    exact ⟨1, s, rfl, rfl⟩
  · intro input s ha hi cost t hr
    obtain ⟨_, rfl⟩ := hr
    exact ⟨t, rfl, hi ▸ ha, Nat.le_of_eq hi.symm⟩

example : positiveWitness.RunsWithin () identityRun Eq (fun _ cost => cost ≤ 1) := by
  refine ⟨identity_solves.terminates, ?_⟩
  intro input s _ _ cost t hr
  exact hr.left ▸ Nat.le_refl 1

-- A relation with no completed executions satisfies neither predicate.
example : ¬positiveWitness.Solves () (fun _ _ (_ : Nat) _ => False) Eq Eq := by
  intro h
  obtain ⟨cost, t, hr⟩ := h.terminates 1 1 (by simp [positiveWitness]) rfl
  exact hr

example : ¬positiveWitness.RunsWithin () (fun _ _ (_ : Nat) _ => False) Eq
    (fun _ _ => True) := by
  intro h
  obtain ⟨cost, t, hr⟩ := h.terminates 1 1 (by simp [positiveWitness]) rfl
  exact hr

-- One good outcome does not excuse another execution with an invalid answer.
example : ¬positiveWitness.Solves () (fun _ (_ : Nat) (_ : Nat) (_ : Nat) => True) Eq Eq := by
  intro h
  obtain ⟨output, rfl, hs⟩ := h.correct 1 1 (by simp [positiveWitness]) rfl 1 0 trivial
  exact Nat.lt_irrefl 0 hs.left

-- Resource bounds cover every completed execution, not just a cheap witness.
example : ¬positiveWitness.RunsWithin ()
    (fun _ (s : Nat) (_ : Nat) t => t = s) Eq (fun _ cost => cost ≤ 1) := by
  intro h
  exact (by decide : ¬2 ≤ 1) (h.bounded 1 1 (by simp [positiveWitness]) rfl 2 1 rfl)

end AlgoleanTests.Problems
