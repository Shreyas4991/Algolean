/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SAT.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Clauses that restrict choices of Boolean variables

* `Clause.atLeastOne` requires at least one listed variable to be true.
* `Clause.forbid` prevents all listed variables from being true together.
* `Clause.implies` requires a conclusion when all listed premises are true.
* `CNF.exactlyOne` requires exactly one distinct listed variable to be true.

The statements use the assignments and formula evaluation already defined for SAT. Repeating
a variable in a list does not change which assignments satisfy these restrictions. The clauses
for at most one choice compare pairs of distinct variables, so their number is at most the
square of the list length.
-/

@[expose] public section

namespace Algolean.Problems.SAT

variable {α : Type u}

/-- This clause requires at least one listed variable to be true. An empty list is impossible. -/
def Clause.atLeastOne (names : List α) : Clause α := names.map Literal.pos

/-- This clause prevents all listed variables from being true together. -/
def Clause.forbid (names : List α) : Clause α := names.map Literal.neg

/-- This clause requires the conclusion to be true whenever every listed premise is true. -/
def Clause.implies (premises : List α) (conclusion : α) : Clause α :=
  forbid premises ++ [.pos conclusion]

/-- The clause is satisfied exactly when a listed variable is true. -/
@[simp] theorem Clause.atLeastOne_satisfiedBy (names : List α) (assignment : α → Bool) :
    (atLeastOne names).SatisfiedBy assignment ↔ ∃ name ∈ names, assignment name = true := by
  simp [satisfiedBy_iff_exists_literal, atLeastOne, Literal.SatisfiedBy]

/-- The clause is satisfied exactly when the listed variables are not all true. -/
@[simp] theorem Clause.forbid_satisfiedBy (names : List α) (assignment : α → Bool) :
    (forbid names).SatisfiedBy assignment ↔ ¬∀ name ∈ names, assignment name = true := by
  simp [satisfiedBy_iff_exists_literal, forbid, Literal.SatisfiedBy]

/-- The clause expresses implication under the same assignment for premises and conclusion. -/
@[simp] theorem Clause.implies_satisfiedBy (premises : List α) (conclusion : α)
    (assignment : α → Bool) :
    (implies premises conclusion).SatisfiedBy assignment ↔
      (∀ name ∈ premises, assignment name = true) → assignment conclusion = true := by
  simp [implies, Clause.SatisfiedBy, Clause.eval, List.or, forbid]
  grind

/-- There is one literal for each variable listed as a possible choice. -/
@[simp] theorem Clause.length_atLeastOne (names : List α) :
    (atLeastOne names).length = names.length := by simp [atLeastOne]

/-- There is one negated literal for each variable in the forbidden combination. -/
@[simp] theorem Clause.length_forbid (names : List α) :
    (forbid names).length = names.length := by simp [forbid]

/-- There is one literal for each premise and one for the conclusion. -/
@[simp] theorem Clause.length_implies (premises : List α) (conclusion : α) :
    (implies premises conclusion).length = premises.length + 1 := by simp [implies]

variable [DecidableEq α]

/--
These clauses prevent two distinct listed variables from both being true. Each ordered pair
of different variables contributes one clause. Repeated names do not forbid that variable alone.
-/
def CNF.atMostOne (names : List α) : CNF α :=
  names.flatMap fun first =>
    (names.filter fun second => second ≠ first).map fun second => Clause.forbid [first, second]

/-- This formula requires one listed variable to be true and prevents any other distinct choice. -/
def CNF.exactlyOne (names : List α) : CNF α := Clause.atLeastOne names :: atMostOne names

/-- Two listed variables can both be true exactly when they name the same variable. -/
@[simp] theorem CNF.atMostOne_satisfiedBy (names : List α) (assignment : α → Bool) :
    (atMostOne names).SatisfiedBy assignment ↔
      ∀ first ∈ names, ∀ second ∈ names,
        assignment first = true → assignment second = true → first = second := by
  simp only [satisfiedBy_iff_forall_clause, atMostOne, List.forall_mem_flatMap,
    List.forall_mem_map, List.forall_mem_filter, decide_eq_true_eq,
    Clause.forbid_satisfiedBy, List.forall_mem_cons]
  grind

/-- The formula is satisfied exactly when a unique distinct listed variable is true. -/
@[simp] theorem CNF.exactlyOne_satisfiedBy (names : List α) (assignment : α → Bool) :
    (exactlyOne names).SatisfiedBy assignment ↔
      ∃! name, name ∈ names ∧ assignment name = true := by
  rw [exactlyOne, satisfiedBy_iff_forall_clause, List.forall_mem_cons,
    ← satisfiedBy_iff_forall_clause, Clause.atLeastOne_satisfiedBy, atMostOne_satisfiedBy]
  grind [ExistsUnique]

/--
When every possible choice is listed and different choices have different variable names,
the formula requires a unique choice whose variable is true.
-/
theorem CNF.exactlyOne_map_satisfiedBy {β : Type v} (values : List β)
    (hvalues : ∀ value, value ∈ values) (name : β → α) (hinj : Function.Injective name)
    (assignment : α → Bool) :
    (exactlyOne (values.map name)).SatisfiedBy assignment ↔
      ∃! value, assignment (name value) = true := by
  rw [exactlyOne_satisfiedBy]
  constructor
  · rintro ⟨entry, ⟨hmem, htrue⟩, hunique⟩
    obtain ⟨value, _, rfl⟩ := List.mem_map.mp hmem
    exact ⟨value, htrue, fun other hother =>
      hinj (hunique (name other) ⟨List.mem_map.mpr ⟨other, hvalues other, rfl⟩, hother⟩)⟩
  · rintro ⟨value, htrue, hunique⟩
    refine ⟨name value, ⟨List.mem_map.mpr ⟨value, hvalues value, rfl⟩, htrue⟩, ?_⟩
    rintro entry ⟨hmem, hother⟩
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp hmem
    exact congrArg name (hunique other hother)

/-- The pair comparisons produce at most the square of the number of listed choices. -/
theorem CNF.length_atMostOne_le (names : List α) :
    (atMostOne names).length ≤ names.length ^ 2 := by
  simp only [atMostOne, List.length_flatMap, List.length_map]
  have h := List.sum_le_length_nsmul
    (names.map fun first => (names.filter fun second => decide (second ≠ first)).length)
    names.length (by
      intro n hn
      obtain ⟨name, _, rfl⟩ := List.mem_map.mp hn
      exact List.length_filter_le _ _)
  simpa [pow_two, Nat.mul_comm] using h

/-- Each pair comparison contributes exactly two literals. -/
theorem CNF.length_flatten_atMostOne (names : List α) :
    (atMostOne names).flatten.length = 2 * (atMostOne names).length := by
  rw [List.length_flatten]
  have h := List.sum_eq_length_nsmul ((atMostOne names).map List.length) 2 (by
    simp only [List.forall_mem_map, atMostOne, List.forall_mem_flatMap,
      Clause.length_forbid, List.length_cons, List.length_nil]
    simp)
  simpa [Nat.mul_comm] using h

/-- Requiring a choice adds one clause to the pair comparisons. -/
theorem CNF.length_exactlyOne_le (names : List α) :
    (exactlyOne names).length ≤ names.length ^ 2 + 1 := by
  simpa [exactlyOne] using Nat.add_le_add_right (length_atMostOne_le names) 1

/-- Each clause either lists all choices or compares two choices, so its length is bounded. -/
theorem CNF.clause_length_exactlyOne_le (names : List α) :
    ∀ clause ∈ exactlyOne names, clause.length ≤ names.length + 2 := by
  simp only [exactlyOne, List.forall_mem_cons, Clause.length_atLeastOne]
  constructor
  · lia
  · simp only [atMostOne, List.forall_mem_flatMap, List.forall_mem_map,
      Clause.length_forbid, List.length_cons, List.length_nil]
    simp

/-- The choice clause and pair comparisons have a quadratic bound on their literal occurrences. -/
theorem CNF.length_flatten_exactlyOne_le (names : List α) :
    (exactlyOne names).flatten.length ≤ names.length + 2 * names.length ^ 2 := by
  simp only [exactlyOne, List.flatten_cons, List.length_append, Clause.length_atLeastOne,
    length_flatten_atMostOne]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (length_atMostOne_le names)) _

end Algolean.Problems.SAT
