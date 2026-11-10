/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Flatten
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Boolean satisfiability

* A `Literal` is a variable or its negation.
* A `Clause` is a list of literals joined by disjunction.
* A `CNF` is a list of clauses joined by conjunction.
* `CNF.satisfiable` is the set of formulas made true by some assignment.

The variable type is arbitrary. Renaming variables injectively preserves satisfiability.
These definitions and proofs adapt the SAT module of the
[EFX formalization](https://zenodo.org/records/23734798).
-/

@[expose] public section

namespace Algolean.Problems.SAT

variable {α : Type u} {β : Type v}

/-- A literal is a variable or its negation. -/
inductive Literal (α : Type u) where
  /-- This literal has the value assigned to its variable. -/
  | pos (name : α)
  /-- This literal has the opposite of the value assigned to its variable. -/
  | neg (name : α)
deriving DecidableEq

/-- This equivalence separates positive and negative literals without changing their names. -/
def Literal.equiv : Literal α ≃ α ⊕ α where
  toFun
    | .pos name => .inl name
    | .neg name => .inr name
  invFun
    | .inl name => .pos name
    | .inr name => .neg name
  left_inv literal := by cases literal <;> rfl
  right_inv name := by cases name <;> rfl

/-- This function returns the variable named by a positive or negative literal. -/
def Literal.name : Literal α → α
  | .pos name => name
  | .neg name => name

/-- A positive literal names the variable supplied to its constructor. -/
@[simp] theorem Literal.name_pos (name : α) : (Literal.pos name).name = name := rfl

/-- A negative literal names the variable supplied to its constructor. -/
@[simp] theorem Literal.name_neg (name : α) : (Literal.neg name).name = name := rfl

/-- This function evaluates a literal using the supplied assignment of truth values. -/
def Literal.eval (literal : Literal α) (assignment : α → Bool) : Bool :=
  match literal with
  | .pos name => assignment name
  | .neg name => !(assignment name)

/-- A positive literal evaluates to the value assigned to its variable. -/
@[simp] theorem Literal.eval_pos (name : α) (assignment : α → Bool) :
    Literal.eval (.pos name) assignment = assignment name := rfl

/-- A negative literal evaluates to the opposite of the value assigned to its variable. -/
@[simp] theorem Literal.eval_neg (name : α) (assignment : α → Bool) :
    Literal.eval (.neg name) assignment = !(assignment name) := rfl

/-- Negating a literal exchanges its positive and negative forms. -/
@[simp] def Literal.not : Literal α → Literal α
  | .pos name => .neg name
  | .neg name => .pos name

/-- A literal is satisfied by an assignment when it evaluates to true. -/
def Literal.SatisfiedBy (literal : Literal α) (assignment : α → Bool) : Prop :=
  literal.eval assignment = true

/-- This set contains the literals made true by some assignment. -/
def Literal.satisfiable : Set (Literal α) :=
  {literal | ∃ assignment, literal.SatisfiedBy assignment}

/-- Every literal has a satisfying assignment. -/
theorem Literal.mem_satisfiable (literal : Literal α) : literal ∈ Literal.satisfiable := by
  cases literal with
  | pos name => exact ⟨fun _ => true, rfl⟩
  | neg name => exact ⟨fun _ => false, rfl⟩

/-- A clause is true when at least one of its literals is true. -/
abbrev Clause (α : Type u) := List (Literal α)

/-- This function evaluates a clause by taking the disjunction of its literal values. -/
def Clause.eval (clause : Clause α) (assignment : α → Bool) : Bool :=
  (clause.map (fun literal => literal.eval assignment)).or

/-- A clause is satisfied by an assignment when it evaluates to true. -/
def Clause.SatisfiedBy (clause : Clause α) (assignment : α → Bool) : Prop :=
  clause.eval assignment = true

/-- This set contains the clauses made true by some assignment. -/
def Clause.satisfiable : Set (Clause α) :=
  {clause | ∃ assignment, clause.SatisfiedBy assignment}

/-- An empty clause is false under every assignment. -/
@[simp] theorem Clause.eval_nil (assignment : α → Bool) :
    Clause.eval [] assignment = false := rfl

/-- A clause is satisfied exactly when one of its literals is satisfied by the same assignment. -/
theorem Clause.satisfiedBy_iff_exists_literal (clause : Clause α) (assignment : α → Bool) :
    clause.SatisfiedBy assignment ↔
      ∃ literal ∈ clause, literal.SatisfiedBy assignment := by
  simp [SatisfiedBy, eval, List.or, Literal.SatisfiedBy]

/-- A clause is satisfiable exactly when it contains a satisfiable literal. -/
theorem Clause.mem_satisfiable_iff_exists_literal (clause : Clause α) :
    clause ∈ Clause.satisfiable ↔ ∃ literal ∈ clause, literal ∈ Literal.satisfiable := by
  simp only [Clause.satisfiable, Set.mem_ofPred_eq, satisfiedBy_iff_exists_literal,
    Literal.satisfiable]
  grind

/-- Joining two clauses is satisfied when either clause is satisfied by the assignment. -/
@[simp] theorem Clause.satisfiedBy_append (first second : Clause α) (assignment : α → Bool) :
    (first ++ second).SatisfiedBy assignment ↔
      first.SatisfiedBy assignment ∨ second.SatisfiedBy assignment := by
  simp [Clause.SatisfiedBy, Clause.eval, List.or]

/-- A formula in conjunctive normal form is a list of clauses that must all be true. -/
abbrev CNF (α : Type u) := List (Clause α)

/-- This function evaluates a formula by taking the conjunction of its clause values. -/
def CNF.eval (formula : CNF α) (assignment : α → Bool) : Bool :=
  (formula.map (fun clause => clause.eval assignment)).and

/-- Assignments agreeing on all literal occurrences give the same value to the formula. -/
theorem CNF.eval_eq_of_agree (formula : CNF α) (first second : α → Bool)
    (h : ∀ literal ∈ formula.flatten, first literal.name = second literal.name) :
    formula.eval first = formula.eval second := by
  unfold CNF.eval
  congr 1
  apply List.map_congr_left
  intro clause hclause
  unfold Clause.eval
  congr 1
  apply List.map_congr_left
  intro literal hliteral
  have heq := h literal (List.mem_flatten.mpr ⟨clause, hclause, hliteral⟩)
  cases literal with
  | pos name => exact heq
  | neg name => exact congrArg Bool.not heq

/-- A formula is satisfied by an assignment when every clause evaluates to true. -/
def CNF.SatisfiedBy (formula : CNF α) (assignment : α → Bool) : Prop :=
  formula.eval assignment = true

/-- This set contains the formulas made true by one assignment shared by all their clauses. -/
def CNF.satisfiable : DecisionProblem (CNF α) :=
  {formula | ∃ assignment, formula.SatisfiedBy assignment}

/-- This set contains the formulas made true by every assignment. -/
def CNF.valid : Set (CNF α) := {formula | ∀ assignment, formula.SatisfiedBy assignment}

/-- An empty formula is true under every assignment. -/
@[simp] theorem CNF.eval_nil (assignment : α → Bool) : CNF.eval [] assignment = true := rfl

/-- A formula is satisfied exactly when every clause is satisfied by the same assignment. -/
theorem CNF.satisfiedBy_iff_forall_clause (formula : CNF α) (assignment : α → Bool) :
    formula.SatisfiedBy assignment ↔ ∀ clause ∈ formula, clause.SatisfiedBy assignment := by
  simp [SatisfiedBy, eval, List.and, Clause.SatisfiedBy]

/-- Joining two formulas requires both to be satisfied by the same assignment. -/
@[simp] theorem CNF.satisfiedBy_append (first second : CNF α) (assignment : α → Bool) :
    (first ++ second).SatisfiedBy assignment ↔
      first.SatisfiedBy assignment ∧ second.SatisfiedBy assignment := by
  simp [CNF.SatisfiedBy, CNF.eval, List.and]

/-- A first clause and the remaining clauses must all hold under the same assignment. -/
@[simp] theorem CNF.satisfiedBy_cons (clause : Clause α) (formula : CNF α)
    (assignment : α → Bool) :
    CNF.SatisfiedBy (clause :: formula) assignment ↔
      clause.SatisfiedBy assignment ∧ formula.SatisfiedBy assignment := by
  simp [CNF.SatisfiedBy, CNF.eval, Clause.SatisfiedBy]

/--
Joining a list of formulas requires every listed formula to use the same satisfying assignment.
-/
@[simp] theorem CNF.satisfiedBy_flatMap {ι : Type w} (entries : List ι) (formula : ι → CNF α)
    (assignment : α → Bool) :
    CNF.SatisfiedBy (entries.flatMap formula) assignment ↔
      ∀ entry ∈ entries, (formula entry).SatisfiedBy assignment := by
  simp only [satisfiedBy_iff_forall_clause, List.forall_mem_flatMap]

/-- Every clause of a satisfiable formula is satisfiable. -/
theorem CNF.clause_mem_satisfiable {formula : CNF α} (h : formula ∈ CNF.satisfiable)
    {clause : Clause α} (hmem : clause ∈ formula) : clause ∈ Clause.satisfiable := by
  obtain ⟨assignment, h⟩ := h
  exact ⟨assignment, (satisfiedBy_iff_forall_clause formula assignment).mp h clause hmem⟩

/-- These are the variables occurring in a literal. -/
@[simp] def Literal.vars : Literal α → Set α
  | .pos name => {name}
  | .neg name => {name}

/-- These are the variables occurring in at least one literal of the clause. -/
def Clause.vars (clause : Clause α) : Set α := ⋃ literal ∈ clause, literal.vars

/-- These are the variables occurring in at least one clause of the formula. -/
def CNF.vars (formula : CNF α) : Set α := ⋃ clause ∈ formula, clause.vars

/-- This function evaluates a literal using an assignment defined only on its variables. -/
def Literal.evalSet (literal : Literal α) (assignment : literal.vars → Bool) : Bool :=
  match literal with
  | .pos name => assignment ⟨name, by simp⟩
  | .neg name => !(assignment ⟨name, by simp⟩)

/-- Restricting an assignment to the literal's variables preserves its value. -/
theorem Literal.evalSet_restrict (literal : Literal α) (assignment : α → Bool) :
    literal.evalSet (fun name => assignment name.val) = literal.eval assignment := by
  cases literal <;> rfl

/-- Renaming a literal changes its variable and preserves its sign. -/
def Literal.rename (literal : Literal α) (rename : α → β) : Literal β :=
  match literal with
  | .pos name => .pos (rename name)
  | .neg name => .neg (rename name)

/-- Renaming a clause renames each of its literals in order. -/
def Clause.rename (clause : Clause α) (rename : α → β) : Clause β :=
  clause.map (fun literal => literal.rename rename)

/-- Renaming a formula renames each of its clauses in order. -/
def CNF.rename (formula : CNF α) (rename : α → β) : CNF β :=
  formula.map (fun clause => clause.rename rename)

/-- Evaluating a renamed literal uses the target assignment at each renamed variable. -/
@[simp] theorem Literal.eval_rename (literal : Literal α) (rename : α → β)
    (assignment : β → Bool) :
    (literal.rename rename).eval assignment = literal.eval (assignment ∘ rename) := by
  cases literal <;> rfl

/-- Evaluating a renamed clause uses the target assignment at each renamed variable. -/
@[simp] theorem Clause.eval_rename (clause : Clause α) (rename : α → β)
    (assignment : β → Bool) :
    (clause.rename rename).eval assignment = clause.eval (assignment ∘ rename) := by
  simp only [Clause.rename, Clause.eval, List.map_map, Function.comp_def, Literal.eval_rename]

/-- Evaluating a renamed formula uses the target assignment at each renamed variable. -/
@[simp] theorem CNF.eval_rename (formula : CNF α) (rename : α → β)
    (assignment : β → Bool) :
    (formula.rename rename).eval assignment = formula.eval (assignment ∘ rename) := by
  simp only [CNF.rename, CNF.eval, List.map_map, Function.comp_def, Clause.eval_rename]

/-- Renaming variables injectively preserves satisfiability, including for empty variable types. -/
theorem CNF.rename_mem_satisfiable_iff (formula : CNF α) (rename : α → β)
    (hinj : Function.Injective rename) :
    formula.rename rename ∈ CNF.satisfiable ↔ formula ∈ CNF.satisfiable := by
  classical
  constructor
  · rintro ⟨assignment, h⟩
    exact ⟨assignment ∘ rename, by simpa [SatisfiedBy] using h⟩
  · rintro ⟨assignment, h⟩
    refine ⟨Function.extend rename assignment (fun _ => false), ?_⟩
    simpa [SatisfiedBy, Function.extend_comp hinj] using h

end Algolean.Problems.SAT
