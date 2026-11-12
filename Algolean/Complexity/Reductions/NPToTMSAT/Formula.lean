/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Initial
public import Algolean.Complexity.Reductions.NPToTMSAT.TransitionClauses
public import Algolean.Complexity.Reductions.NPToTMSAT.VariableNames
public import Algolean.Problems.Encodings.SAT
public import Mathlib.Logic.Equiv.List

/-!
# A SAT formula for a bounded verifier computation

The clauses describe the initial tape, each transition, and a clean accepting output.
Their satisfying assignments correspond exactly to accepting computations with the stated
certificate and time bounds. Variable names use the existing binary SAT representation.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

attribute [local instance 100] Fintype.toEncodable

namespace Algolean.Algorithms.NPToTMSAT

open Computability Problems Problems.SAT

variable {Γ : Type}

namespace Formula

section Indexed

variable [Fintype Γ] [DecidableEq Γ]

/-- These clauses require a halted head over the accepting symbol and blanks everywhere else. -/
@[expose] def finalClauses (problem : BoundedVerification Γ) (yes : Γ) : CNF (Variable problem) :=
  Clause.atLeastOne ((List.finRange (width problem)).map fun position =>
    Variable.head (Fin.last problem.time) (position, none)) ::
  (List.finRange (width problem)).flatMap fun position =>
    [Clause.implies [.head (Fin.last problem.time) (position, none)]
       (.tape (Fin.last problem.time) position (some (.inl yes))),
     Clause.atLeastOne [.head (Fin.last problem.time) (position, none),
       .tape (Fin.last problem.time) position none]]

omit [Fintype Γ] in
private theorem finalClauses_iff (problem : BoundedVerification Γ) (yes : Γ)
    (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    (finalClauses problem yes).SatisfiedBy (rowAssignment certificate rows) ↔
      (rows (Fin.last problem.time)).Accepting yes := by
  simp only [finalClauses, CNF.satisfiedBy_iff_forall_clause, List.forall_mem_cons,
    List.forall_mem_flatMap]
  simp [rowAssignment, Prod.mk.injEq, Row.Accepting, and_imp]
  grind [Row.cells_headIndex]

/-- This joins the clauses for the certificate, initial tape, transitions, and final acceptance. -/
@[expose] noncomputable def indexedFormula (problem : BoundedVerification Γ) (yes : Γ) :
    CNF (Variable problem) :=
  choiceClauses problem ++ (initialClauses problem ++
    (stepClauses problem ++ finalClauses problem yes))

/--
The clauses describe an accepting computation exactly when the verifier accepts a certificate
within its bounds.
-/
theorem indexedFormula_satisfiable_iff (problem : BoundedVerification Γ) (yes : Γ) :
    indexedFormula problem yes ∈ CNF.satisfiable ↔ problem ∈ accepted yes := by
  rw [mem_accepted_iff_exists_computation]
  constructor
  · rintro ⟨assignment, hformula⟩
    have hparts : (choiceClauses problem).SatisfiedBy assignment ∧
        (initialClauses problem).SatisfiedBy assignment ∧
        (stepClauses problem).SatisfiedBy assignment ∧
        (finalClauses problem yes).SatisfiedBy assignment := by
      simpa only [indexedFormula, CNF.satisfiedBy_append] using hformula
    obtain ⟨certificate, rows, rfl⟩ :=
      (choiceClauses_iff_exists_rows problem assignment).mp hparts.1
    let computation : Computation problem := {
      certificate := certificate
      rows := rows
      initial := (initialClauses_iff problem certificate rows).mp hparts.2.1
      next := (stepClauses_iff problem certificate rows).mp hparts.2.2.1 }
    exact ⟨computation, (finalClauses_iff problem yes certificate rows).mp hparts.2.2.2⟩
  · rintro ⟨computation, haccept⟩
    refine ⟨rowAssignment computation.certificate computation.rows, ?_⟩
    simp only [indexedFormula, CNF.satisfiedBy_append]
    exact ⟨choiceClauses_rowAssignment _ _,
      (initialClauses_iff _ _ _).mpr computation.initial,
      (stepClauses_iff _ _ _).mpr computation.next,
      (finalClauses_iff _ _ _ _).mpr haccept⟩

end Indexed

end Formula

open Formula

variable [Fintype Γ]

open Classical in
/--
This constructs a CNF formula whose satisfying assignments describe an accepting computation
of the given bounded verification. Its binary variable names record their indices separately.
The numbering of the alphabet is fixed once for all inputs and certificates.
-/
@[expose] noncomputable def formula (problem : BoundedVerification Γ) (yes : Γ) :
    CNF SAT.Variable :=
  (indexedFormula problem yes).rename Variable.name

end Algolean.Algorithms.NPToTMSAT

namespace Algolean.Algorithms.NPToTMSAT

open Computability Problems Problems.SAT Formula

variable {Γ : Type} [Fintype Γ]

/-- The formula is satisfiable exactly when the verifier accepts a certificate within its bounds. -/
theorem formula_satisfiable_iff (problem : BoundedVerification Γ) (yes : Γ) :
    formula problem yes ∈ CNF.satisfiable ↔ problem ∈ accepted yes := by
  classical
  exact (CNF.rename_mem_satisfiable_iff _ _ Variable.name_injective).trans
    (indexedFormula_satisfiable_iff problem yes)

end Algolean.Algorithms.NPToTMSAT
