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

/-!
# A SAT formula for a bounded verifier computation

The clauses describe the initial tape, each transition, and a clean accepting output.
Their satisfying assignments correspond exactly to accepting computations with the stated
certificate and time bounds. Variable names use the existing binary SAT representation.
-/

public section

namespace Algolean.Algorithms.NPToTMSAT

open Computability Problems Problems.SAT Problems.TMSAT

variable {Γ : Type}

namespace Formula

section Indexed

variable [Fintype Γ] [DecidableEq Γ]

/-- These clauses require a halted head over the accepting symbol and blanks everywhere else. -/
@[expose] def finalClauses (problem : Instance Γ) (yes : Γ) : CNF (Variable problem) :=
  Clause.atLeastOne ((List.finRange (width problem)).map fun position =>
    Variable.head (Fin.last problem.time) (position, none)) ::
  (List.finRange (width problem)).flatMap fun position =>
    [Clause.implies [.head (Fin.last problem.time) (position, none)]
       (.tape (Fin.last problem.time) position (some (.inl yes))),
     Clause.atLeastOne [.head (Fin.last problem.time) (position, none),
       .tape (Fin.last problem.time) position none]]

omit [Fintype Γ] in
private theorem finalClauses_iff (problem : Instance Γ) (yes : Γ)
    (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    (finalClauses problem yes).SatisfiedBy (rowAssignment certificate rows) ↔
      (rows (Fin.last problem.time)).Accepting yes := by
  simp only [finalClauses, CNF.satisfiedBy_iff_forall_clause, List.forall_mem_cons,
    List.forall_mem_flatMap]
  simp [rowAssignment, Prod.mk.injEq, Row.Accepting, and_imp]
  grind [Row.cells_headIndex]

/-- This joins the clauses for the certificate, initial tape, transitions, and final acceptance. -/
@[expose] noncomputable def indexedFormula (problem : Instance Γ) (yes : Γ) :
    CNF (Variable problem) :=
  choiceClauses problem ++ (initialClauses problem ++
    (stepClauses problem ++ finalClauses problem yes))

/-- The clauses describe an accepting computation exactly when the TMSAT instance is satisfiable. -/
theorem indexedFormula_satisfiable_iff (problem : Instance Γ) (yes : Γ) :
    indexedFormula problem yes ∈ CNF.satisfiable ↔ problem ∈ satisfiable yes := by
  rw [mem_satisfiable_iff_exists_computation]
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

/--
This constructs a CNF formula whose satisfying assignments describe an accepting computation
of the given TMSAT instance. It uses binary names with separate fields for each variable's indices.
The numbering of the alphabet is fixed once and does not depend on the instance or on the
accepting certificate.
-/
@[expose] noncomputable def formula (problem : Instance Γ) (yes : Γ) : CNF SAT.Variable := by
  classical
  letI : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact (indexedFormula problem yes).rename Variable.name

end Algolean.Algorithms.NPToTMSAT

namespace Algolean.Algorithms.NPToTMSAT

open Computability Problems Problems.SAT Problems.TMSAT Formula

variable {Γ : Type} [Fintype Γ]

/-- The constructed formula is satisfiable exactly when the machine instance is satisfiable. -/
theorem formula_satisfiable_iff (problem : Instance Γ) (yes : Γ) :
    formula problem yes ∈ CNF.satisfiable ↔ problem ∈ satisfiable yes := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact (CNF.rename_mem_satisfiable_iff _ _ Variable.name_injective).trans
    (indexedFormula_satisfiable_iff problem yes)

end Algolean.Algorithms.NPToTMSAT
