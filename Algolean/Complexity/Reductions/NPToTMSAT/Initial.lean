/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Variables

/-!
# Clauses for the initial input and certificate

The verifier starts with the input word on its tape, followed by one separating symbol and
the certificate. All other cells are blank. We describe the cells from `-t` through
`input.length + certificateLength + t`, where `t` is the allowed number of transitions.

These clauses require the first row of the computation to describe that initial tape. They
also put the head over the start of the input and set the verifier's initial state. The
certificate symbols are chosen by the Boolean assignment, one symbol for each certificate cell.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToTMSAT

open Problems.SAT Alphabet

variable {Γ : Type}

/--
This identifies what belongs in one cell of the initial tape. It returns either the fixed
symbol for that cell or the index of the certificate symbol stored there. Cell zero in this
finite list is tape position `-t`, so the input starts at cell `t`.
-/
@[expose] def initialSource (problem : BoundedVerification Γ) (position : Fin (width problem)) :
    Option (TapeSymbol Γ) ⊕ Fin problem.certificateLength :=
  if hleft : position.val < problem.time then .inl none
  else if hinput : position.val < problem.time + problem.input.length then
    .inl (some (.inl (problem.input[position.val - problem.time]'(by lia))))
  else if hseparator : position.val = problem.time + problem.input.length then .inl (some (.inr 0))
  else if hcertificate : position.val <
      problem.time + problem.input.length + 1 + problem.certificateLength then
    .inr ⟨position.val - (problem.time + problem.input.length + 1), by lia⟩
  else .inl none

private theorem initialSource_cell (problem : BoundedVerification Γ)
    (certificate : List.Vector Γ problem.certificateLength) (position : Fin (width problem)) :
    (initialRow problem certificate).cells[position.val]'(by simp) =
      match initialSource problem position with
      | .inl symbol => symbol
      | .inr index => some (.inl certificate.val[index.val]) := by
  simp only [cells_initialRow]
  simp only [wordPair_encode, List.map_append, List.map_cons, List.map_map]
  unfold initialSource
  split_ifs with hleft hinput hseparator hcertificate
  · simp [hleft]
  · have hlt : position.val - problem.time < problem.input.length := by lia
    simp [List.getElem_append, hleft, hlt]
  · simp_all
  · have hnot : ¬position.val - problem.time < problem.input.length := by lia
    have hskip : position.val - problem.time - problem.input.length =
        position.val - (problem.time + problem.input.length + 1) + 1 := by lia
    have hhigh : position.val - (problem.time + problem.input.length + 1) <
        problem.certificateLength := by lia
    simp [List.getElem_append, hleft, hnot, hskip, hhigh]
  · have hnot : ¬position.val - problem.time < problem.input.length := by lia
    have hskip : position.val - problem.time - problem.input.length =
        position.val - (problem.time + problem.input.length + 1) + 1 := by lia
    have hhigh : ¬position.val - (problem.time + problem.input.length + 1) <
        problem.certificateLength := by lia
    simp [List.getElem_append, hleft, hnot, hskip, hhigh]

variable [Fintype Γ] [DecidableEq Γ]

/--
These clauses require the first row to put the input and its certificate on the tape, with
one separating symbol between them and blanks elsewhere. They also set the initial head and
state. A Boolean variable chooses each certificate symbol; an implication puts that same
symbol in the corresponding tape cell.
-/
noncomputable def initialClauses (problem : BoundedVerification Γ) : CNF (Variable problem) :=
  [[.pos (.head 0 (⟨problem.time, by dsimp [width]; lia⟩, some problem.verifier.initial))]] ++
    (List.finRange (width problem)).flatMap fun position =>
      match initialSource problem position with
      | .inl symbol => [[.pos (.tape 0 position symbol)]]
      | .inr index => (Finset.univ : Finset Γ).toList.map fun symbol =>
          Clause.implies [.certificate index symbol] (.tape 0 position (some (.inl symbol)))

omit [DecidableEq Γ] in
/-- The initial formula consists of its head requirement followed by the cell requirements. -/
theorem initialClauses_eq (problem : BoundedVerification Γ) :
    initialClauses problem =
      [[.pos (.head 0 (⟨problem.time, by dsimp [width]; lia⟩,
        some problem.verifier.initial))]] ++
        (List.finRange (width problem)).flatMap fun position =>
          match initialSource problem position with
          | .inl symbol => [[.pos (.tape 0 position symbol)]]
          | .inr index => (Finset.univ : Finset Γ).toList.map fun symbol =>
              Clause.implies [.certificate index symbol]
                (.tape 0 position (some (.inl symbol))) := by
  rfl

omit [DecidableEq Γ] in
private theorem initialClauses_satisfied (problem : BoundedVerification Γ)
    (assignment : Variable problem → Bool) :
    (initialClauses problem).SatisfiedBy assignment ↔
      assignment (.head 0 (⟨problem.time, by dsimp [width]; lia⟩,
        some problem.verifier.initial)) = true ∧
      ∀ position, match initialSource problem position with
        | .inl symbol => assignment (.tape 0 position symbol) = true
        | .inr index => ∀ symbol, assignment (.certificate index symbol) = true →
            assignment (.tape 0 position (some (.inl symbol))) = true := by
  simp only [initialClauses, CNF.satisfiedBy_append, CNF.satisfiedBy_flatMap,
    List.mem_finRange, forall_const]
  apply and_congr
  · simp [CNF.SatisfiedBy, CNF.eval, Clause.eval]
  · apply forall_congr'
    intro position
    split
    · simp [CNF.SatisfiedBy, CNF.eval, Clause.eval]
    · simp only [CNF.satisfiedBy_iff_forall_clause, List.forall_mem_map]
      simp

/--
For the assignment describing a certificate and sequence of rows, these clauses hold exactly
when the first row is the verifier's actual initial tape and state for that certificate.
-/
theorem initialClauses_iff (problem : BoundedVerification Γ)
    (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    (initialClauses problem).SatisfiedBy (rowAssignment certificate rows) ↔
      rows 0 = initialRow problem certificate := by
  rw [initialClauses_satisfied]
  have hcells (position : Fin (width problem)) :
      (match initialSource problem position with
        | .inl symbol => rowAssignment certificate rows (.tape 0 position symbol) = true
        | .inr index => ∀ symbol, rowAssignment certificate rows (.certificate index symbol) =
            true → rowAssignment certificate rows (.tape 0 position (some (.inl symbol))) = true) ↔
        (rows 0).cells[position.val]'(by simp) =
          (initialRow problem certificate).cells[position.val]'(by simp) := by
    simp only [initialSource_cell]
    split <;> simp [rowAssignment]
  simp_rw [hcells]
  simp only [rowAssignment, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hhead, hstate⟩, htape⟩
    apply Row.eq_of_cells
    · exact hstate
    · simpa only [initialRow, Row.headIndex, List.length_replicate] using hhead
    · apply List.ext_getElem
      · simp
      · intro i hi hj
        exact htape ⟨i, by simpa using hi⟩
  · intro h
    rw [h]
    constructor
    · simp [initialRow, Row.headIndex]
    · intro position
      rfl

omit [DecidableEq Γ] in
/--
The initial-tape clauses number at most one plus the tape width times the alphabet size plus
one. Every such clause contains at most two literals: a fixed symbol, or an implication from
a certificate choice to its tape cell.
-/
theorem initialClauses_bounds (problem : BoundedVerification Γ) :
    (initialClauses problem).length ≤ 1 + width problem * (Fintype.card Γ + 1) ∧
      ∀ clause ∈ initialClauses problem, clause.length ≤ 2 := by
  constructor
  · simp only [initialClauses, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap]
    have h := List.sum_le_length_nsmul
      ((List.finRange (width problem)).map fun position =>
        (match initialSource problem position with
        | .inl symbol => [[Literal.pos (Variable.tape 0 position symbol)]]
        | .inr index => (Finset.univ : Finset Γ).toList.map fun symbol =>
            Clause.implies [.certificate index symbol]
              (.tape 0 position (some (.inl symbol)))).length)
      (Fintype.card Γ + 1) (by
        intro n hn
        obtain ⟨position, _, rfl⟩ := List.mem_map.mp hn
        split <;> simp)
    simpa [nsmul_eq_mul] using Nat.add_le_add_left h 1
  · simp only [initialClauses, List.forall_mem_append, List.forall_mem_flatMap]
    constructor
    · simp
    · intro position _
      split
      · simp
      · simp only [List.forall_mem_map, Clause.length_implies, List.length_cons, List.length_nil]
        simp

end Algolean.Algorithms.NPToTMSAT
