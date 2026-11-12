/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Basic
public import Algolean.Problems.SAT.Constraints

/-!
# Boolean variables for a bounded computation

The formula describes the tape at times zero through the time bound. A row is the list of tape
cells at one such time, together with the head position and machine state.

* A tape variable says which symbol is in one cell at one time.
* A head variable says where the head is and which state the machine is in at that time.
* A certificate variable chooses one symbol at one place in the certificate.
* The choice clauses require exactly one value for each of these choices.

The construction lists individual cells, symbols, and states. It never lists whole possible
rows or computations. In particular, the number of choices does not grow exponentially with
the tape width.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Computation

open Problems.SAT

variable {Γ : Type}

/-- These Boolean variables describe a single symbol choice or a head position and state. -/
inductive Variable (problem : BoundedVerification Γ) where
  /-- This chooses the symbol at one position in the certificate. -/
  | certificate (position : Fin problem.certificateLength) (symbol : Γ)
  /-- This cell has the specified symbol at the given time. -/
  | tape (time : Fin (problem.time + 1)) (position : Fin (width problem))
      (symbol : Option (TapeSymbol Γ))
  /-- The head has the specified position and state at the given time. -/
  | head (time : Fin (problem.time + 1))
      (control : Fin (width problem) × Option (Fin (problem.verifier.states + 1)))
deriving DecidableEq

/-- These are all possible states, including the halted state. -/
@[expose] def stateChoices (problem : BoundedVerification Γ) :
    List (Option (Fin (problem.verifier.states + 1))) :=
  none :: (List.finRange (problem.verifier.states + 1)).map some

/-- These are all possible combinations of head position and machine state. -/
@[expose] def controlChoices (problem : BoundedVerification Γ) :
    List (Fin (width problem) × Option (Fin (problem.verifier.states + 1))) :=
  (List.finRange (width problem)).flatMap fun position =>
    (stateChoices problem).map fun state => (position, state)

/-- Every state, including the halted state, occurs among the choices. -/
@[simp] private theorem mem_stateChoices (problem : BoundedVerification Γ)
    (state : Option (Fin (problem.verifier.states + 1))) : state ∈ stateChoices problem := by
  cases state <;> simp [stateChoices]

/-- Every possible head position and state occurs among the choices. -/
@[simp] theorem mem_controlChoices (problem : BoundedVerification Γ)
    (control : Fin (width problem) × Option (Fin (problem.verifier.states + 1))) :
    control ∈ controlChoices problem := by simp [controlChoices]

/-- There is one head-position choice for each state, including halt, at every tape position. -/
@[simp] theorem length_controlChoices (problem : BoundedVerification Γ) :
    (controlChoices problem).length = width problem * (problem.verifier.states + 2) := by
  simp [controlChoices, stateChoices, List.length_flatMap, Nat.mul_comm]

variable [Fintype Γ] [DecidableEq Γ] {problem : BoundedVerification Γ}

/-- These clauses choose exactly one alphabet symbol at each position in the certificate. -/
@[expose] noncomputable def certificateClauses (problem : BoundedVerification Γ) :
    CNF (Variable problem) :=
  (List.finRange problem.certificateLength).flatMap fun position =>
    CNF.exactlyOne ((Finset.univ : Finset Γ).toList.map (Variable.certificate position))

/-- These clauses choose exactly one symbol in every recorded tape cell at every time. -/
@[expose] noncomputable def tapeClauses (problem : BoundedVerification Γ) :
    CNF (Variable problem) :=
  (List.finRange (problem.time + 1)).flatMap fun time =>
    (List.finRange (width problem)).flatMap fun position =>
      CNF.exactlyOne ((Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map
        (Variable.tape time position))

/-- These clauses choose one head position and state at every recorded time. -/
@[expose] def headClauses (problem : BoundedVerification Γ) : CNF (Variable problem) :=
  (List.finRange (problem.time + 1)).flatMap fun time =>
    CNF.exactlyOne ((controlChoices problem).map (Variable.head time))

/--
These clauses require one head position and state per row, and exactly one symbol per cell.
The existing SAT construction for exactly one choice is used for each of these requirements.
-/
@[expose] noncomputable def choiceClauses (problem : BoundedVerification Γ) :
    CNF (Variable problem) :=
  certificateClauses problem ++
  (headClauses problem ++ tapeClauses problem)

/-- This assignment records precisely the state, head position, and cells of each row. -/
@[expose] def rowAssignment (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    Variable problem → Bool
  | .certificate position symbol => decide (certificate.val[position.val] = symbol)
  | .tape time position symbol => decide ((rows time).cells[position.val]'(by simp) = symbol)
  | .head time control => decide (((rows time).headIndex, (rows time).state) = control)

private theorem choices_iff
    (problem : BoundedVerification Γ) (assignment : Variable problem → Bool) :
    (choiceClauses problem).SatisfiedBy assignment ↔
      (∀ position, ∃! symbol, assignment (.certificate position symbol) = true) ∧
      ((∀ time, ∃! control, assignment (.head time control) = true) ∧
      (∀ time position, ∃! symbol, assignment (.tape time position symbol) = true)) := by
  simp only [choiceClauses, certificateClauses, headClauses, tapeClauses,
    CNF.satisfiedBy_append, CNF.satisfiedBy_flatMap,
    List.mem_finRange, forall_const]
  apply and_congr
  · apply forall_congr'
    intro position
    exact CNF.exactlyOne_map_satisfiedBy _ (by simp) _
      (by intro first second h; cases h; rfl) _
  · apply and_congr
    · apply forall_congr'
      intro time
      exact CNF.exactlyOne_map_satisfiedBy _ (mem_controlChoices problem) _
        (by intro first second h; cases h; rfl) _
    · apply forall_congr'
      intro time
      apply forall_congr'
      intro position
      exact CNF.exactlyOne_map_satisfiedBy _ (by simp) _
        (by intro first second h; cases h; rfl) _

private theorem unique_bool {α : Type} [DecidableEq α] (f : α → Bool)
    (h : ∃! value, f value = true) (value : α) :
    f value = decide (Classical.choose h = value) := by
  have hc := Classical.choose_spec h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact ⟨fun hv => (hc.2 value hv).symm, fun heq => heq ▸ hc.1⟩

/-- The choices made by any sequence of rows satisfy all the choice clauses. -/
theorem choiceClauses_rowAssignment
    (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    (choiceClauses problem).SatisfiedBy (rowAssignment certificate rows) := by
  rw [choices_iff]
  constructor
  · intro position
    refine ⟨certificate.val[position.val], by simp [rowAssignment], ?_⟩
    intro symbol h
    simp only [rowAssignment, decide_eq_true_eq] at h
    exact h.symm
  · constructor
    · intro time
      refine ⟨((rows time).headIndex, (rows time).state), by simp [rowAssignment], ?_⟩
      intro control h
      simp only [rowAssignment, decide_eq_true_eq] at h
      exact h.symm
    · intro time position
      refine ⟨(rows time).cells[position.val]'(by simp), by simp [rowAssignment], ?_⟩
      intro symbol h
      simp only [rowAssignment, decide_eq_true_eq] at h
      exact h.symm

/--
An assignment satisfies the choice clauses exactly when it records a sequence of rows. This
recovers symbols and head positions from Boolean choices without enumerating possible rows.
-/
theorem choiceClauses_iff_exists_rows (problem : BoundedVerification Γ)
    (assignment : Variable problem → Bool) :
    (choiceClauses problem).SatisfiedBy assignment ↔
      ∃ certificate rows, assignment = rowAssignment certificate rows := by
  constructor
  · intro h
    obtain ⟨hcertificate, hhead, htape⟩ := (choices_iff problem assignment).mp h
    let certificate : List.Vector Γ problem.certificateLength :=
      ⟨List.ofFn fun position => Classical.choose (hcertificate position), by simp⟩
    let control := fun time => Classical.choose (hhead time)
    let symbol := fun time position => Classical.choose (htape time position)
    let rows : Fin (problem.time + 1) → Row problem.verifier (width problem) :=
      fun time => Row.ofCells (control time).2
      ⟨List.ofFn (symbol time), by simp⟩ (control time).1
    refine ⟨certificate, rows, ?_⟩
    funext entry
    cases entry with
    | certificate position value =>
      simpa only [rowAssignment, certificate, List.getElem_ofFn] using
        unique_bool _ (hcertificate position) value
    | tape time position value =>
      have hcells : (rows time).cells = List.ofFn (symbol time) := Row.cells_ofCells _ _ _
      simpa only [rowAssignment, hcells, List.getElem_ofFn] using
        unique_bool _ (htape time position) value
    | head time value =>
      have hh : (rows time).headIndex = (control time).1 := Row.headIndex_ofCells _ _ _
      have hs : (rows time).state = (control time).2 := rfl
      simpa only [rowAssignment, hh, hs] using
        unique_bool (fun value => assignment (.head time value)) (hhead time) value
  · rintro ⟨certificate, rows, rfl⟩
    exact choiceClauses_rowAssignment certificate rows

/--
The number of choice clauses is quadratic in the largest list of possible choices. There is
one such list per certificate symbol, per row's head and state, and per tape cell at each time.
The second bound counts the literals in a single clause.
-/
theorem choiceClauses_bounds (problem : BoundedVerification Γ) :
    let choices := Fintype.card Γ + 2 + width problem * (problem.verifier.states + 2)
    (choiceClauses problem).length ≤
      (problem.certificateLength + (problem.time + 1) * (width problem + 1)) *
        (choices ^ 2 + 1) ∧
      ∀ clause ∈ choiceClauses problem, clause.length ≤ choices + 2 := by
  let choices := Fintype.card Γ + 2 + width problem * (problem.verifier.states + 2)
  let limit := choices ^ 2 + 1
  have hlength (names : List (Variable problem)) (h : names.length ≤ choices) :
      (CNF.exactlyOne names).length ≤ limit :=
    (CNF.length_exactlyOne_le names).trans
      (Nat.add_le_add_right (Nat.pow_le_pow_left h 2) 1)
  have hclause (names : List (Variable problem)) (h : names.length ≤ choices) :
      ∀ clause ∈ CNF.exactlyOne names, clause.length ≤ choices + 2 :=
    fun clause hc => (CNF.clause_length_exactlyOne_le names clause hc).trans
      (Nat.add_le_add_right h 2)
  have hflat {ι : Type} (items : List ι) (block : ι → CNF (Variable problem)) (bound : Nat)
      (h : ∀ item ∈ items, (block item).length ≤ bound) :
      (items.flatMap block).length ≤ items.length * bound := by
    simpa [List.length_flatMap] using List.sum_le_sum h
  have hcert (position : Fin problem.certificateLength) :
      ((Finset.univ : Finset Γ).toList.map
        (Variable.certificate (problem := problem) position)).length ≤ choices := by
    simp only [List.length_map, Finset.length_toList, Finset.card_univ]
    dsimp [choices]
    lia
  have hhead (time : Fin (problem.time + 1)) :
      ((controlChoices problem).map (Variable.head time)).length ≤ choices := by
    simp [choices]
  have htape (time : Fin (problem.time + 1)) (position : Fin (width problem)) :
      ((Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map
        (Variable.tape time position)).length ≤ choices := by
    simp [choices, TapeSymbol, Alphabet.Extended]
  constructor
  · have hc := hflat (List.finRange problem.certificateLength)
      (fun position => CNF.exactlyOne ((Finset.univ : Finset Γ).toList.map
        (Variable.certificate position))) limit (fun position _ => hlength _ (hcert position))
    have hh := hflat (List.finRange (problem.time + 1))
      (fun time => CNF.exactlyOne ((controlChoices problem).map (Variable.head time))) limit
        (fun time _ => hlength _ (hhead time))
    have ht := hflat (List.finRange (problem.time + 1))
      (fun time => (List.finRange (width problem)).flatMap fun position =>
        CNF.exactlyOne ((Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map
          (Variable.tape time position))) (width problem * limit) (by
            intro time _
            simpa only [List.length_finRange] using
              hflat (List.finRange (width problem)) _ limit
                (fun position _ => hlength _ (htape time position)))
    simp only [List.length_finRange] at hc hh ht
    simp only [choiceClauses, certificateClauses, headClauses, tapeClauses, List.length_append]
    change _ ≤ (problem.certificateLength + (problem.time + 1) * (width problem + 1)) * limit
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_assoc]
      at hc hh ht ⊢
    lia
  · simp only [choiceClauses, certificateClauses, headClauses, tapeClauses,
    List.forall_mem_append, List.forall_mem_flatMap]
    exact ⟨fun position _ => hclause _ (hcert position),
      fun time _ => hclause _ (hhead time),
      fun time _ position _ => hclause _ (htape time position)⟩

end Algolean.Algorithms.NPToSAT.Computation
