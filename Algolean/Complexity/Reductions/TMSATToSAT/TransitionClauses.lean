/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Variables

/-!
# Clauses for consecutive verifier configurations

The Boolean variables describe the tape, head, and state before and after each transition.
These clauses require the verifier to write the symbol specified by its table and to choose
its specified next state and head position. Every cell other than the one being written keeps
its old symbol. After the machine halts, later rows keep the same state, head, and tape.

The correctness theorem connects these clauses to the existing finite-row execution. The
supporting descriptions of head movement and table entries are private to this module.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT

open Cslib.Turing Problems.TMSAT

variable {Γ : Type}

/--
This reads the verifier's table for a running state. For a halted state it keeps the scanned
symbol and stays halted without moving, so later rows repeat the halted configuration.
-/
private def instruction (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (state : Option (Fin (verifier.states + 1))) (symbol : Option (TapeSymbol Γ)) :
    SingleTapeTM.Transition (TapeSymbol Γ) verifier.states :=
  match state with
  | none => (symbol, none, none)
  | some state => verifier.transition state symbol

/-- This requires the next numbered head position to follow the specified movement. -/
private def Moved {width : Nat}
    (first : Fin width) (movement : Option Bool) (second : Fin width) : Prop :=
  match movement with
  | none => second = first
  | some false => second.val + 1 = first.val
  | some true => second.val = first.val + 1

private instance {width : Nat} (first : Fin width) (movement : Option Bool) (second : Fin width) :
    Decidable (Moved first movement second) := by unfold Moved; split <;> infer_instance

/-- This checks the next state and head position selected by one table entry. -/
private def controlAllowed (problem : Instance Γ)
    (first : Fin (width problem) × Option (Fin (problem.verifier.states + 1)))
    (symbol : Option (TapeSymbol Γ))
    (second : Fin (width problem) × Option (Fin (problem.verifier.states + 1))) : Prop :=
  let action := instruction problem.verifier first.2 symbol
  second.2 = action.2.2 ∧ Moved first.1 action.2.1 second.1

private instance (problem : Instance Γ)
    (first : Fin (width problem) × Option (Fin (problem.verifier.states + 1)))
    (symbol : Option (TapeSymbol Γ))
    (second : Fin (width problem) × Option (Fin (problem.verifier.states + 1))) :
    Decidable (controlAllowed problem first symbol second) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace Row

variable {verifier : SingleTapeTM.Description (TapeSymbol Γ)} {width : Nat}

private theorem step_fields {first second : Row verifier width} (h : first.step = some second) :
    let action := instruction verifier first.state first.symbol
    second.state = action.2.2 ∧ Moved first.headIndex action.2.1 second.headIndex ∧
      second.cells = first.cells.set first.headIndex.val action.1 := by
  cases hs : first.state with
  | none =>
    have heq : first = second := by simpa [step, hs] using h
    subst second
    simp [instruction, hs, Moved, cells, headIndex]
  | some state =>
    generalize ht : verifier.transition state first.symbol = action
    obtain ⟨written, movement, next⟩ := action
    cases movement with
    | none =>
      simp only [step, hs, ht] at h
      cases Option.some.inj h
      simp [instruction, ht, Moved, cells, headIndex]
    | some direction =>
      cases direction <;> simp only [step, hs, ht] at h <;> split at h
      all_goals try contradiction
      all_goals cases Option.some.inj h
      all_goals
        simp_all [instruction, Moved, cells, headIndex, List.reverse_cons, List.append_assoc]

/--
One row follows another exactly when the table gives its next state and head position, and
its list of cells is the old list with the scanned cell replaced by the written symbol.
No next position is available for a movement beyond the recorded interval.
-/
private theorem step_iff (first second : Row verifier width) :
    first.step = some second ↔
      let action := instruction verifier first.state first.symbol
      second.state = action.2.2 ∧ Moved first.headIndex action.2.1 second.headIndex ∧
        second.cells = first.cells.set first.headIndex.val action.1 := by
  constructor
  · exact step_fields
  · rintro ⟨hstate, hhead, hcells⟩
    have hexists : ∃ actual, first.step = some actual := by
      cases hs : first.state with
      | none => exact ⟨first, by simp [step, hs]⟩
      | some state =>
        generalize ht : verifier.transition state first.symbol = action
        obtain ⟨written, movement, next⟩ := action
        cases movement with
        | none => simp [step, hs, ht]
        | some direction =>
          have hlen := first.length_eq
          have hbound := second.headIndex.isLt
          cases direction <;> simp only [step, hs, ht] <;> split
          all_goals first
            | exact ⟨_, rfl⟩
            | simp_all [instruction, Moved, headIndex]
    obtain ⟨actual, hactual⟩ := hexists
    obtain ⟨haState, haHead, haCells⟩ := step_fields hactual
    have heq : actual = second := eq_of_cells (haState.trans hstate.symm) (by
      cases hm : (instruction verifier first.state first.symbol).2.1 with
      | none =>
        simp only [Moved, hm] at haHead hhead
        exact haHead.trans hhead.symm
      | some direction =>
        apply Fin.ext
        cases direction <;> simp only [Moved, hm] at haHead hhead <;>
          lia) (haCells.trans hcells.symm)
    simpa only [heq] using hactual

end Row

end Algolean.Algorithms.TMSATToSAT

namespace Algolean.Algorithms.TMSATToSAT

open Problems.SAT Problems.TMSAT

variable {Γ : Type} [Fintype Γ]

private noncomputable def writeClauses (problem : Instance Γ) : CNF (Variable problem) :=
  (List.finRange problem.time).flatMap fun time =>
    (controlChoices problem).flatMap fun control =>
      (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map fun symbol =>
        Clause.implies [.head time.castSucc control, .tape time.castSucc control.1 symbol]
          (.tape time.succ control.1 (instruction problem.verifier control.2 symbol).1)

private noncomputable def controlClauses (problem : Instance Γ) : CNF (Variable problem) :=
  (List.finRange problem.time).flatMap fun time =>
    (controlChoices problem).flatMap fun first =>
      (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.flatMap fun symbol =>
        ((controlChoices problem).filter fun second =>
          ¬controlAllowed problem first symbol second).map fun second =>
            Clause.forbid [.head time.castSucc first, .tape time.castSucc first.1 symbol,
              .head time.succ second]

private noncomputable def unchangedClauses (problem : Instance Γ) : CNF (Variable problem) :=
  (List.finRange problem.time).flatMap fun time =>
    (controlChoices problem).flatMap fun control =>
      ((List.finRange (width problem)).filter fun position => position ≠ control.1).flatMap
        fun position => (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map fun symbol =>
          Clause.implies [.head time.castSucc control, .tape time.castSucc position symbol]
            (.tape time.succ position symbol)

/--
These clauses require the row at time `r + 1` to follow from the row at time `r` according to
the verifier's transition table. They check the symbol written, the next head and state, and
the preservation of every other tape cell.
-/
noncomputable def stepClauses (problem : Instance Γ) : CNF (Variable problem) :=
  writeClauses problem ++ controlClauses problem ++ unchangedClauses problem

private theorem writeClauses_satisfied (problem : Instance Γ)
    (assignment : Variable problem → Bool) :
    (writeClauses problem).SatisfiedBy assignment ↔
      ∀ (time : Fin problem.time) control symbol,
        assignment (.head time.castSucc control) = true →
        assignment (.tape time.castSucc control.1 symbol) = true →
        assignment (.tape time.succ control.1
          (instruction problem.verifier control.2 symbol).1) = true := by
  simp only [writeClauses, CNF.satisfiedBy_flatMap]
  simp only [CNF.satisfiedBy_iff_forall_clause, List.forall_mem_map]
  simp [and_imp]

private theorem controlClauses_satisfied (problem : Instance Γ)
    (assignment : Variable problem → Bool) :
    (controlClauses problem).SatisfiedBy assignment ↔
      ∀ (time : Fin problem.time) first symbol second,
        assignment (.head time.castSucc first) = true →
        assignment (.tape time.castSucc first.1 symbol) = true →
        assignment (.head time.succ second) = true →
        controlAllowed problem first symbol second := by
  simp only [controlClauses, CNF.satisfiedBy_flatMap]
  simp only [CNF.satisfiedBy_iff_forall_clause, List.forall_mem_map, List.forall_mem_filter]
  simp only [List.mem_finRange, forall_const, mem_controlChoices, Finset.mem_toList,
    Finset.mem_univ, decide_eq_true_eq, Clause.forbid_satisfiedBy, List.forall_mem_cons]
  grind

private theorem unchangedClauses_satisfied (problem : Instance Γ)
    (assignment : Variable problem → Bool) :
    (unchangedClauses problem).SatisfiedBy assignment ↔
      ∀ (time : Fin problem.time) control position, position ≠ control.1 → ∀ symbol,
        assignment (.head time.castSucc control) = true →
        assignment (.tape time.castSucc position symbol) = true →
        assignment (.tape time.succ position symbol) = true := by
  simp only [unchangedClauses, CNF.satisfiedBy_flatMap]
  simp only [CNF.satisfiedBy_iff_forall_clause, List.forall_mem_map, List.forall_mem_filter]
  simp [and_imp]

/--
There are polynomially many transition clauses in the time, tape width, and number of states.
The three summands count written-cell requirements, restrictions on the next head and state,
and requirements that other cells keep their symbols. Each clause has at most three literals.
-/
theorem stepClauses_bounds (problem : Instance Γ) :
    let heads := width problem * (problem.verifier.states + 2)
    let symbols := Fintype.card Γ + 2
    (stepClauses problem).length ≤ problem.time * heads * symbols *
      (1 + heads + width problem) ∧
      ∀ clause ∈ stepClauses problem, clause.length ≤ 3 := by
  let heads := width problem * (problem.verifier.states + 2)
  let symbols := Fintype.card Γ + 2
  have hflat {ι : Type} (items : List ι) (block : ι → CNF (Variable problem)) (bound : Nat)
      (h : ∀ item ∈ items, (block item).length ≤ bound) :
      (items.flatMap block).length ≤ items.length * bound := by
    rw [List.length_flatMap]
    have hs := List.sum_le_length_nsmul (items.map fun item => (block item).length) bound (by
      intro n hn
      obtain ⟨item, hi, rfl⟩ := List.mem_map.mp hn
      exact h item hi)
    simpa [nsmul_eq_mul] using hs
  have hsymbols : (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.length = symbols := by
    simp [symbols, TapeSymbol, Alphabet.Extended]
  have hwrite : (writeClauses problem).length = problem.time * heads * symbols := by
    simp [writeClauses, List.length_flatMap, heads, symbols, TapeSymbol, Alphabet.Extended,
      Nat.mul_assoc]
  have hcontrol : (controlClauses problem).length ≤ problem.time * (heads * (symbols * heads)) := by
    apply (hflat _ _ (heads * (symbols * heads)) ?_).trans_eq
      (by simp only [List.length_finRange])
    intro time _
    apply (hflat _ _ (symbols * heads) ?_).trans_eq
      (by simp only [length_controlChoices]; rfl)
    intro first _
    apply (hflat _ _ heads ?_).trans_eq (by rw [hsymbols])
    intro symbol _
    simpa only [List.length_map, length_controlChoices] using
      List.length_filter_le (fun second => decide (¬controlAllowed problem first symbol second))
        (controlChoices problem)
  have hunchanged : (unchangedClauses problem).length ≤
      problem.time * (heads * (width problem * symbols)) := by
    apply (hflat _ _ (heads * (width problem * symbols)) ?_).trans_eq
      (by simp only [List.length_finRange])
    intro time _
    apply (hflat _ _ (width problem * symbols) ?_).trans_eq
      (by simp only [length_controlChoices]; rfl)
    intro control _
    have h := hflat ((List.finRange (width problem)).filter fun position => position ≠ control.1)
      (fun position => (Finset.univ : Finset (Option (TapeSymbol Γ))).toList.map fun symbol =>
        Clause.implies [.head time.castSucc control, .tape time.castSucc position symbol]
          (.tape time.succ position symbol)) symbols
      (by intro position _; simpa only [List.length_map] using hsymbols.le)
    have hfilter := List.length_filter_le
      (fun position => decide (position ≠ control.1)) (List.finRange (width problem))
    exact h.trans (Nat.mul_le_mul_right symbols
      (by simpa only [List.length_finRange] using hfilter))
  constructor
  · simp only [stepClauses, List.length_append, hwrite]
    change _ ≤ problem.time * heads * symbols * (1 + heads + width problem)
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm symbols]
      at hcontrol hunchanged ⊢
    lia
  · simp only [stepClauses, List.forall_mem_append]
    constructor
    · constructor
      · simp only [writeClauses, List.forall_mem_flatMap, List.forall_mem_map,
          Clause.length_implies, List.length_cons, List.length_nil]
        simp
      · simp only [controlClauses, List.forall_mem_flatMap, List.forall_mem_map,
          Clause.length_forbid, List.length_cons, List.length_nil]
        simp
    · simp only [unchangedClauses, List.forall_mem_flatMap, List.forall_mem_map,
        Clause.length_implies, List.length_cons, List.length_nil]
      simp

variable [DecidableEq Γ]

/--
On the assignment describing a sequence of rows, these clauses hold exactly when each row
follows its predecessor by one verifier transition, with halted rows repeated unchanged.
-/
theorem stepClauses_iff (problem : Instance Γ)
    (certificate : List.Vector Γ problem.certificateLength)
    (rows : Fin (problem.time + 1) → Row problem.verifier (width problem)) :
    (stepClauses problem).SatisfiedBy (rowAssignment certificate rows) ↔
      ∀ time : Fin problem.time, (rows time.castSucc).step = some (rows time.succ) := by
  rw [stepClauses, CNF.satisfiedBy_append, CNF.satisfiedBy_append,
    writeClauses_satisfied, controlClauses_satisfied, unchangedClauses_satisfied]
  constructor
  · rintro ⟨⟨hw, hc⟩, hu⟩ time
    rw [Row.step_iff]
    have hcontrol := hc time
      ((rows time.castSucc).headIndex, (rows time.castSucc).state)
      (rows time.castSucc).symbol ((rows time.succ).headIndex, (rows time.succ).state)
      (by simp [rowAssignment]) (by simp [rowAssignment]) (by simp [rowAssignment])
    obtain ⟨hstate, hhead⟩ := hcontrol
    refine ⟨hstate, hhead, ?_⟩
    have hwrite := hw time ((rows time.castSucc).headIndex, (rows time.castSucc).state)
      (rows time.castSucc).symbol (by simp [rowAssignment]) (by simp [rowAssignment])
    simp only [rowAssignment, decide_eq_true_eq] at hwrite
    apply List.ext_getElem
    · simp
    · intro j hj hk
      by_cases heq : (rows time.castSucc).headIndex.val = j
      · subst j
        simpa only [List.getElem_set_self] using hwrite
      · have hunchanged := hu time
          ((rows time.castSucc).headIndex, (rows time.castSucc).state)
          ⟨j, by simpa using hj⟩ (by intro h; exact heq (congrArg Fin.val h).symm)
          ((rows time.castSucc).cells[j]'(by simpa using hj))
          (by simp [rowAssignment]) (by simp [rowAssignment])
        simp only [rowAssignment, decide_eq_true_eq] at hunchanged
        simpa only [List.getElem_set_ne heq] using hunchanged
  · intro hsteps
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro time control symbol hh ha
      simp only [rowAssignment, decide_eq_true_eq] at hh ha ⊢
      subst control
      simp only [Row.cells_headIndex] at ha
      subst symbol
      obtain ⟨_, _, hcells⟩ := (Row.step_iff _ _).mp (hsteps time)
      simp only [hcells, List.getElem_set_self]
    · intro time first symbol second hh ha hn
      simp only [rowAssignment, decide_eq_true_eq] at hh ha hn
      subst first
      subst second
      simp only [Row.cells_headIndex] at ha
      subst symbol
      obtain ⟨hstate, hhead, _⟩ := (Row.step_iff _ _).mp (hsteps time)
      exact ⟨hstate, hhead⟩
    · intro time control position hposition symbol hh ha
      simp only [rowAssignment, decide_eq_true_eq] at hh ha ⊢
      subst control
      obtain ⟨_, _, hcells⟩ := (Row.step_iff _ _).mp (hsteps time)
      have hne : (rows time.castSucc).headIndex.val ≠ position.val := by
        intro h
        exact hposition (Fin.ext h.symm)
      simpa only [hcells, List.getElem_set_ne hne] using ha

end Algolean.Algorithms.TMSATToSAT
