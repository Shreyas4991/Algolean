/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Size

/-!
# Choosing finite control states for compiled programs

This file finds a finite set of execution positions for a query program. Each position is
represented by the program that would run from that position.

* Branches include positions from both alternatives.
* Loops reuse the same positions on every iteration.
* A step from any position leads to another position in the set.

The compiler pairs a program position with a source logical label to form a compiled control state.
The source type `tm.State` supplies the labels. Program positions are stored separately.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler.Internal

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol}

/-- A query program performs tape operations and returns no information through its Lean result. -/
abbrev Program (tm : SingleTapeTM Symbol) := Prog (TMQuery tm) Unit

/-- This function places a list of query instructions before the supplied continuation program. -/
def assemble : List (TMQuery tm Unit) → Program tm → Program tm
  | [], next => next
  | query :: rest, next => .liftBind query (fun _ => assemble rest next)

/-- Assembling instructions agrees with running them in order and then running the continuation. -/
theorem assemble_eq_forM (code : List (TMQuery tm Unit)) (next : Program tm) :
    assemble code next = (do code.forM (fun query => FreeM.lift query); next) := by
  induction code with
  | nil => simp [assemble]
  | cons query rest ih =>
    simp only [List.forM_eq_forM] at ih
    simp only [assemble, List.forM_eq_forM, List.forM_cons, bind_assoc]
    rw [FreeM.liftBind_eq]
    congr 1
    funext _
    exact ih

/-- Extracting and reassembling a program's instructions recovers the original program. -/
theorem assemble_instructions (program : Program tm) :
    assemble (Internal.instructions program) (pure ()) = program := by
  induction program with
  | pure value => cases value; rfl
  | liftBind query next ih =>
    cases query <;> simp_all [Internal.instructions, assemble, -FreeM.liftBind_eq]

variable [DecidableEq Symbol] [DecidableEq tm.State]

/-- A condition needs only the logical label and the symbol under the head. -/
def test (condition : TMCondition tm) (label : Option tm.State) (symbol : Option Symbol) : Bool :=
  condition.eval ⟨label, ⟨symbol, ∅, ∅⟩⟩

/-- Testing these two values gives the same result as evaluating the condition on the full tape. -/
theorem test_eq_eval (condition : TMCondition tm) (cfg : tm.Cfg) :
    test condition cfg.state cfg.BiTape.head = condition.eval cfg := by
  induction condition with
  | tapeIs symbol => rfl
  | stateIs label => rfl
  | not condition ih => simpa only [test, TMCondition.eval] using congrArg Bool.not ih

/--
This function determines which program runs after one query. A selected branch runs before its
continuation. A successful loop test runs the body and then returns to the same loop test.
-/
def advance (program : Program tm) (label : Option tm.State) (symbol : Option Symbol) :
    Program tm :=
  match program with
  | .pure _ => program
  | .liftBind query next =>
    match query with
    | .write _ => next ()
    | .update _ => next ()
    | .move _ => next ()
    | .branchCode condition yes no =>
      assemble (if test condition label symbol then yes else no) (next ())
    | .whileCode condition body =>
      if test condition label symbol then assemble body program else next ()

/--
This set contains the execution positions within the instructions and their branch and loop
bodies. It also contains the continuation, where execution proceeds after the instructions end.
-/
noncomputable def residuals (code : List (TMQuery tm Unit)) (next : Program tm) :
    Finset (Program tm) := by
  classical
  exact match code with
  | [] => {next}
  | query :: rest =>
    let tail := assemble rest next
    let base := insert (assemble (query :: rest) next) (residuals rest next)
    match query with
    | .branchCode _ yes no => base ∪ residuals yes tail ∪ residuals no tail
    | .whileCode condition body =>
      base ∪ residuals body (assemble (.whileCode condition body :: rest) next)
    | _ => base
termination_by sizeOf code

omit [DecidableEq Symbol] [DecidableEq tm.State] in
/-- The start of an instruction list is one of its execution positions. -/
theorem assemble_mem_residuals (code : List (TMQuery tm Unit)) (next : Program tm) :
    assemble code next ∈ residuals code next := by
  classical
  cases code with
  | nil => simp [residuals, assemble]
  | cons query rest => cases query <;> simp [residuals]

omit [DecidableEq Symbol] [DecidableEq tm.State] in
/-- The continuation is one of the positions reached when the instruction list finishes. -/
theorem next_mem_residuals (code : List (TMQuery tm Unit)) (next : Program tm) :
    next ∈ residuals code next := by
  classical
  induction code with
  | nil => simp [residuals]
  | cons query rest ih => cases query <;> simp [residuals, ih]

omit [DecidableEq Symbol] [DecidableEq tm.State] in
/-- There is at most one execution position per instruction, plus the continuation position. -/
theorem card_residuals_le (code : List (TMQuery tm Unit)) (next : Program tm) :
    (residuals code next).card ≤ codeSize code + 1 := by
  classical
  have hunion (s t : Finset (Program tm)) (p : Program tm) (hs : p ∈ s) (ht : p ∈ t) :
      (s ∪ t).card + 1 ≤ s.card + t.card := by
    have hpos : 0 < (s ∩ t).card := Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hs, ht⟩⟩
    have heq := Finset.card_union_add_card_inter s t
    lia
  cases code with
  | nil => simp [residuals, codeSize]
  | cons query rest =>
    let tail := assemble rest next
    let base := insert (assemble (query :: rest) next) (residuals rest next)
    have hrest := card_residuals_le rest next
    have hbase : base.card ≤ (residuals rest next).card + 1 := Finset.card_insert_le _ _
    have htail : tail ∈ base := Finset.mem_insert_of_mem (assemble_mem_residuals rest next)
    cases query with
    | branchCode condition yes no =>
      have hyes := card_residuals_le yes tail
      have hno := card_residuals_le no tail
      have hfirst := hunion base (residuals yes tail) tail htail (next_mem_residuals yes tail)
      have hsecond := hunion (base ∪ residuals yes tail) (residuals no tail) tail
        (Finset.mem_union_left _ htail) (next_mem_residuals no tail)
      simp only [residuals, codeSize]
      change (base ∪ residuals yes tail ∪ residuals no tail).card ≤
        codeSize rest + 1 + (codeSize yes + codeSize no) + 1
      lia
    | whileCode condition body =>
      let root := assemble (.whileCode condition body :: rest) next
      have hbody := card_residuals_le body root
      have hroot : root ∈ base := Finset.mem_insert_self _ _
      have hboth := hunion base (residuals body root) root hroot (next_mem_residuals body root)
      simp only [residuals, codeSize]
      change (base ∪ residuals body root).card ≤
        codeSize rest + 1 + codeSize body + 1
      lia
    | write value | update state | move direction =>
      simp only [residuals, codeSize]
      change base.card ≤ codeSize rest + 1 + 0 + 1
      lia
termination_by sizeOf code

/-- Executing the first query leads to another position within the same instruction list. -/
theorem advance_assemble_mem (query : TMQuery tm Unit) (rest : List (TMQuery tm Unit))
    (next : Program tm) (label : Option tm.State) (symbol : Option Symbol) :
    advance (assemble (query :: rest) next) label symbol ∈ residuals (query :: rest) next := by
  classical
  cases query with
  | write value =>
    simp only [advance, assemble, residuals, Finset.mem_insert]
    exact Or.inr (assemble_mem_residuals rest next)
  | update value =>
    simp only [advance, assemble, residuals, Finset.mem_insert]
    exact Or.inr (assemble_mem_residuals rest next)
  | move direction =>
    simp only [advance, assemble, residuals, Finset.mem_insert]
    exact Or.inr (assemble_mem_residuals rest next)
  | branchCode condition yes no =>
    simp only [advance, assemble, residuals]
    split
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (assemble_mem_residuals yes _))
    · exact Finset.mem_union_right _ (assemble_mem_residuals no _)
  | whileCode condition body =>
    simp only [advance, assemble, residuals]
    split
    · exact Finset.mem_union_right _ (assemble_mem_residuals body _)
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (assemble_mem_residuals rest next))

/--
A step within an instruction list stays among its execution positions. If execution has already
reached the continuation, the next step is a step of that continuation.
-/
theorem advance_mem_or_boundary (code : List (TMQuery tm Unit)) (next pending : Program tm)
    (h : pending ∈ residuals code next) (label : Option tm.State) (symbol : Option Symbol) :
    advance pending label symbol ∈ residuals code next ∨
      advance pending label symbol = advance next label symbol := by
  classical
  cases code with
  | nil =>
    simp only [residuals, Finset.mem_singleton] at h
    subst pending
    exact Or.inr rfl
  | cons query rest =>
    have hroot := advance_assemble_mem query rest next label symbol
    have htail : ∀ pending ∈ residuals rest next,
        advance pending label symbol ∈ residuals (query :: rest) next ∨
          advance pending label symbol = advance next label symbol := by
      intro pending hp
      rcases advance_mem_or_boundary rest next pending hp label symbol with hm | heq
      · left
        cases query <;> simp only [residuals] <;> simp [hm]
      · exact Or.inr heq
    cases query with
    | write value =>
      simp only [residuals, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact Or.inl hroot
      · exact htail _ h
    | update value =>
      simp only [residuals, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact Or.inl hroot
      · exact htail _ h
    | move direction =>
      simp only [residuals, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact Or.inl hroot
      · exact htail _ h
    | branchCode condition yes no =>
      simp only [residuals, Finset.mem_union, Finset.mem_insert] at h
      rcases h with ((rfl | h) | h) | h
      · exact Or.inl hroot
      · exact htail _ h
      · rcases advance_mem_or_boundary yes (assemble rest next) pending h label symbol with hm | heq
        · exact Or.inl (by simp [residuals, hm])
        · rw [heq]
          exact htail _ (assemble_mem_residuals rest next)
      · rcases advance_mem_or_boundary no (assemble rest next) pending h label symbol with hm | heq
        · exact Or.inl (by simp [residuals, hm])
        · rw [heq]
          exact htail _ (assemble_mem_residuals rest next)
    | whileCode condition body =>
      simp only [residuals, Finset.mem_union, Finset.mem_insert] at h
      rcases h with (rfl | h) | h
      · exact Or.inl hroot
      · exact htail _ h
      · rcases advance_mem_or_boundary body
          (assemble (.whileCode condition body :: rest) next) pending h label symbol with hm | heq
        · exact Or.inl (by simp [residuals, hm])
        · exact Or.inl (heq ▸ hroot)
termination_by sizeOf code

/-- These are all execution positions used to compile the complete query program. -/
noncomputable def programPositions (program : Program tm) : Finset (Program tm) :=
  residuals (Internal.instructions program) (pure ())

omit [DecidableEq Symbol] [DecidableEq tm.State] in
/-- The original program is the initial execution position of its compiled machine. -/
theorem mem_programPositions (program : Program tm) : program ∈ programPositions program := by
  simpa only [programPositions, assemble_instructions] using
    assemble_mem_residuals (Internal.instructions program) (pure ())

/-- Every possible next query leads to a position in the same finite set of compiled positions. -/
theorem advance_mem_programPositions (program pending : Program tm)
    (h : pending ∈ programPositions program) (label : Option tm.State) (symbol : Option Symbol) :
    advance pending label symbol ∈ programPositions program := by
  rcases advance_mem_or_boundary (Internal.instructions program) (pure ()) pending h label symbol
    with hm | heq
  · exact hm
  · rw [heq]
    exact next_mem_residuals (Internal.instructions program) (pure ())

end Algolean.Algorithms.TMQuery.Compiler.Internal
