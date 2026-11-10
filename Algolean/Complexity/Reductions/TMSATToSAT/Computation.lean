/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.TMSAT.Basic
public import Algolean.Models.SingleTapeTM.Tape
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Basic.Finite.Sum

/-!
# Describing a bounded computation using finitely many tape cells

* A `Row` records the state, head position, and a fixed number of tape cells.
* `Row.step` performs one transition and leaves a halted row unchanged. A move beyond the
  recorded cells fails rather than wrapping around or discarding a cell.
* The initial row contains the input, its separator, and a certificate of the required length.
  There are `t` blank cells on each side, where `t` is the instance's time bound.
* A `Computation` has `t + 1` rows. It ends in an accepting row exactly when its certificate
  makes the original machine accept within `t` transitions.

The leftmost recorded position is `-t`; the rightmost is `input.length + certificateLength + t`.
Every position the head can visit within the time bound lies between them. Repeating a halted
row fills out the description after an early halt; it does not add transitions to the original
machine's execution. These are descriptions of computations, not new Turing machine programs.
-/

@[expose] public section

namespace Algolean.Algorithms.TMSATToSAT

open Cslib.Turing Problems.TMSAT Relation Alphabet

variable {Γ : Type}

/--
This records a finite part of the tape and the machine state. The left cells are listed starting
with the cell next to the head, followed by cells farther left. The right cells use the same
order toward the right. Their total length, including the scanned cell, is exactly `width`.
-/
structure Row (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (width : Nat) where
  /-- This is the current state, with `none` meaning that the machine has halted. -/
  state : Option (Fin (verifier.states + 1))
  /-- These cells lie to the left of the head, with the nearest cell first. -/
  left : List (Option (TapeSymbol Γ))
  /-- This is the cell currently under the head, with `none` meaning blank. -/
  symbol : Option (TapeSymbol Γ)
  /-- These cells lie to the right of the head, with the nearest cell first. -/
  right : List (Option (TapeSymbol Γ))
  /-- Every row records exactly the specified number of tape cells. -/
  length_eq : left.length + 1 + right.length = width

namespace Row

variable {verifier : SingleTapeTM.Description (TapeSymbol Γ)} {width : Nat}

/-- This is the head position when the recorded cells are numbered from left to right. -/
def headIndex (row : Row verifier width) : Fin width :=
  ⟨row.left.length, by have := row.length_eq; lia⟩

/-- This lists all recorded cells from left to right, including the cell under the head. -/
def cells (row : Row verifier width) : List (Option (TapeSymbol Γ)) :=
  row.left.reverse ++ row.symbol :: row.right

/-- Listing the cells preserves the width of the row. -/
@[simp] theorem length_cells (row : Row verifier width) : row.cells.length = width := by
  simpa [cells, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using row.length_eq

/-- This builds a row from a state, a list of exactly `width` cells, and a head position. -/
def ofCells (state : Option (Fin (verifier.states + 1)))
    (cells : List.Vector (Option (TapeSymbol Γ)) width) (head : Fin width) :
    Row verifier width where
  state := state
  left := (cells.val.take head.val).reverse
  symbol := cells.val[head.val]'(by simp)
  right := cells.val.drop (head.val + 1)
  length_eq := by
    have := head.isLt
    simp only [List.length_reverse, List.length_take, List.length_drop, cells.property]
    lia

/-- Recovering the state, cells, and head position loses no information about a row. -/
@[simp] theorem ofCells_self (row : Row verifier width) :
    ofCells row.state ⟨row.cells, row.length_cells⟩ row.headIndex = row := by
  cases row
  simp [ofCells, cells, headIndex, List.drop_append]

/--
There are finitely many rows because the state, head position, and each recorded cell are finite.
-/
instance [Finite Γ] : Finite (Row verifier width) := by
  exact Finite.of_injective
    (β := Option (Fin (verifier.states + 1)) × Fin width ×
      List.Vector (Option (TapeSymbol Γ)) width)
    (fun row : Row verifier width =>
      (row.state, row.headIndex, (⟨row.cells, row.length_cells⟩ :
        List.Vector (Option (TapeSymbol Γ)) width))) (by
      intro first second heq
      have h := congrArg (fun data => ofCells data.1 data.2.2 data.2.1) heq
      simpa only [ofCells_self] using h)

/-- This interprets the recorded cells as a CSLib configuration, with blank cells outside them. -/
def toCfg [Fintype Γ] (row : Row verifier width) : verifier.machine.Cfg :=
  ⟨row.state, ⟨row.symbol, StackTape.ofList row.left, StackTape.ofList row.right⟩⟩

/--
This performs the transition selected by the current state and scanned symbol. It writes before
moving, and it records the next state even when that state means halt. An already halted row
stays unchanged. Attempting to move beyond either end of the recorded cells returns `none`.
-/
def step (row : Row verifier width) : Option (Row verifier width) :=
  match row.state with
  | none => some row
  | some state =>
    let (written, movement, next) := verifier.transition state row.symbol
    match movement with
    | none => some {row with state := next, symbol := written}
    | some false =>
      match hl : row.left with
      | [] => none
      | first :: rest => some {
          state := next, left := rest, symbol := first, right := written :: row.right
          length_eq := by
            have := row.length_eq
            simp only [hl, List.length_cons] at this ⊢
            lia }
    | some true =>
      match hr : row.right with
      | [] => none
      | first :: rest => some {
          state := next, left := written :: row.left, symbol := first, right := rest
          length_eq := by
            have := row.length_eq
            simp only [hr, List.length_cons] at this ⊢
            lia }

/-- A row accepts when the machine has halted with the chosen symbol under its head. -/
def Accepting (row : Row verifier width) (yes : Γ) : Prop :=
  row.state = none ∧ row.symbol = some (.inl yes)

/-- Acceptance of a row is exactly acceptance of the configuration it represents. -/
@[simp] theorem toCfg_mem_accepting [Fintype Γ] (row : Row verifier width) (yes : Γ) :
    row.toCfg ∈ accepting yes verifier ↔ row.Accepting yes := Iff.rfl

private def advance (row : Row verifier width) : Row verifier width := row.step.getD row

private theorem step_exists (row : Row verifier width) (hl : row.left ≠ []) (hr : row.right ≠ []) :
    ∃ next, row.step = some next := by
  cases hs : row.state with
  | none => exact ⟨row, by simp [step, hs]⟩
  | some state =>
    generalize ht : verifier.transition state row.symbol = transition
    obtain ⟨written, movement, next⟩ := transition
    cases movement with
    | none => simp [step, hs, ht]
    | some direction =>
      cases direction <;> simp only [step, hs, ht] <;> split <;> simp_all

private theorem advance_bounds (row : Row verifier width) :
    row.left.length ≤ (advance row).left.length + 1 ∧
      row.right.length ≤ (advance row).right.length + 1 := by
  cases hs : row.state with
  | none => simp [advance, step, hs]
  | some state =>
    generalize ht : verifier.transition state row.symbol = transition
    obtain ⟨written, movement, next⟩ := transition
    cases movement with
    | none => simp [advance, step, hs, ht]
    | some direction =>
      cases direction <;> simp only [advance, step, hs, ht] <;> split <;> simp_all <;> lia

private theorem iterate_bounds (row : Row verifier width) (n : Nat) :
    row.left.length ≤ (advance^[n] row).left.length + n ∧
      row.right.length ≤ (advance^[n] row).right.length + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := advance_bounds (advance^[n] row)
    rw [Function.iterate_succ_apply']
    constructor <;> lia

end Row

variable [Fintype Γ]

private def nextCfg (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (configuration : verifier.machine.Cfg) : verifier.machine.Cfg :=
  (verifier.machine.step configuration).getD configuration

private theorem iterate_nextCfg_relates
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (configuration : verifier.machine.Cfg)
    (n : Nat) : RelatesWithinSteps verifier.machine.TransitionRelation configuration
      ((nextCfg verifier)^[n] configuration) n := by
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change RelatesWithinSteps _ configuration
      ((verifier.machine.step ((nextCfg verifier)^[n] configuration)).getD
        ((nextCfg verifier)^[n] configuration)) (n + 1)
    cases hs : verifier.machine.step ((nextCfg verifier)^[n] configuration) with
    | none => simpa only [hs, Option.getD_none] using ih.mono (Nat.le_succ n)
    | some next =>
      simpa only [hs, Option.getD_some] using ih.trans (RelatesWithinSteps.single hs)

private theorem iterate_nextCfg_of_relates
    {verifier : SingleTapeTM.Description (TapeSymbol Γ)}
    {first last : verifier.machine.Cfg} {n : Nat}
    (h : RelatesInSteps verifier.machine.TransitionRelation first last n) :
    (nextCfg verifier)^[n] first = last := by
  induction h with
  | refl => rfl
  | tail middle last n _ hstep ih =>
    rw [Function.iterate_succ_apply', ih]
    change (verifier.machine.step middle).getD middle = last
    rw [hstep]
    rfl

private theorem iterate_nextCfg_accepting
    (yes : Γ) (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (word : List (TapeSymbol Γ)) (time : Nat) :
    (nextCfg verifier)^[time] (verifier.machine.initCfg word) ∈ accepting yes verifier ↔
      AcceptsWithin yes verifier word time := by
  constructor
  · intro h
    exact ⟨_, h, iterate_nextCfg_relates verifier _ time⟩
  · rintro ⟨final, hfinal, steps, hle, hrun⟩
    have hfixed : nextCfg verifier final = final := by
      obtain ⟨state, tape⟩ := final
      have hs : state = none := hfinal.1
      simp [nextCfg, hs]
    have hiter : (nextCfg verifier)^[time] (verifier.machine.initCfg word) = final := by
      rw [show time = (time - steps) + steps by lia, Function.iterate_add_apply,
        iterate_nextCfg_of_relates hrun, Function.iterate_fixed hfixed]
    simpa only [hiter] using hfinal

private theorem step_toCfg {verifier : SingleTapeTM.Description (TapeSymbol Γ)} {width : Nat}
    {row next : Row verifier width} (h : row.step = some next) :
    next.toCfg = nextCfg verifier row.toCfg := by
  cases hs : row.state with
  | none =>
    have heq : row = next := by simpa [Row.step, hs] using h
    subst next
    simp [nextCfg, Row.toCfg, hs]
  | some state =>
    generalize ht : verifier.transition state row.symbol = transition
    obtain ⟨written, movement, nextState⟩ := transition
    cases movement with
    | none =>
      simp only [Row.step, hs, ht] at h
      cases Option.some.inj h
      simp [nextCfg, Row.toCfg, SingleTapeTM.Description.machine, hs, ht,
        BiTape.optionMove, BiTape.write]
    | some direction =>
      cases direction <;> simp only [Row.step, hs, ht] at h <;> split at h
      all_goals try contradiction
      all_goals cases Option.some.inj h
      all_goals
        simp_all [nextCfg, Row.toCfg, SingleTapeTM.Description.machine,
          BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.moveRight, BiTape.write]

/-- This is the number of cells needed for the initial word and `time` blank cells on each side. -/
def width (problem : Instance Γ) : Nat :=
  problem.input.length + problem.certificateLength + 2 * problem.time + 1

/--
This starts the verifier on the input, separator, and certificate. There are `time` blank cells
to the left of the initial head and `time` blank cells after the certificate. The head starts
at recorded position `time`, which represents position zero of the original tape.
-/
def initialRow (problem : Instance Γ)
    (certificate : List.Vector Γ problem.certificateLength) :
    Row problem.verifier (width problem) := by
  let word := (wordPair Γ).encode (problem.input, certificate.val)
  refine {
    state := some problem.verifier.initial
    left := List.replicate problem.time none
    symbol := word.head?
    right := (word.drop 1).map some ++ List.replicate problem.time none
    length_eq := ?_ }
  have hlength : word.length = problem.input.length + problem.certificateLength + 1 := by
    simp [word, wordPair_encode, certificate.property]
    lia
  simp only [List.length_replicate, List.length_append, List.length_map, List.length_drop,
    hlength, width]
  lia

private theorem initialRow_toCfg (problem : Instance Γ)
    (certificate : List.Vector Γ problem.certificateLength) :
    (initialRow problem certificate).toCfg =
      problem.verifier.machine.initCfg ((wordPair Γ).encode (problem.input, certificate.val)) := by
  let word := (wordPair Γ).encode (problem.input, certificate.val)
  change (⟨some problem.verifier.initial,
    ⟨word.head?, StackTape.ofList (List.replicate problem.time none),
      StackTape.ofList ((word.drop 1).map some ++ List.replicate problem.time none)⟩⟩ :
      problem.verifier.machine.Cfg) = problem.verifier.machine.initCfg word
  simp only [StackTape.ofList_replicate_none, StackTape.ofList_append_blanks,
    StackTape.ofList_map_some]
  cases word <;> rfl

omit [Fintype Γ] in
private theorem step_iterate_initial (problem : Instance Γ)
    (certificate : List.Vector Γ problem.certificateLength) (n : Nat) (hn : n < problem.time) :
    let row := Row.advance^[n] (initialRow problem certificate)
    row.step = some (Row.advance row) := by
  let row := Row.advance^[n] (initialRow problem certificate)
  have hb := Row.iterate_bounds (initialRow problem certificate) n
  have hleft := hb.1
  change (List.replicate problem.time (none : Option (TapeSymbol Γ))).length ≤
    row.left.length + n at hleft
  rw [List.length_replicate] at hleft
  have hstart : problem.time ≤ (initialRow problem certificate).right.length := by
    simp only [initialRow, List.length_append, List.length_map, List.length_drop,
      List.length_replicate]
    lia
  have hright : problem.time ≤ row.right.length + n := hstart.trans hb.2
  obtain ⟨next, heq⟩ := Row.step_exists row
    (by intro h; simp only [h, List.length_nil] at hleft; lia)
    (by intro h; simp only [h, List.length_nil] at hright; lia)
  change row.step = some (row.step.getD row)
  simp [heq]

/--
This describes the verifier's computation on one certificate of the required length. There are
exactly `time + 1` rows, starting with the prescribed input. Each following row performs one
transition, or repeats an already halted row. The rows all record the same fixed tape interval.
-/
structure Computation (problem : Instance Γ) where
  /-- The certificate contains exactly the number of symbols required by the instance. -/
  certificate : List.Vector Γ problem.certificateLength
  /-- A row records the configuration at each time from zero through the time bound. -/
  rows : Fin (problem.time + 1) → Row problem.verifier (width problem)
  /-- The first row starts the verifier on the input, separator, and chosen certificate. -/
  initial : rows 0 = initialRow problem certificate
  /-- Consecutive rows obey the transition table, repeating a row after the machine halts. -/
  next : ∀ i : Fin problem.time, (rows i.castSucc).step = some (rows i.succ)

namespace Computation

variable {problem : Instance Γ}

/--
The padding with blank cells lets every certificate's computation run through all the rows.
Before the last row, neither end of the recorded interval can obstruct a head movement.
-/
private def ofCertificate (problem : Instance Γ)
    (certificate : List.Vector Γ problem.certificateLength) :
    Computation problem where
  certificate := certificate
  rows i := Row.advance^[i.val] (initialRow problem certificate)
  initial := rfl
  next i := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Function.iterate_succ_apply'] using
      step_iterate_initial problem certificate i.val i.isLt

/--
The computation accepts when its last row has halted with the accepting symbol under the head.
-/
def Accepting (computation : Computation problem) (yes : Γ) : Prop :=
  (computation.rows (Fin.last problem.time)).Accepting yes

omit [Fintype Γ] in
private theorem row_eq_iterate (computation : Computation problem) (i : Fin (problem.time + 1)) :
    computation.rows i = Row.advance^[i.val] (initialRow problem computation.certificate) := by
  induction i using Fin.induction with
  | zero => exact computation.initial
  | succ i ih =>
    simp only [Fin.val_succ, Function.iterate_succ_apply']
    simp only [Fin.val_castSucc] at ih
    rw [← ih]
    simp only [Row.advance, computation.next, Option.getD_some]

omit [Fintype Γ] in
/--
At row `i`, the head is at most `i` cells from its initial position. Recorded position `time`
represents position zero of the original tape, so this bounds movement in both directions.
-/
theorem headIndex_bounds (computation : Computation problem) (i : Fin (problem.time + 1)) :
    let position := ((computation.rows i).headIndex.val : Int) - problem.time
    position ∈ Set.Icc (-(i.val : Int)) i.val := by
  have hb := Row.iterate_bounds (initialRow problem computation.certificate) i.val
  rw [← computation.row_eq_iterate i] at hb
  have hfirst := (initialRow problem computation.certificate).length_eq
  have hcurrent := (computation.rows i).length_eq
  have hleft : (initialRow problem computation.certificate).left.length = problem.time := by
    simp [initialRow]
  rw [hleft] at hb hfirst
  dsimp [Row.headIndex]
  constructor <;> lia

private theorem row_toCfg (computation : Computation problem) (i : Fin (problem.time + 1)) :
    (computation.rows i).toCfg = (nextCfg problem.verifier)^[i.val]
      (problem.verifier.machine.initCfg
        ((wordPair Γ).encode (problem.input, computation.certificate.val))) := by
  induction i using Fin.induction with
  | zero =>
    rw [computation.initial, initialRow_toCfg]
    rfl
  | succ i ih =>
    simp only [Fin.val_succ, Function.iterate_succ_apply']
    rw [step_toCfg (computation.next i), ih]
    rfl

/--
The description accepts exactly when the original CSLib machine accepts its chosen certificate
within the instance's time bound. Repeated halted rows do not count as extra machine transitions.
-/
theorem accepting_iff (computation : Computation problem) (yes : Γ) :
    computation.Accepting yes ↔ AcceptsWithin yes problem.verifier
      ((wordPair Γ).encode (problem.input, computation.certificate.val)) problem.time := by
  rw [Accepting, ← Row.toCfg_mem_accepting, computation.row_toCfg]
  exact iterate_nextCfg_accepting yes problem.verifier _ problem.time

end Computation

/--
A TMSAT instance is satisfiable exactly when it has an accepting computation described by these
finitely many rows and cells. The certificate retains exactly the length required by TMSAT.
-/
theorem mem_satisfiable_iff_exists_computation (problem : Instance Γ) (yes : Γ) :
    problem ∈ satisfiable yes ↔ ∃ computation : Computation problem, computation.Accepting yes := by
  constructor
  · rintro ⟨certificate, hlength, haccept⟩
    let computation := Computation.ofCertificate problem ⟨certificate, hlength⟩
    exact ⟨computation, (computation.accepting_iff yes).mpr haccept⟩
  · rintro ⟨computation, haccept⟩
    exact ⟨computation.certificate.val, computation.certificate.property,
      (computation.accepting_iff yes).mp haccept⟩

end Algolean.Algorithms.TMSATToSAT
