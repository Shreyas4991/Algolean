/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Basic
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.While

/-!
# Reading a word while updating a finite state

* `scan` reads the occupied cells from left to right and stops on the first blank.
* At each symbol, a fixed table determines the next state from the current state and symbol.
* `scan_correct` proves that the symbols are unchanged, the final state is obtained by applying
  that table in reading order, and the number of head moves equals the word's length.

The program uses the existing tape and state conditionals. Its table is finite and fixed before
execution. The input is supplied on the tape, and the final state stays inside the machine.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

namespace FiniteState

/--
These fixed cases are tested in order. The first true condition selects its instructions;
if every test is false, the program does nothing.
-/
def select {α : Type} (cases : List α) (test : α → TMCondition tm)
    (action : α → Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit :=
  match cases with
  | [] => pure ()
  | candidate :: rest => branch (test candidate) (action candidate) (select rest test action)

/-- If exactly the chosen case tests true, the program runs that case's instructions. -/
theorem select_correct {α : Type} [DecidableEq α] (cases : List α)
    (test : α → TMCondition tm) (action : α → Prog (TMQuery tm) Unit)
    (chosen : α) (s final : TMState tm) (cost : TMCost)
    (hmem : chosen ∈ cases)
    (htest : ∀ candidate, (test candidate).eval s.config = decide (candidate = chosen))
    (haction : Completes (action chosen) s cost final) :
    Completes (select cases test action) s cost final := by
  induction cases with
  | nil => simp at hmem
  | cons candidate rest ih =>
    simp only [select]
    apply Completes.branch
    by_cases heq : candidate = chosen
    · subst candidate
      simpa [htest] using haction
    · have hrest : chosen ∈ rest := by simpa [Ne.symm heq] using hmem
      simpa [htest, heq] using ih hrest

end FiniteState

/-- A scan table supplies the next state and lists every state and symbol used by its tests. -/
structure ScanTable (tm : SingleTapeTM Symbol) where
  /-- This list includes every possible state, so the program can test them one at a time. -/
  states : List tm.State
  /-- This list includes every tape symbol other than blank. -/
  symbols : List Symbol
  /-- This function gives the next state for each current state and tape symbol. -/
  next : tm.State → Symbol → tm.State
  /-- Every possible state appears among the program's cases. -/
  mem_states : ∀ label, label ∈ states
  /-- Every tape symbol other than blank appears among the program's cases. -/
  mem_symbols : ∀ symbol, symbol ∈ symbols

namespace FiniteState

/-- This program tests the current symbol and sets the state specified by the table. -/
def updateForSymbol (table : ScanTable tm) (label : tm.State) : Prog (TMQuery tm) Unit :=
  select table.symbols (fun symbol => .tapeIs (some symbol))
    (fun symbol => FreeM.lift (.update (table.next label symbol)))

/-- Reading the supplied symbol sets the expected state without moving or changing the tape. -/
theorem updateForSymbol_correct (table : ScanTable tm)
    (label : tm.State) (symbol : Symbol) (s : TMState tm)
    (hhead : s.config.BiTape.head = some symbol) :
    Completes (updateForSymbol table label) s 0
      {s with config.state := some (table.next label symbol)} := by
  apply select_correct _ _ _ symbol s _ 0 (table.mem_symbols symbol)
  · intro candidate
    simp [hhead, eq_comm]
  · exact completes_update s (table.next label symbol)

/-- This program tests the current state, then uses the current symbol to choose the new state. -/
def updateFromTable (table : ScanTable tm) : Prog (TMQuery tm) Unit :=
  select table.states (fun label => .stateIs (some label)) (updateForSymbol table)

/-- The table chooses the new state without moving the head or changing any tape symbols. -/
theorem updateFromTable_correct (table : ScanTable tm)
    (label : tm.State) (symbol : Symbol) (s : TMState tm)
    (hstate : s.config.state = some label) (hhead : s.config.BiTape.head = some symbol) :
    Completes (updateFromTable table) s 0
      {s with config.state := some (table.next label symbol)} := by
  apply select_correct _ _ _ label s _ 0 (table.mem_states label)
  · intro candidate
    simp [hstate, eq_comm]
  · exact updateForSymbol_correct table label symbol s hhead

end FiniteState

open FiniteState

/--
This Turing machine program reads symbols to the right until it reaches a blank. At each symbol,
`table.next` determines the new state from the current state and symbol. The program changes no tape
symbols and moves right once per symbol. If the current state is `none`, it just moves right.
-/
def scan (table : ScanTable tm) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    updateFromTable table
    moveₜ .Right

/--
Starting in `label`, the scan applies `table.next` once for each symbol of `right`, in order. It stops
on the blank after `right`, preserves all tape symbols, and makes exactly `right.length` head
moves. The symbols in `left` are already behind the head and are not read.
-/
theorem scan_correct (table : ScanTable tm) (left right : List Symbol)
    (label : tm.State) (s : TMState tm)
    (htape : s.config.BiTape = cursor left right) (hstate : s.config.state = some label) :
    ∃ cost final, Completes (scan table) s cost final ∧
      final.config.BiTape = cursor (right.reverse ++ left) [] ∧
      final.config.state = some (right.foldl table.next label) ∧
      final.headPos = s.headPos + right.length ∧ cost.steps = right.length := by
  induction right generalizing left label s with
  | nil =>
    exact ⟨0, s, completes_while_false _ _ s (by simp [htape]),
      by simpa using htape, hstate, by simp, rfl⟩
  | cons symbol right ih =>
    let updated : TMState tm := {s with config.state := some (table.next label symbol)}
    let moved := updated.move .Right
    have hupdate : Completes (updateFromTable table) s 0 updated :=
      updateFromTable_correct table.next label symbol s hstate (by simp [htape])
    have hbody := hupdate.seq (completes_move updated .Right)
    obtain ⟨cost, final, hrun, hfinal, hlabel, hpos, hsteps⟩ :=
      ih (symbol :: left) (table.next label symbol) moved
        (by simp [moved, updated, TMState.move, htape]) rfl
    refine ⟨(0 + updated.moveCost .Right) + cost, final, Completes.while_step (by simp [htape]) hbody hrun, ?_, hlabel, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using hfinal
    · simp [moved, updated, TMState.move] at hpos
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      lia
    · simp [TMState.moveCost, hsteps]

end Algolean.Algorithms.SingleTapeTuringMachines
