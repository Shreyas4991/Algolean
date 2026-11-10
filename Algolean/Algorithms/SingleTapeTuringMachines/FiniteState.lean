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
# Reading a word and updating the machine's state

* `scan` starts under the tape head, reads to the right, and stops on the first blank.
* After reading symbol `a` in state `q`, it changes the state to `table.next q a` and moves right.
* `scan_correct` proves that every tape symbol is preserved, the state changes follow this rule,
  and the number of head moves equals the number of symbols read.

`ScanTable` lists the state names and tape symbols so that the program can compare them with
the current state and the symbol under the head using ordinary conditionals. These lists and
the rule `table.next` are chosen once when constructing the program. The same program runs on
every input length; only the initial tape contents and machine state vary between runs.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This defines a rule for changing state while reading a tape: `next q a` is the state to enter
after reading symbol `a` in state `q`. The lists `states` and `symbols` let the program find the
current state and symbol by comparing them with each list element, from first to last.
-/
structure ScanTable (tm : SingleTapeTM Symbol) where
  /-- The program compares the current state with these state names, from first to last. -/
  states : List tm.State
  /-- The program compares the symbol under the head with these symbols, from first to last. -/
  symbols : List Symbol
  /-- This function gives the next state for each current state and tape symbol. -/
  next : tm.State → Symbol → tm.State
  /-- Every possible state name appears in `states`, so these comparisons can find it. -/
  mem_states : ∀ label, label ∈ states
  /-- Every tape symbol other than blank appears in `symbols`, so these comparisons can find it. -/
  mem_symbols : ∀ symbol, symbol ∈ symbols

namespace FiniteState

/--
This Turing machine program compares the symbol under the head with each element of
`table.symbols`, from first to last. When it finds a match `a`, it sets the state to
`table.next label a`. It leaves the head and tape symbols unchanged. On a blank, it does nothing.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def updateForSymbol (table : ScanTable tm) (label : tm.State) : Prog (TMQuery tm) Unit :=
  select table.symbols (fun symbol => .tapeIs (some symbol))
    (fun symbol => FreeM.lift (.update (table.next label symbol)))

/--
If the head is on `symbol`, the program sets the state to `table.next label symbol`.
The head does not move, and all tape symbols are preserved.
-/
theorem updateForSymbol_correct (table : ScanTable tm)
    (label : tm.State) (symbol : Symbol) (s : TMState tm)
    (hhead : s.config.BiTape.head = some symbol) :
    Completes (updateForSymbol table label) s 0
      {s with config.state := some (table.next label symbol)} := by
  apply select_correct _ _ _ symbol s _ 0 (table.mem_symbols symbol)
  · intro candidate
    simp [hhead, eq_comm]
  · exact completes_update s (table.next label symbol)

/--
This Turing machine program compares the current state with each name in `table.states`, from
first to last. When it finds a match `q`, it runs `updateForSymbol table q` to read the current
tape symbol and change the state. If the state is `none`, it leaves the machine unchanged.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def updateFromTable (table : ScanTable tm) : Prog (TMQuery tm) Unit :=
  select table.states (fun label => .stateIs (some label)) (updateForSymbol table)

/--
If the machine is in state `label` with the head on `symbol`, this program sets the state to
`table.next label symbol`. The head does not move, and all tape symbols are preserved.
-/
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
This Turing machine program repeatedly reads the symbol under the head, changes the state from
`q` to `table.next q a` when it reads symbol `a`, and moves right. It stops on the first blank
and preserves every tape symbol. If the state is `none`, it moves without changing the state.

The lists and state-change rule in `table` are chosen when constructing the program. This one
program handles all input lengths. It reads the initial tape and state during execution.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def scan (table : ScanTable tm) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    updateFromTable table
    moveₜ .Right

/--
Starting in state `label`, the program reads the symbols of `right` from first to last.
For example, reading `[a, b]` leaves it in state `table.next (table.next label a) b`.
It stops on the following blank, preserves the tape, and makes exactly `right.length` head moves.
The symbols in `left` are behind the starting head position and are not read.
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
      updateFromTable_correct table label symbol s hstate (by simp [htape])
    have hbody := hupdate.seq (completes_move updated .Right)
    obtain ⟨cost, final, hrun, hfinal, hlabel, hpos, hsteps⟩ :=
      ih (symbol :: left) (table.next label symbol) moved
        (by simp [moved, updated, TMState.move, htape]) rfl
    refine ⟨(0 + updated.moveCost .Right) + cost, final,
      Completes.while_step (by simp [htape]) hbody hrun, ?_, hlabel, ?_, ?_⟩
    · simpa [List.reverse_cons, List.append_assoc] using hfinal
    · simp [moved, updated, TMState.move] at hpos
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      lia
    · simp [TMState.moveCost, hsteps, Nat.add_comm]

end Algolean.Algorithms.SingleTapeTuringMachines
