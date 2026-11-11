/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Basic
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Copying
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.While

/-!
# Reading a word and updating the machine's state

`ScanTable` lists the control states and nonblank tape symbols. It specifies which state to
enter after reading each symbol in each state.

* `FiniteState.updateForSymbol` reads the symbol under the head and applies the table's rule
  for a chosen state. It leaves the tape and head unchanged and does nothing on a blank cell.
* `FiniteState.updateFromTable` reads the current state and tape symbol and applies their rule.
  It leaves the tape and head unchanged. On a blank cell or in state `none`, it does nothing.
* `scan` repeats these state updates while moving right and stops on the first blank. It
  preserves every tape cell and makes one head move per symbol read.

These are machine templates. The table and the state passed to `updateForSymbol` are fixed
when constructing the containing machine, independently of the input and its length. The
same finite program runs on every input length.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

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
    (fun symbol => do [TMQuery tm]
      state ←ₜ table.next label symbol)

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
  · change Completes (do [TMQuery tm] state ←ₜ table.next label symbol) s 0
      {s with config := ⟨some (table.next label symbol), s.config.BiTape⟩}
    apply Spec.exact_completes
    vcgen
    simp_all

/-- Reading a fixed symbol changes the control label and preserves the tape and head. -/
@[spec] theorem updateForSymbol_spec (table : ScanTable tm) (label : tm.State)
    (symbol : Symbol) (view : BiTape Symbol) (hhead : view.head = some symbol)
    (previous : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨previous, view⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      updateForSymbol table label
    ⦃ fun _ cost final => final.config = ⟨some (table.next label symbol), view⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  have hc : Completes (updateForSymbol table label) current 0
      {current with config := ⟨some (table.next label symbol), current.config.BiTape⟩} :=
    updateForSymbol_correct table label symbol current (by simp [hcfg, hhead])
  vcgen [Spec.of_completes hc initial]
  all_goals simp_all

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

/-- The table chooses the next label from the current label and scanned symbol. -/
@[spec] theorem updateFromTable_spec (table : ScanTable tm) (label : tm.State)
    (symbol : Symbol) (view : BiTape Symbol) (hhead : view.head = some symbol)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some label, view⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      updateFromTable table
    ⦃ fun _ cost final => final.config = ⟨some (table.next label symbol), view⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  have hc : Completes (updateFromTable table) current 0
      {current with config := ⟨some (table.next label symbol), current.config.BiTape⟩} :=
    updateFromTable_correct table label symbol current (by simp [hcfg]) (by simp [hcfg, hhead])
  vcgen [Spec.of_completes hc initial]
  all_goals simp_all

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

/-- Scanning applies the table to every symbol and uses exactly one move per symbol. -/
@[spec] theorem scan_spec (table : ScanTable tm) (left tail : StackTape Symbol)
    (word : List Symbol) (label : tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some label, BiTape.segment left word tail⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      scan table
    ⦃ fun _ cost final => final.config = ⟨some (word.foldl table.next label),
        BiTape.segment (StackTape.prepend word.reverse left) [] tail⟩ ∧
        final.headPos = origin + word.length ∧ cost.steps = elapsed + word.length ⦄ := by
  induction word generalizing left label origin elapsed with
  | nil =>
    unfold scan
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol word ih =>
    unfold scan
    vcgen [Spec.while_step_spec (loop := scan table) (hloop := rfl),
      updateFromTable_spec table label symbol (BiTape.segment left (symbol :: word) tail)
        (by simp) origin elapsed,
      ih (StackTape.cons (some symbol) left) (table.next label symbol)
        (origin + 1) (elapsed + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost,
      List.reverse_cons, StackTape.prepend_append, add_assoc]
    all_goals lia

/--
Scanning preserves the tape to the word's left and beyond the blank on its right. The final
state follows the table's updates, and the number of head moves equals the scanned length.
-/
theorem scan_segment_correct (table : ScanTable tm) (left tail : StackTape Symbol)
    (word : List Symbol) (label : tm.State) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left word tail)
    (hstate : s.config.state = some label) :
    ∃ cost final, Completes (scan table) s cost final ∧
      final.config = ⟨some (word.foldl table.next label),
        BiTape.segment (StackTape.prepend word.reverse left) [] tail⟩ ∧
      final.headPos = s.headPos + word.length ∧ cost.steps = word.length := by
  apply Spec.completes
  vcgen [scan_spec table left tail word label s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

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
  obtain ⟨cost, final, hr, hf, hp, hm⟩ := scan_segment_correct table
    (StackTape.mapSome left) StackTape.nil right label s
      (by cases right <;> simpa [cursor, BiTape.segment] using htape) hstate
  exact ⟨cost, final, hr, by simp [hf, cursor, BiTape.segment], by simp [hf], hp, hm⟩

end Algolean.Algorithms.SingleTapeTuringMachines
