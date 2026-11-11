/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.MachineComposition

/-!
# Comparing the input with a fixed word

* `compareWord` compares the whole input with a word chosen when constructing the program.
* It erases the input and leaves one symbol saying whether the words are equal.
* `compareWord_correct` proves its answer and counts one head move per input symbol.
* `PolyTimeComputable.compareOutput` adds this comparison to an existing computation.

The comparison word is fixed independently of the input. Its symbols determine a finite sequence
of tests. The same program handles inputs of every length, including the empty word.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This program erases the input and writes `yes` if it equals `expected`, or `no` otherwise.
The comparison includes the end of the word, so a proper prefix does not count as a match.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def compareWord (tm : SingleTapeTM Symbol) (yes no : Symbol) :
    List Symbol → Prog (TMQuery tm) Unit
  | [] => do [TMQuery tm]
    ifₜ tape =ₜ none then
      tape ←ₜ some yes
    else
      eraseRight tm
      tape ←ₜ some no
  | symbol :: rest => do [TMQuery tm]
    ifₜ tape =ₜ some symbol then
      eraseAndMove tm
      compareWord tm yes no rest
    else
      eraseRight tm
      tape ←ₜ some no

/-- Comparing the whole word erases it and writes its equality answer after its original end. -/
@[spec] theorem compareWord_spec (yes no : Symbol) (expected input : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      compareWord tm yes no expected
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.mk₁ [if input = expected then yes else no]⟩ ∧
        final.headPos = origin + input.length ∧ cost.steps = elapsed + input.length ⦄ := by
  induction expected generalizing input origin elapsed with
  | nil =>
    vcgen [compareWord, eraseRight_spec input StackTape.nil label origin elapsed]
    all_goals cases input
    all_goals simp_all [TMState.write, BiTape.mk₁, BiTape.nil, BiTape.write]
  | cons symbol rest ih =>
    cases input with
    | nil =>
      vcgen [compareWord, eraseRight_spec [] StackTape.nil label origin elapsed]
      all_goals simp_all [TMState.write, BiTape.mk₁, BiTape.nil, BiTape.write]
    | cons first input =>
      vcgen [compareWord, eraseAndMove_spec,
        eraseRight_spec (first :: input) StackTape.nil label origin elapsed,
        ih input (origin + 1) (elapsed + 1)]
      all_goals cases input
      all_goals simp_all [TMState.write, TMState.move, TMState.moveCost, BiTape.mk₁,
        BiTape.nil, BiTape.write, BiTape.moveRight, add_assoc]
      all_goals lia

/--
Comparing the whole input produces exactly its equality answer and erases every input cell.
The head finishes just after the original input, using exactly its length in head moves.
-/
theorem compareWord_correct (yes no : Symbol) (expected input : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.mk₁ input) :
    Runs (compareWord tm yes no expected) s
      (BiTape.mk₁ [if input = expected then yes else no])
      (s.headPos + input.length) input.length := by
  apply Spec.runs
  vcgen [compareWord_spec yes no expected input s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine has one control state. The comparison instructions define all of its behavior.
-/
abbrev comparisonControl (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] :
    SingleTapeTM Symbol where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- Comparing with a fixed word is computable in linear time on the same tape alphabet. -/
noncomputable def compareWordComputer (yes no : Symbol) (expected : List Symbol) :
    PolyTimeComputable (fun input => [if input = expected then yes else no]) where
  tm := comparisonControl Symbol
  program := compareWord (comparisonControl Symbol) yes no expected
  timeBound := id
  computesWithin := by
    apply TMQuery.ComputesWithin.of_outputsWithinTime
    intro input
    obtain ⟨cost, final, hr, htape, _, hsteps⟩ :=
      compareWord_correct yes no expected input (TMState.init (comparisonControl Symbol) input) rfl
    exact hr.outputsWithinTime
      (by simpa using congrArg SingleTapeTM.Cfg.BiTape htape) (by simpa using hsteps.le)
  poly := X
  bounds _ := by simp

end Algolean.Algorithms.SingleTapeTuringMachines

namespace Algolean.Algorithms.TMQuery

open SingleTapeTuringMachines

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

/--
This runs the given computation and compares its entire output with `expected`. It returns the
one-symbol word `[yes]` on equality and `[no]` otherwise, with a polynomial time bound.
-/
noncomputable def PolyTimeComputable.compareOutput {f : List Symbol → List Symbol}
    (computer : PolyTimeComputable f) (expected : List Symbol) (yes no : Symbol) :
    PolyTimeComputable (fun input => [if f input = expected then yes else no]) := by
  exact computer.comp (compareWordComputer yes no expected)

end Algolean.Algorithms.TMQuery
