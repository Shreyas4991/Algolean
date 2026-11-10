/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Erasing
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
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This program erases the input and writes `yes` if it equals `expected`, or `no` otherwise.
The comparison includes the end of the word, so a proper prefix does not count as a match.
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

/--
Comparing the whole input produces exactly its equality answer and erases every input cell.
The head finishes just after the original input, using exactly its length in head moves.
-/
theorem compareWord_correct (yes no : Symbol) (expected input : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.mk₁ input) :
    Runs (compareWord tm yes no expected) s
      (BiTape.mk₁ [if input = expected then yes else no])
      (s.headPos + input.length) input.length := by
  induction expected generalizing input s with
  | nil =>
    have hreject := (eraseRight_correct input s
      (by simpa [cursor_start] using htape)).append_write (some no)
    unfold compareWord
    apply Runs.branch
    cases input with
    | nil => simpa [htape, BiTape.mk₁, BiTape.nil, BiTape.write] using write_correct s (some yes)
    | cons symbol rest => simpa [htape, BiTape.mk₁, BiTape.nil, BiTape.write] using hreject
  | cons symbol rest ih =>
    have hreject := (eraseRight_correct input s
      (by simpa [cursor_start] using htape)).append_write (some no)
    unfold compareWord
    apply Runs.branch
    cases input with
    | nil => simpa [htape, BiTape.mk₁, BiTape.nil, BiTape.write] using hreject
    | cons first input =>
      by_cases heq : first = symbol
      · subst first
        have hfirst := eraseAndMove_correct symbol input s
          (by simpa [cursor_start] using htape)
        have hrest := hfirst.seq (q := compareWord tm yes no rest) (by
          intro middle hmiddle hpos
          simpa [hpos, Nat.cast_add, add_assoc] using
            ih input middle
              (by simpa [cursor_start] using congrArg SingleTapeTM.Cfg.BiTape hmiddle))
        simpa [htape, BiTape.mk₁, Nat.add_comm, add_comm, add_left_comm, add_assoc] using hrest
      · simpa [htape, BiTape.mk₁, BiTape.nil, BiTape.write, heq] using hreject

/--
This machine has one control state. The comparison instructions supply all of its behavior.
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
  outputsFunInTime input := by
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
