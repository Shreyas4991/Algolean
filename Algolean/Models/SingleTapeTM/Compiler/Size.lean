/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM

/-!
# Counting instructions in query programs

The instruction count includes both alternatives of each branch and counts each loop body once.
It measures the source program independently of the input and the number of loop iterations.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol}

namespace Internal

/--
This function counts instruction occurrences in a list, including every branch and loop body once.
It counts both alternatives of a branch, regardless of which alternative is executed.
-/
def codeSize : List (TMQuery tm Unit) → ℕ
  | [] => 0
  | query :: rest => codeSize rest + 1 + match query with
    | .branchCode _ yes no => codeSize yes + codeSize no
    | .whileCode _ body => codeSize body
    | _ => 0
termination_by code => sizeOf code

end Internal

/--
This function counts the program's instruction occurrences. It includes both alternatives of
each branch and counts each loop body once, regardless of how many times the loop executes.
-/
def instructionCount (program : Prog (TMQuery tm) Unit) : ℕ :=
  Internal.codeSize (TMQuery.Internal.instructions program)

end Algolean.Algorithms.TMQuery.Compiler
