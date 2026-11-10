/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Basic
public import Algolean.Models.SingleTapeTM.Compiler.ToQuery

/-!
# Converting between query programs and transition-table Turing machines

This module provides compilers in both directions over the same tape alphabet.

* Each query instruction becomes one transition. Finishing the program adds a halting transition.
* A compiled control state stores a program position and a logical label. The source type
  `tm.State` supplies the labels. The program position also carries control information.
* With `R` program positions, including completion, and `Q` logical labels, the compiled machine
  has `R * (Q + 1)` control states. The extra label is `none`.
  For `L` instructions, there are at most `L + 1` positions,
  so the machine has at most `(L + 1) * (Q + 1)` control states.
* Query-to-table compilation preserves the output and bounds transitions by `C * time + C`.
* Table-to-query compilation uses one additional control label and preserves time bounds exactly.
  Its loop performs one charged move instruction for every source transition, including stationary
  transitions through the query instruction `Stop`.
* `TMQuery.polyTimeComputable_iff` proves that the two models compute the same polynomial-time
  word-valued functions.

The instruction count includes both branch alternatives and counts each loop body once.
For a fixed query program and source machine, `C` is independent of input length.
A source time bound `T(n)` therefore becomes `C * T(n) + C`, which is affine in source running time.
The compiled state count is also independent of the input and the number of loop iterations.
-/
