/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Classes.NP
public import Algolean.Complexity.Membership.NP.SAT
public import Algolean.Complexity.Reductions.NPtoSAT.Reduction

/-!
# The Cook–Levin theorem

* `cook_levin` states that SAT is NP-complete. SAT belongs to NP, and every language in NP
  over the same formula alphabet has a polynomial-time Karp reduction to SAT.

The reduction is computed by one fixed single-tape Query program for each source language.
Both parts use SAT's original formula encoding with binary variable names.
-/

public section

namespace Algolean.Problems

open Algorithms

/--
SAT is NP-complete: it belongs to NP, and every NP language over its alphabet has a
polynomial-time Karp reduction to it.
-/
theorem cook_levin : SAT ∈ NPComplete :=
  ⟨SAT_mem_NP, fun _ h => NP.karpReducible_SAT h⟩

end Algolean.Problems
