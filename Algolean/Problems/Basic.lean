/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Data.List.Defs
public import Mathlib.Data.Set.Basic

/-!
# Mathematical problem statements

* A `DecisionProblem` is the set of inputs whose answer is yes.
* A `Language` is a set of finite words.

These definitions do not specify a machine, an algorithm, or an input encoding.
-/

@[expose] public section

namespace Algolean.Problems

/-- A decision problem is the set of inputs whose answer is yes. -/
abbrev DecisionProblem (α : Type u) := Set α

/-- A language is a set of finite words. -/
abbrev Language (Symbol : Type u) := Set (List Symbol)

end Algolean.Problems

namespace Algolean.Algorithms

/-- This name preserves access to the shared language definition from earlier algorithm files. -/
abbrev Language (Symbol : Type u) := Problems.Language Symbol

end Algolean.Algorithms
