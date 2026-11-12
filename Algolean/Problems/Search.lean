/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic

/-!
# First-match array search

The mathematical input and specification are independent of the machine and its encoding.
An answer is the first matching index, or `none` if the key is absent.
-/

@[expose] public section

namespace Algolean.Search

/-- An array and the value to find in it. -/
structure Input (α : Type u) where
  data : Array α
  key : α

/-- A matching index with no earlier occurrence. -/
def IsFirstMatch (data : Array α) (key : α) (i : Nat) : Prop :=
  i < data.size ∧ data[i]? = some key ∧ ∀ j, j < i → data[j]? ≠ some key

/-- First-match search, including an absence certificate for unsuccessful searches. -/
def linearSearch (input : Input α) : Set (Option Nat) :=
  {output | match output with
    | none => input.key ∉ input.data
    | some i => IsFirstMatch input.data input.key i}

end Algolean.Search
