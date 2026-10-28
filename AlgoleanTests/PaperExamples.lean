/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.ListComparisonSort
public import Std.Tactic.Do

/-!
# Minimum of three: the paper's verification example

`minThree` is the comparison-query program used in the paper's decision tree and
verification examples. `minThree_spec` proves its correctness with `vcgen`.
The four verification conditions correspond to the four root-to-leaf paths in the tree.
-/

@[expose] public section

set_option experimental.vcgen true

namespace AlgoleanTests.PaperExamples

open Algolean Algolean.Algorithms Cslib Cslib.FreeM Std.WP

/-- Integer comparisons with one unit of cost per comparison. -/
def comparisonModel : Model (SortOps Int) Nat :=
  sortModelNat (fun x y => decide (x ≤ y))

local instance : HasModel (SortOps Int) Nat where
  model := comparisonModel

/-- Find the minimum of three integers using comparison queries. -/
def minThree (a b c : Int) : Prog (SortOps Int) Int := do
  if ← lift (SortOps.cmpLE a b) then
    if ← lift (SortOps.cmpLE a c) then
      return a
    else
      return c
  else
    if ← lift (SortOps.cmpLE b c) then
      return b
    else
      return c

/-- `vcgen` reduces correctness to the four paths through the comparison tree. -/
theorem minThree_spec (a b c : Int) :
    ⦃ True ⦄ minThree a b c ⦃ fun m => m = min a (min b c) ⦄ := by
  vcgen [minThree, sortModelNat, Model.handler]
  all_goals simp_all [HasModel.model, comparisonModel, sortModelNat, min_def]
  all_goals split_ifs <;> omega

end AlgoleanTests.PaperExamples
