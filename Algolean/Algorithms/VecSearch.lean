/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas, Eric Wieser
-/

module

public import Algolean.Models.VecSearch
public import Batteries.Data.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Set

@[expose] public section

/-!
# Linear search and Binary Search in Fin vectors

In this file we state and prove the correctness and complexity of linear search in lists under
the `VecSearch` model.
--

## Main Definitions

- `vecLinearSearch` : Linear search algorithm in the `VecSearch` query model
- `vecBinarySearch` : Binary search algorithm in the `VecSearch` query model

## Main results

- `vecLinearSearch_eval`: `vecLinearSearch` evaluates identically to `List.contains`.
- `listLinearSearchM_time_complexity_upper_bound` : `linearSearch` takes at most `n`
  comparison operations
- `listLinearSearchM_time_complexity_lower_bound` : There exist lists on which `linearSearch` needs
  `n` comparisons
-/
namespace Algolean

namespace Algorithms

open Cslib Prog

open VecSearch in
/-- Linear Search in Lists on top of the `ListSearch` query model. -/
@[simp, grind]
def vecLinearSearch (v : Vector α n) (x : α) : Prog (VecSearch α) Bool := do
  match n with
  | 0 => return false
  | _ + 1 =>
    let cmp : Bool ← compare v 0 x
    if cmp then
      return true
    else
      vecLinearSearch (v.tail) x


@[simp, grind .]
lemma vecLinearSearch_eval [BEq α] [LawfulBEq α] (v : Vector α n) (x : α) :
    ((vecLinearSearch v x).eval VecSearch.natCost) = (x ∈ v) := by
  fun_induction vecLinearSearch with
  | case1 v =>
      simp_all [Vector.eq_empty (xs := v)]
  | case2 n v ih =>
    simp_all only [Vector.tail_eq_cast_extract, Nat.add_one_sub_one, Vector.mem_cast, eq_iff_iff,
      FreeM.lift_def, FreeM.pure_eq_pure, Cslib.FreeM.bind_eq_bind, FreeM.liftBind_bind,
      FreeM.pure_bind, eval_liftBind, VecSearch.natCost_evalQuery, Fin.getElem_fin,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, beq_iff_eq, Nat.succ_eq_add_one]
    split_ifs with h₀
    · simp_all
    · simp_all only [beq_iff_eq]
      constructor
      · intro hx
        -- This goal should be a Vector API lemma
        exact (Vector.mem_toList_iff).1 <|
          List.mem_of_mem_tail <|
            List.mem_of_mem_take <|
              by simpa [Vector.toList_extract] using (Vector.mem_toList_iff).2 hx
      · intro hx
        -- There should also be an API lemma here for Vector. Easy to go through lists though
        have hcons : v.toList = v[0] :: v.toList.tail := by
          simpa using (List.drop_eq_getElem_cons (l := v.toList) (i := 0) (by simp))
        have htake : (v.toList.tail).take n = v.toList.tail :=
          List.take_of_length_le (by simp)
        exact (Vector.mem_toList_iff).1 <|
          by
            simpa [Vector.toList_extract, htake] using
              (List.mem_of_ne_of_mem h₀ (hcons ▸ (Vector.mem_toList_iff).2 hx))

lemma listLinearSearchM_correct_true [BEq α] [LawfulBEq α] (v : Vector α n)
    {x : α} (x_mem_l : x ∈ v) : (vecLinearSearch v x).eval VecSearch.natCost = true := by
  rwa [vecLinearSearch_eval]

lemma listLinearSearchM_correct_false [BEq α] [LawfulBEq α] (v : Vector α n)
    {x : α} (x_mem_l : x ∉ v) : (vecLinearSearch v x).eval VecSearch.natCost = false := by
  apply Bool.eq_false_iff.mpr
  intro hx
  exact x_mem_l (by simpa [vecLinearSearch_eval v x] using hx)

lemma listLinearSearchM_time_complexity_upper_bound [BEq α] (v : Vector α n) (x : α) :
    (vecLinearSearch v x).time VecSearch.natCost ≤ n := by
  fun_induction vecLinearSearch
  · simp
  · simp
    split_ifs
    · simp
    · simp_all
      linarith

lemma listLinearSearchM_time_complexity_lower_bound [DecidableEq α] [Nontrivial α] (n : ℕ) :
    ∃ (v : Vector α n) (x : α), (vecLinearSearch v x).time VecSearch.natCost = n := by
  obtain ⟨x, y, hneq⟩ := exists_pair_ne α
  use Vector.replicate n y, x
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [vecLinearSearch, FreeM.lift_def, FreeM.pure_eq_pure, Nat.add_one_sub_one,
        Vector.tail_eq_cast_extract, Vector.extract_replicate, Cslib.FreeM.bind_eq_bind,
        FreeM.liftBind_bind, FreeM.pure_bind, time_liftBind, VecSearch.natCost_cost,
        VecSearch.natCost_evalQuery, Fin.getElem_fin, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        Vector.getElem_replicate, beq_iff_eq]
      split_ifs with heq
      · exfalso
        exact hneq heq
      · simp_all
        have s₁ : min (n + 1) (n + 1) - 1 = n := by grind
        have hsucc :
            (vecLinearSearch (Vector.replicate n y) x).time VecSearch.natCost + 1 = n + 1 := by
          exact congrArg (fun t => t + 1) ih
        simpa [s₁, Vector.cast, Nat.add_comm] using hsucc

end Algorithms

end Algolean
