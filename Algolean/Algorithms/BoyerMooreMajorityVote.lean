/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Comparison
public import Mathlib.Data.List.Count
public import Std.Tactic.Do

/-!
# Boyer-Moore majority vote

This file implements the Boyer-Moore majority-vote algorithm in the `Comparison` query model.

## Algorithm

An element is a strict majority of a list when it occurs in strictly more than half of the
positions. The algorithm finds it, if it exists, in two passes that use only equality comparisons.

The first pass selects a candidate by cancellation. It maintains a current candidate together with a
weight. Starting from no candidate, it processes each element `x` as follows. If there is no current
candidate, `x` becomes the candidate with weight one. If `x` equals the current candidate, the
weight increases by one. If `x` differs from the current candidate, the weight decreases by one, and
the candidate is discarded once the weight reaches zero. Each differing element thus cancels one
unit of the candidate's weight. A strict majority element occurs more often than all other elements
combined, so it survives every cancellation and is the candidate retained at the end.

Cancellation only guarantees that if a strict majority exists it is the retained candidate. The
retained candidate need not itself be a majority when no majority exists. The second pass therefore
counts the actual occurrences of the candidate and returns it only when that count exceeds half the
length, and returns `none` otherwise.

## Main definitions

- `IsMajority`: an element occurs in strictly more than half of a list.
- `boyerMooreMajorityVote`: returns the strict majority element, if one exists.

## Main results

- `boyerMooreMajorityVote_spec`: an `mvcgen`-verified Hoare triple characterizing the result.
- `boyerMooreMajorityVote_correct`: the algorithm returns `some a` exactly when `a` is a strict
  majority.
- `boyerMooreMajorityVote_time_complexity`: the algorithm uses at most `2 * xs.length`
  comparisons.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Prog Comparison Std.Do

/-- `a` is a strict majority of `xs` when it occurs more than `xs.length / 2` times. -/
def IsMajority [BEq α] (a : α) (xs : List α) : Prop :=
  xs.length < 2 * xs.count a

/--
The cancellation state. `none` means no current candidate; `some (c, n)` represents candidate `c`
with weight `n + 1`.
-/
abbrev VoteState (α : Type*) := Option (α × Nat)

namespace VoteState

/-- One pure Boyer-Moore cancellation step. -/
def step [BEq α] (state : VoteState α) (x : α) : VoteState α :=
  match state with
  | none => some (x, 0)
  | some (c, n) =>
      if c == x then
        some (c, n + 1)
      else
        match n with
        | 0 => none
        | n + 1 => some (c, n)

/-- Signed surplus retained for `a`: positive exactly when the retained candidate is `a`. -/
def score [BEq α] (a : α) : VoteState α → Int
  | none => 0
  | some (c, n) =>
      if c == a then
        n + 1
      else
        -(n + 1)

/-- The occurrence surplus of `a`: occurrences minus non-occurrences. -/
def balance [BEq α] (a : α) (xs : List α) : Int :=
  2 * (xs.count a : Int) - xs.length

/-- One monadic Boyer-Moore cancellation step, charging for equality comparisons. -/
def stepM (state : VoteState α) (x : α) : Prog (Comparison α) (VoteState α) := do
  match state with
  | none =>
      return some (x, 0)
  | some (c, n) =>
      let same : Bool ← compare c x
      if same then
        return some (c, n + 1)
      else
        match n with
        | 0 => return none
        | n + 1 => return some (c, n)

end VoteState

/-- Select a majority candidate by cancelling pairs of unequal elements. -/
def majorityCandidate (xs : List α) : Prog (Comparison α) (Option α) := do
  let mut state : VoteState α := none
  for x in xs do
    state ← (VoteState.stepM state x : Prog (Comparison α) (VoteState α))
  return state.map Prod.fst

/--
Mutable state for the verification pass. The parameter keeps loop invariants universe-polymorphic.
-/
structure OccurrenceCount (α : Type*) where
  /-- Occurrences of the candidate counted so far. -/
  value : Nat
  /-- Unused; its type mentions `α` to keep the loop invariant universe-polymorphic. -/
  phantom : Option α

/-- Update an occurrence counter after one comparison. -/
def countStep (candidate x : α) (count : OccurrenceCount α) :
    Prog (Comparison α) (OccurrenceCount α) := do
  let same : Bool ← compare candidate x
  return if same then ⟨count.value + 1, count.phantom⟩ else count

/-- Run the verification loop, retaining its occurrence-count state. -/
def countLoop (candidate : α) (xs : List α) : Prog (Comparison α) (OccurrenceCount α) := do
  let mut count : OccurrenceCount α := ⟨0, none⟩
  for x in xs do
    count ← (countStep candidate x count : Prog (Comparison α) (OccurrenceCount α))
  return count

/-- Count occurrences of `candidate` using comparison queries. -/
def countOccurrences (candidate : α) (xs : List α) : Prog (Comparison α) Nat := do
  return (← countLoop candidate xs).value

/--
Return the strict majority element of `xs`, if it exists, using Boyer-Moore cancellation followed
by a verification pass.
-/
def boyerMooreMajorityVote (xs : List α) : Prog (Comparison α) (Option α) := do
  match ← majorityCandidate xs with
  | none =>
      return none
  | some candidate =>
      let occurrences ← countOccurrences candidate xs
      if xs.length < 2 * occurrences then
        return some candidate
      else
        return none

section Correctness

private theorem VoteState.stepM_eval [BEq α] (state : VoteState α) (x : α) :
    (VoteState.stepM state x).eval Comparison.natCost = VoteState.step state x := by
  rcases state with _ | ⟨c, n⟩
  · simp [VoteState.stepM, VoteState.step]
  · cases n <;> simp [VoteState.stepM, VoteState.step] <;> split <;> simp_all

private lemma VoteState.balance_append_singleton [BEq α] [LawfulBEq α]
    (a x : α) (xs : List α) :
    balance a (xs ++ [x]) = balance a xs + if x == a then 1 else -1 := by
  simp only [balance, List.count_append, List.count_cons, List.count_nil,
    List.length_append, List.length_cons, List.length_nil]
  split <;> lia

private lemma VoteState.score_step [BEq α] [LawfulBEq α]
    (a x : α) (state : VoteState α) :
    score a state + (if x == a then 1 else -1) ≤ score a (VoteState.step state x) := by
  rcases state with _ | ⟨c, n⟩
  · simp [score, step]
  · cases n <;> simp [score, step] <;> grind

private lemma VoteState.balance_pos_of_majority [BEq α] [LawfulBEq α]
    (a : α) (xs : List α) (h : IsMajority a xs) : 0 < balance a xs := by
  simp only [IsMajority, balance] at h ⊢
  lia

private lemma VoteState.candidate_eq_of_score_pos [BEq α] [LawfulBEq α]
    (a : α) (state : VoteState α) (h : 0 < score a state) :
    state.map Prod.fst = some a := by
  rcases state with _ | ⟨c, n⟩ <;> grind [score]

set_option mvcgen.warning false in
/-- A monadic cancellation step evaluates to the corresponding pure state transition. -/
theorem VoteState.stepM_spec [BEq α] [LawfulBEq α]
    (state : VoteState α) (x : α) :
    ⦃⌜True⌝⦄ VoteState.stepM state x ⦃⇓result => ⌜result = VoteState.step state x⌝⦄ := by
  mvcgen [stepM]
  all_goals simp_all [Comparison.hasModel_model, step]

set_option mvcgen.warning false in
/-- One verification step increments precisely when the current element equals the candidate. -/
theorem countStep_spec [BEq α] [LawfulBEq α]
    (candidate x : α) (count : OccurrenceCount α) :
    ⦃⌜True⌝⦄ countStep candidate x count
      ⦃⇓result =>
        ⌜result = if candidate == x then ⟨count.value + 1, count.phantom⟩ else count⌝⦄ := by
  mvcgen [countStep]

set_option mvcgen.warning false in
/-- The first pass retains every strict-majority element as its candidate. -/
theorem majorityCandidate_spec [BEq α] [LawfulBEq α] (xs : List α) :
    ⦃⌜True⌝⦄ majorityCandidate xs
      ⦃⇓candidate => ⌜∀ a, IsMajority a xs → candidate = some a⌝⦄ := by
  mvcgen [majorityCandidate, VoteState.stepM_spec] invariants
    · ⇓⟨it, state⟩ =>
        ⌜∀ a, VoteState.balance a it.prefix ≤ VoteState.score a state⌝
  case vc1.step.success =>
    subst_vars
    intro a
    rw [VoteState.balance_append_singleton]
    refine le_trans ?_ (VoteState.score_step a _ ‹VoteState α›)
    have := ‹∀ a, VoteState.balance a _ ≤ VoteState.score a _› a
    lia
  case vc2.pre => intro a; rfl
  case vc3.post.success =>
    rename_i result hresult
    intro a ha
    exact VoteState.candidate_eq_of_score_pos a _
      ((VoteState.balance_pos_of_majority a xs ha).trans_le (hresult a))

set_option mvcgen.warning false in
/-- The verification loop counts exactly the occurrences of its candidate. -/
theorem countLoop_spec [BEq α] [LawfulBEq α] (candidate : α) (xs : List α) :
    ⦃⌜True⌝⦄ countLoop candidate xs
      ⦃⇓count => ⌜count.value = xs.count candidate⌝⦄ := by
  mvcgen [countLoop, countStep_spec] invariants
    · ⇓⟨it, count⟩ => ⌜count.value = it.prefix.count candidate⌝
  all_goals grind

set_option mvcgen.warning false in
/-- The verification pass counts exactly the occurrences of its candidate. -/
theorem countOccurrences_spec [BEq α] [LawfulBEq α] (candidate : α) (xs : List α) :
    ⦃⌜True⌝⦄ countOccurrences candidate xs
      ⦃⇓count => ⌜count = xs.count candidate⌝⦄ := by
  mvcgen [countOccurrences, countLoop_spec]

set_option mvcgen.warning false in
/--
Functional correctness as a Hoare triple: the returned element is exactly the strict majority,
when one exists.
-/
theorem boyerMooreMajorityVote_spec [BEq α] [LawfulBEq α] (xs : List α) :
    ⦃⌜True⌝⦄ boyerMooreMajorityVote xs
      ⦃⇓result => ⌜∀ a, result = some a ↔ IsMajority a xs⌝⦄ := by
  mvcgen [boyerMooreMajorityVote, majorityCandidate_spec, countOccurrences_spec]
  all_goals grind [IsMajority]

/-- Boyer-Moore returns `some a` exactly when `a` is a strict majority of the input. -/
theorem boyerMooreMajorityVote_correct [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    (boyerMooreMajorityVote xs).eval Comparison.natCost = some a ↔ IsMajority a xs := by
  exact (eval_of_triple (boyerMooreMajorityVote_spec xs) a)

end Correctness

section TimeComplexity

private lemma VoteState.stepM_time [BEq α] (state : VoteState α) (x : α) :
    (VoteState.stepM state x).time Comparison.natCost ≤ 1 := by
  rcases state with _ | ⟨c, n⟩
  · simp [stepM]
  · cases n <;> simp [stepM] <;> split <;> simp_all

private lemma countStep_time [BEq α] (candidate x : α) (count : OccurrenceCount α) :
    (countStep candidate x count).time Comparison.natCost = 1 := by
  simp [countStep]

private lemma voteFoldlM_time [BEq α] (state : VoteState α) (xs : List α) :
    (List.foldlM (m := Prog (Comparison α)) (fun state x => VoteState.stepM state x) state xs).time
      Comparison.natCost ≤ xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, Prog.time_bind, List.length_cons]
      have hstep := VoteState.stepM_time state x
      have htail := ih ((VoteState.stepM state x).eval Comparison.natCost)
      lia

private lemma countFoldlM_time [BEq α] (candidate : α) (count : OccurrenceCount α)
    (xs : List α) :
    (List.foldlM (m := Prog (Comparison α))
      (fun count x => countStep candidate x count) count xs).time
      Comparison.natCost = xs.length := by
  induction xs generalizing count with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldlM_cons, Prog.time_bind, countStep_time, ih]
      lia

private lemma majorityCandidate_time [BEq α] (xs : List α) :
    (majorityCandidate xs).time Comparison.natCost ≤ xs.length := by
  simpa [majorityCandidate] using voteFoldlM_time (none : VoteState α) xs

private lemma countOccurrences_time [BEq α] (candidate : α) (xs : List α) :
    (countOccurrences candidate xs).time Comparison.natCost = xs.length := by
  simpa [countOccurrences, countLoop] using
    countFoldlM_time candidate (⟨0, none⟩ : OccurrenceCount α) xs

/-- The two Boyer-Moore passes use at most two equality comparisons per input element. -/
theorem boyerMooreMajorityVote_time_complexity [BEq α] (xs : List α) :
    (boyerMooreMajorityVote xs).time Comparison.natCost ≤ 2 * xs.length := by
  simp only [boyerMooreMajorityVote, Prog.time_bind]
  split
  · have h := majorityCandidate_time xs
    simp only [Prog.time_pure, add_zero]
    lia
  · rename_i candidate hc
    rw [Prog.time_bind]
    rw [countOccurrences_time]
    have h := majorityCandidate_time xs
    split <;> simp only [Prog.time_pure, add_zero] <;> lia

end TimeComplexity

end Algolean.Algorithms
