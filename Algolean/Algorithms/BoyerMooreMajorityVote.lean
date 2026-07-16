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
# Boyer--Moore majority vote

This file implements the Boyer--Moore majority-vote algorithm in the `Comparison` query model.
Both passes use Lean's `for` syntax: the first cancels unequal pairs to select a candidate, and the
second verifies that the candidate is a strict majority.

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

/-- The cancellation state. `candidate c n` represents a candidate with weight `n + 1`. -/
inductive VoteState (α : Type*) where
  | empty
  | candidate (value : α) (extra : Nat)

namespace VoteState

/-- The candidate retained by a cancellation state. -/
def candidate? : VoteState α → Option α
  | .empty => none
  | .candidate c _ => some c

/-- One pure Boyer--Moore cancellation step. -/
def step [BEq α] (state : VoteState α) (x : α) : VoteState α :=
  match state with
  | .empty => .candidate x 0
  | .candidate c n =>
      if c == x then
        .candidate c (n + 1)
      else
        match n with
        | 0 => .empty
        | n + 1 => .candidate c n

/-- Signed surplus retained for `a`: positive exactly when the retained candidate is `a`. -/
def score [BEq α] (a : α) : VoteState α → Int
  | .empty => 0
  | .candidate c n =>
      if c == a then
        n + 1
      else
        -(n + 1)

/-- The occurrence surplus of `a`: occurrences minus non-occurrences. -/
def balance [BEq α] (a : α) (xs : List α) : Int :=
  2 * (xs.count a : Int) - xs.length

/-- One monadic Boyer--Moore cancellation step, charging for equality comparisons. -/
def stepM (state : VoteState α) (x : α) : Prog (Comparison α) (VoteState α) := do
  match state with
  | .empty =>
      return .candidate x 0
  | .candidate c n =>
      let same : Bool ← compare c x
      if same then
        return .candidate c (n + 1)
      else
        match n with
        | 0 => return .empty
        | n + 1 => return .candidate c n

end VoteState

/-- Select a majority candidate by cancelling pairs of unequal elements. -/
def majorityCandidate (xs : List α) : Prog (Comparison α) (Option α) := do
  let mut state : VoteState α := .empty
  for x in xs do
    state ← (state.stepM x : Prog (Comparison α) (VoteState α))
  return state.candidate?

/--
Mutable state for the verification pass. The parameter keeps loop invariants universe-polymorphic.
-/
structure OccurrenceCount (α : Type*) where
  value : Nat
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
Return the strict majority element of `xs`, if it exists, using Boyer--Moore cancellation followed
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
    (state.stepM x).eval Comparison.natCost = state.step x := by
  cases state with
  | empty => simp [VoteState.stepM, VoteState.step]
  | candidate c n =>
      cases n with
      | zero =>
          simp [VoteState.stepM, VoteState.step]
          split <;> simp_all
      | succ n =>
          simp [VoteState.stepM, VoteState.step]
          split <;> simp_all

private lemma VoteState.balance_append_singleton [BEq α] [LawfulBEq α]
    (a x : α) (xs : List α) :
    balance a (xs ++ [x]) = balance a xs + if x == a then 1 else -1 := by
  simp only [balance, List.count_append, List.count_cons, List.count_nil,
    List.length_append, List.length_cons, List.length_nil]
  split <;> omega

private lemma VoteState.score_step [BEq α] [LawfulBEq α]
    (a x : α) (state : VoteState α) :
    score a state + (if x == a then 1 else -1) ≤ score a (state.step x) := by
  cases state with
  | empty => simp [score, step]
  | candidate c n =>
      by_cases hca : c = a
      · subst c
        by_cases hax : a = x
        · subst x; simp [score, step]
        · have hxa : x ≠ a := fun h => hax h.symm
          cases n <;> simp [score, step, hax, hxa]
      · by_cases hxa : x = a
        · subst x
          cases n <;> simp [score, step, hca]
        · by_cases hcx : c = x
          · subst x; simp [score, step, hca]
          · cases n with
            | zero => simp [score, step, hca, hxa, hcx]
            | succ n => simp [score, step, hca, hxa, hcx]; omega

private lemma VoteState.balance_pos_of_majority [BEq α] [LawfulBEq α]
    (a : α) (xs : List α) (h : IsMajority a xs) : 0 < balance a xs := by
  simp only [IsMajority, balance] at h ⊢
  omega

private lemma VoteState.candidate_eq_of_score_pos [BEq α] [LawfulBEq α]
    (a : α) (state : VoteState α) (h : 0 < score a state) :
    state.candidate? = some a := by
  cases state with
  | empty => simp [score] at h
  | candidate c n =>
      by_cases hca : c = a
      · subst c; simp [candidate?]
      · have hn : (0 : Int) ≤ n := by omega
        simp [score, hca] at h
        omega

set_option mvcgen.warning false in
/-- A monadic cancellation step evaluates to the corresponding pure state transition. -/
theorem VoteState.stepM_spec [BEq α] [LawfulBEq α]
    (state : VoteState α) (x : α) :
    ⦃⌜True⌝⦄ state.stepM x ⦃⇓result => ⌜result = state.step x⌝⦄ := by
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
    calc
      _ ≤ VoteState.score a _ + (if _ == a then 1 else -1) := by
        simpa only [add_comm] using add_le_add_right
          (‹∀ a, VoteState.balance a _ ≤ VoteState.score a _› a)
          (if _ == a then 1 else -1)
      _ ≤ _ := VoteState.score_step a _ _
  case vc2.pre => intro a; rfl
  case vc3.post.success =>
    rename_i result hresult
    intro a ha
    apply VoteState.candidate_eq_of_score_pos a
    have hle : VoteState.balance a xs ≤ VoteState.score a result := hresult a
    exact (VoteState.balance_pos_of_majority a xs ha).trans_le hle

set_option mvcgen.warning false in
/-- The verification loop counts exactly the occurrences of its candidate. -/
theorem countLoop_spec [BEq α] [LawfulBEq α] (candidate : α) (xs : List α) :
    ⦃⌜True⌝⦄ countLoop candidate xs
      ⦃⇓count => ⌜count.value = xs.count candidate⌝⦄ := by
  mvcgen [countLoop, countStep_spec] invariants
    · ⇓⟨it, count⟩ => ⌜count.value = it.prefix.count candidate⌝
  case vc1.step.success pref cur suff hsplit current hcurrent result hresult =>
    subst result
    by_cases h : candidate = cur
    · subst_vars; simp_all [List.count_append]
    · have h' : cur ≠ candidate := Ne.symm h
      simp_all [List.count_append]

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

/-- Boyer--Moore returns `some a` exactly when `a` is a strict majority of the input. -/
theorem boyerMooreMajorityVote_correct [BEq α] [LawfulBEq α] (a : α) (xs : List α) :
    (boyerMooreMajorityVote xs).eval Comparison.natCost = some a ↔ IsMajority a xs := by
  exact (eval_of_triple (boyerMooreMajorityVote_spec xs) a)

end Correctness

section TimeComplexity

private lemma VoteState.stepM_time [BEq α] (state : VoteState α) (x : α) :
    (state.stepM x).time Comparison.natCost ≤ 1 := by
  cases state with
  | empty => simp [stepM]
  | candidate c n =>
      cases n with
      | zero =>
          simp [stepM]
          split <;> simp_all
      | succ n =>
          simp [stepM]
          split <;> simp_all

private lemma countStep_time [BEq α] (candidate x : α) (count : OccurrenceCount α) :
    (countStep candidate x count).time Comparison.natCost = 1 := by
  simp [countStep]

private lemma voteFoldlM_time [BEq α] (state : VoteState α) (xs : List α) :
    (List.foldlM (m := Prog (Comparison α)) (fun state x => state.stepM x) state xs).time
      Comparison.natCost ≤ xs.length := by
  induction xs generalizing state with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, Prog.time_bind, List.length_cons]
      have hstep := VoteState.stepM_time state x
      have htail := ih ((state.stepM x).eval Comparison.natCost)
      omega

private lemma countFoldlM_time [BEq α] (candidate : α) (count : OccurrenceCount α)
    (xs : List α) :
    (List.foldlM (m := Prog (Comparison α))
      (fun count x => countStep candidate x count) count xs).time
      Comparison.natCost = xs.length := by
  induction xs generalizing count with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldlM_cons, Prog.time_bind, List.length_cons]
      rw [countStep_time, ih]
      omega

private lemma majorityCandidate_time [BEq α] (xs : List α) :
    (majorityCandidate xs).time Comparison.natCost ≤ xs.length := by
  simpa [majorityCandidate] using voteFoldlM_time (.empty : VoteState α) xs

private lemma countOccurrences_time [BEq α] (candidate : α) (xs : List α) :
    (countOccurrences candidate xs).time Comparison.natCost = xs.length := by
  simpa [countOccurrences, countLoop] using
    countFoldlM_time candidate (⟨0, none⟩ : OccurrenceCount α) xs

/-- The two Boyer--Moore passes use at most two equality comparisons per input element. -/
theorem boyerMooreMajorityVote_time_complexity [BEq α] (xs : List α) :
    (boyerMooreMajorityVote xs).time Comparison.natCost ≤ 2 * xs.length := by
  simp only [boyerMooreMajorityVote, Prog.time_bind]
  split
  · have h := majorityCandidate_time xs
    simp only [Prog.time_pure, add_zero]
    omega
  · rename_i candidate hc
    rw [Prog.time_bind]
    rw [countOccurrences_time]
    have h := majorityCandidate_time xs
    split <;> simp only [Prog.time_pure, add_zero] <;> omega

end TimeComplexity

end Algolean.Algorithms
