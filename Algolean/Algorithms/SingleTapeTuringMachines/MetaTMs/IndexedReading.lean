/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnarySubtraction
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.FiniteState

/-!
# Finding a word position recorded in a binary counter

The reader walks through a word while decreasing a binary counter farther left. It stops at
its requested position or at the blank ending the word. The word and every intervening word
are preserved. Leading zeros are permitted in the counter.

This is a machine template. The containing machine fixes the digit symbols, control states,
alphabet comparisons, and number of intervening words once. The counter and word are tape data.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private noncomputable def decreaseIfPositive (zero one : Γ) (zeroState positiveState : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  testZero tm one zeroState positiveState
  ifₜ state =ₜ some positiveState then
    decrementLeft tm zero one
  else
    pure ()

private theorem decreaseIfPositive_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (bits : List Bool) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (counterDigits zero one bits) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      decreaseIfPositive (tm := tm) zero one zeroState positiveState
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroState else positiveState),
          BiTape.segment StackTape.nil (counterDigits zero one (subtractDigits bits 1)) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 6 * bits.length + 6 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hbound⟩
  by_cases hz : binaryValue bits.reverse = 0
  · vcgen [decreaseIfPositive, testZero_spec (tm := tm) zero one hne zeroState positiveState
      hstates bits tail label origin initial.steps, Spec.branch_false_spec]
    all_goals simp_all [counterDigits, subtractDigits]
    all_goals lia
  · have hcarry := carryCount_le_length (bits.reverse.map Bool.not)
    vcgen [decreaseIfPositive, testZero_spec (tm := tm) zero one hne zeroState positiveState
      hstates bits tail label origin initial.steps,
      decrementLeft_spec (tm := tm) zero one hne bits (by lia) tail (some positiveState)
        origin (initial.steps + 2 * bits.length + 2)]
    all_goals simp_all [counterDigits, subtractDigits]
    all_goals lia

private noncomputable def indexedStep (zero one : Γ) (zeroState positiveState : tm.State)
    (near : Nat) (restore : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  onPrefixAtMark tm (onCounter tm
    (decreaseIfPositive zero one zeroState positiveState) near)
  tape ←ₜ some restore
  ifₜ state =ₜ some positiveState then
    moveₜ .Right
  else
    pure ()

private def stepMoves (digits source distance : Nat) : Nat :=
  8 * digits + 2 * source + 4 * distance + 16

private theorem indexedStep_spec (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (restore : Γ) (bits : List Bool) (near : List (List Γ)) (before after : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let count := if binaryValue bits.reverse = 0 then 0 else 1
    let result := counterDigits zero one (subtractDigits bits 1)
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.prepend before.reverse
          (counterLeft (counterDigits zero one bits) near)) (restore :: after) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      indexedStep (tm := tm) zero one zeroState positiveState near.length restore
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroState else positiveState),
          if count = 0 then
            BiTape.segment (StackTape.prepend before.reverse (counterLeft result near))
              (restore :: after) tail
          else BiTape.segment
            (StackTape.prepend (before ++ [restore]).reverse
              (counterLeft result near)) after tail⟩ ∧
        final.headPos = origin + count ∧ cost.steps ≤ elapsed +
          stepMoves bits.length before.length (regionSpan near) ⦄ := by
  dsimp only
  let result := counterDigits zero one (subtractDigits bits 1)
  let suffix := StackTape.prepend after (StackTape.cons none tail)
  let flag := some (if binaryValue bits.reverse = 0 then zeroState else positiveState)
  let bound := (6 * bits.length + 6) + bits.length + bits.length +
    2 * (near.map List.length).sum + 4 * near.length + 4
  have hv (place : ℤ) (steps : Nat) := onCounter_spec (tm := tm)
    (decreaseIfPositive zero one zeroState positiveState)
    (counterDigits zero one bits) result near before suffix suffix label flag
    (6 * bits.length + 6) (by
      intro position elapsed
      simpa [result, flag, counterDigits, Nat.add_assoc] using
        decreaseIfPositive_spec (tm := tm) zero one hne zeroState positiveState hstates bits
          (counterRight near before suffix) label position elapsed)
    place steps
  have hp := onPrefixAtMark_spec (tm := tm)
    (onCounter tm (decreaseIfPositive zero one zeroState positiveState) near.length)
    (counterLeft (counterDigits zero one bits) near) (counterLeft result near) (by simp)
    before suffix suffix label flag bound
    (by simpa [bound, result, counterDigits, Nat.add_assoc] using hv) origin elapsed
  vcgen [indexedStep, hp]
  all_goals
    by_cases hz : binaryValue bits.reverse = 0
    all_goals
      cases after
      all_goals simp_all [TMState.write, TMState.move, TMState.moveCost, BiTape.segment,
        BiTape.write, BiTape.moveRight, List.reverse_append, result, suffix, flag, bound,
        stepMoves, regionSpan]
      all_goals lia

private noncomputable def indexedBody (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (near : Nat) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  ifₜ tape =ₜ none then
    state ←ₜ zeroState
  else
    select symbols (fun symbol => .tapeIs (some symbol))
      (indexedStep zero one zeroState positiveState near)

private noncomputable def indexedLoop (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (near : Nat) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (state =ₜ some positiveState) do
    indexedBody symbols zero one zeroState positiveState near

private theorem indexedBody_nil_spec (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (near : Nat) (left tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left [] tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      indexedBody (tm := tm) symbols zero one zeroState positiveState near
    ⦃ fun _ cost final => final.config = ⟨some zeroState, BiTape.segment left [] tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hb⟩
  vcgen [indexedBody, Spec.branch_true_spec]
  refine ⟨by simp [hcfg], ?_⟩
  vcgen
  simp_all

private theorem indexedBody_cons_spec (symbols : List Γ)
    (hcover : ∀ symbol, symbol ∈ symbols) (zero one : Γ) (hne : zero ≠ one)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (restore : Γ) (bits : List Bool) (near : List (List Γ)) (before after : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let count := if binaryValue bits.reverse = 0 then 0 else 1
    let result := counterDigits zero one (subtractDigits bits 1)
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.prepend before.reverse
          (counterLeft (counterDigits zero one bits) near)) (restore :: after) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      indexedBody (tm := tm) symbols zero one zeroState positiveState near.length
    ⦃ fun _ cost final => final.config =
        ⟨some (if binaryValue bits.reverse = 0 then zeroState else positiveState),
          if count = 0 then
            BiTape.segment (StackTape.prepend before.reverse (counterLeft result near))
              (restore :: after) tail
          else BiTape.segment
            (StackTape.prepend (before ++ [restore]).reverse
              (counterLeft result near)) after tail⟩ ∧
        final.headPos = origin + count ∧ cost.steps ≤ elapsed +
          stepMoves bits.length before.length (regionSpan near) ⦄ := by
  dsimp only
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hb⟩
  vcgen [indexedBody, Spec.branch_false_spec]
  refine ⟨by simp [hcfg], ?_⟩
  vcgen [Spec.select_spec (tm := tm) symbols (fun symbol => .tapeIs (some symbol))
    (indexedStep zero one zeroState positiveState near.length) restore (hcover restore)]
  constructor
  · intro candidate
    simp [hcfg, eq_comm]
  · vcgen [indexedStep_spec (tm := tm) zero one hne zeroState positiveState hstates restore
      bits near before after tail label origin elapsed]
    all_goals simp_all

/--
This states where the indexed reader stops. The head reaches the requested source position
or its ending blank, and the binary counter records the unvisited part of the requested index.
-/
@[expose] def AtIndex (zero one : Γ) (zeroState : tm.State) (bits : List Bool)
    (near : List (List Γ)) (before input : List Γ) (tail : StackTape Γ) (origin : ℤ)
    (final : TMState tm) : Prop :=
  let visited := min (binaryValue bits.reverse) input.length
  final.config = ⟨some zeroState,
    BiTape.segment (StackTape.prepend (before ++ input.take visited).reverse
      (counterLeft (counterDigits zero one (subtractDigits bits visited)) near))
      (input.drop visited) tail⟩ ∧ final.headPos = origin + visited

private theorem indexedLoop_stopped_spec (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (near : Nat) (view : BiTape Γ) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some zeroState, view⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      indexedLoop (tm := tm) symbols zero one zeroState positiveState near
    ⦃ fun _ cost final => final.config = ⟨some zeroState, view⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed ⦄ := by
  unfold indexedLoop
  vcgen [Spec.while_false_spec]
  all_goals simp_all

private theorem subtractDigits_add (bits : List Bool) (first second : Nat) :
    subtractDigits (subtractDigits bits first) second = subtractDigits bits (first + second) := by
  induction second with
  | zero => rfl
  | succ second ih =>
    simp only [subtractDigits, ih]
    rfl

omit [DecidableEq Γ] [DecidableEq tm.State] in
private theorem atIndex_cons (zero one : Γ) (zeroState : tm.State) (bits : List Bool)
    (near : List (List Γ)) (before : List Γ) (symbol : Γ) (input : List Γ)
    (tail : StackTape Γ) (origin : ℤ) (final : TMState tm)
    (hz : binaryValue bits.reverse ≠ 0) :
    AtIndex zero one zeroState bits near before (symbol :: input) tail origin final ↔
      AtIndex zero one zeroState (subtractDigits bits 1) near (before ++ [symbol]) input
        tail (origin + 1) final := by
  have hi : min (binaryValue (subtractDigits bits 1).reverse) input.length + 1 =
      min (binaryValue bits.reverse) (symbol :: input).length := by
    rw [subtractDigits_value]
    simp only [List.length_cons]
    by_cases hsmall : binaryValue bits.reverse ≤ input.length + 1
    · rw [Nat.min_eq_left hsmall, Nat.min_eq_left (by lia)]
      lia
    · rw [Nat.min_eq_right (by lia), Nat.min_eq_right (by lia)]
  simp only [AtIndex, ← hi, List.take_succ_cons, List.drop_succ_cons,
    subtractDigits_add, List.append_assoc, Nat.add_comm 1]
  simp only [List.singleton_append, List.reverse_append, List.reverse_cons,
    List.singleton_append, List.append_assoc]
  simp only [Nat.cast_add, Nat.cast_one, Int.add_assoc, Int.add_comm]

private theorem indexedLoop_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (zeroState positiveState : tm.State)
    (hstates : zeroState ≠ positiveState) (bits : List Bool) (near : List (List Γ))
    (before input : List Γ) (tail : StackTape Γ) (size : Nat)
    (hsize : bits.length + before.length + input.length + regionSpan near + 4 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some positiveState,
        BiTape.segment (StackTape.prepend before.reverse
          (counterLeft (counterDigits zero one bits) near)) input tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      indexedLoop (tm := tm) symbols zero one zeroState positiveState near.length
    ⦃ fun _ cost final => AtIndex zero one zeroState bits near before input tail origin final ∧
        cost.steps ≤ elapsed + (input.length + 1) * (64 * size) ⦄ := by
  induction input generalizing bits before origin elapsed with
  | nil =>
    unfold indexedLoop
    vcgen [Spec.while_step_spec
      (loop := indexedLoop (tm := tm) symbols zero one zeroState positiveState near.length)
      (hloop := rfl), indexedBody_nil_spec (tm := tm) symbols zero one zeroState positiveState
      near.length (StackTape.prepend before.reverse
        (counterLeft (counterDigits zero one bits) near)) tail (some positiveState) origin elapsed,
      indexedLoop_stopped_spec (tm := tm) symbols zero one zeroState positiveState
      hstates near.length (BiTape.segment (StackTape.prepend before.reverse
        (counterLeft (counterDigits zero one bits) near)) [] tail) origin elapsed]
    all_goals simp_all [AtIndex]
    all_goals lia
  | cons symbol input ih =>
    let next := subtractDigits bits 1
    let view := BiTape.segment (StackTape.prepend before.reverse
      (counterLeft (counterDigits zero one bits) near)) (symbol :: input) tail
    have hstep := indexedBody_cons_spec (tm := tm) symbols hcover zero one hne
      zeroState positiveState hstates symbol bits near before input tail (some positiveState)
      origin elapsed
    have hb : stepMoves bits.length before.length (regionSpan near) ≤ 64 * size := by
      dsimp [stepMoves]
      lia
    by_cases hz : binaryValue bits.reverse = 0
    · have hdone := indexedLoop_stopped_spec (tm := tm) symbols zero one zeroState positiveState
        hstates near.length view origin
        (elapsed + stepMoves bits.length before.length (regionSpan near))
      simp only [AtIndex, hz, Nat.zero_min, List.take_zero, List.drop_zero, List.append_nil,
        subtractDigits_zero, Int.natCast_zero, Int.add_zero]
      unfold indexedLoop
      vcgen [Spec.while_step_spec
        (loop := indexedLoop (tm := tm) symbols zero one zeroState positiveState near.length)
        (hloop := rfl), hstep, hdone]
      all_goals simp only [hz, ite_true, subtractDigits] at *
      all_goals simp_all [view]
      all_goals lia
    · have hr := ih next (before ++ [symbol]) (by
        simp only [next, subtractDigits_length, List.length_append, List.length_singleton]
        simp only [List.length_cons] at hsize
        lia) (origin + 1) (elapsed + 64 * size)
      simp only [atIndex_cons zero one zeroState bits near before symbol input tail origin _ hz]
      unfold indexedLoop
      vcgen [Spec.while_step_spec
        (loop := indexedLoop (tm := tm) symbols zero one zeroState positiveState near.length)
        (hloop := rfl), hstep, hr]
      all_goals simp_all [next]
      all_goals lia

/--
This template finds the position recorded by a binary counter farther left. It preserves the
source word and stops at its ending blank when the requested position lies beyond the word.
The counter is decreased once for each source symbol crossed.
-/
noncomputable def seekCounterIndex (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (near : Nat) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ positiveState
  indexedLoop symbols zero one zeroState positiveState near

/-- The indexed reader preserves its source and has a quadratic bound on head moves. -/
@[spec] theorem seekCounterIndex_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (zeroState positiveState : tm.State)
    (hstates : zeroState ≠ positiveState) (bits : List Bool) (near : List (List Γ))
    (before input : List Γ) (tail : StackTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    let size := bits.length + before.length + input.length + regionSpan near + 4
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.prepend before.reverse
          (counterLeft (counterDigits zero one bits) near)) input tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      seekCounterIndex tm symbols zero one zeroState positiveState near.length
    ⦃ fun _ cost final => AtIndex zero one zeroState bits near before input tail origin final ∧
        cost.steps ≤ elapsed + 64 * size ^ 2 ⦄ := by
  dsimp only
  let size := bits.length + before.length + input.length + regionSpan near + 4
  have ht : (input.length + 1) * (64 * size) ≤ 64 * size ^ 2 := by
    have hinput : input.length + 1 ≤ size := by dsimp [size]; lia
    calc
      _ ≤ size * (64 * size) := Nat.mul_le_mul_right _ hinput
      _ = _ := by ring
  vcgen [seekCounterIndex, indexedLoop_spec (tm := tm) symbols hcover zero one hne
    zeroState positiveState hstates bits near before input tail size le_rfl origin elapsed]
  all_goals simp_all
  all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
