/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.PositionIteration
public import Algolean.Complexity.Reductions.NPtoSAT.InitialComparison
public import Algolean.Complexity.Reductions.NPtoSAT.InitialSource
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.LiteralWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.CertificateChoices
public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Initial
public import Algolean.Complexity.Reductions.NPtoSAT.InitialCells
public import Algolean.Complexity.Reductions.NPtoSAT.InitialWords
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.MarkedUnaryCounting
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.IndexedReading
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.CounterNormalization
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryComparison
import Mathlib.Data.List.TakeWhile
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Writing the initial tape requirements

* `writeInitialClauses` writes clauses placing the verifier's head at the start of its input.
  It fixes the original input symbols, the separator, and the blank cells on both sides, and
  links each certificate cell to the corresponding certificate choice.
* `writeInitialClauses_spec` states the exact appended formula and proves that the input,
  bounds, and head position are restored.
* `timeBound` bounds the head moves by a polynomial in the lengths of the tape words and output.

The program reads input symbols from the preserved input and positions from the bound words.
The verifier and its initial state are fixed when constructing the containing machine.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.InitialWriting

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT Computability
open NPToSAT.Computation NPToSAT.Computation.HeadChoices NPToSAT.Computation.LiteralWriting
open PositionIteration
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def countPosition (zero one tick : Γ) : Prog (TMQuery tm) Unit :=
  countEarlierAtMark tm zero one tick 2 5

private theorem countPosition_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat) (hsize : choice.size ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      countPosition (tm := tm) zero one tick
    ⦃ fun _ cost final => AtPairCounter tick choice input output
        (counterWord zero one choice.firstPosition.1) label origin final ∧
        cost.steps ≤ elapsed + 128 * (size + 16) ^ 2 ⦄ := by
  let before := [List.replicate choice.time.2 tick, List.replicate choice.time.1 tick]
  let between := [List.replicate choice.secondPosition.2 tick,
    List.replicate choice.secondPosition.1 tick, List.replicate choice.firstState.2 tick,
    List.replicate choice.firstState.1 tick, List.replicate choice.firstPosition.2 tick]
  have hc := countEarlierAtMark_spec (tm := tm) zero one hne tick 0 choice.firstPosition.1
    before between (List.replicate choice.secondState.1 tick) (choice.rightWords tick input)
    output label origin elapsed
  have hb : earlierCountMoves 0 choice.firstPosition.1 before between
      (List.replicate choice.secondState.1 tick) ≤ 128 * (size + 16) ^ 2 := by
    have hbound : 0 + choice.firstPosition.1 + regionSpan before + regionSpan between +
        (List.replicate choice.secondState.1 tick).length + 4 ≤ size + 16 := by
      dsimp [before, between, regionSpan, ActiveChoices.size] at *
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        List.length_replicate] at *
      lia
    exact (earlierCountMoves_le _ _ _ _ _).trans
      (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hbound 2))
  norm_num only [before, between, List.length_cons, List.length_nil] at hc
  vcgen [countPosition, hc]
  all_goals simp_all [AtPair, AtPairCounter, pairTape, ActiveChoices.leftWords, markedUnaryTape]
  all_goals lia

private noncomputable def subtractEarlierAtMark (zero one tick : Γ)
    (zeroState positiveState : tm.State) (before between : Nat) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (onCounter tm
    (subtractBlocks tm zero one tick [] zeroState positiveState positiveState before) between)

private theorem subtractEarlierAtMark_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (bits : List Bool) (count : Nat) (before between : List (List Γ)) (current : List Γ)
    (parts : List (List Γ)) (output : List Γ) (origin : ℤ) (elapsed : Nat) :
    let near := between ++ List.replicate count tick :: before
    ⦃ fun cost initial => initial.config = ⟨some positiveState,
        markedUnaryTape near current parts output (counterDigits zero one bits)⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      subtractEarlierAtMark (tm := tm) zero one tick zeroState positiveState
        before.length between.length
    ⦃ fun _ cost final => final.config = ⟨some positiveState,
        markedUnaryTape near current parts output
          (counterDigits zero one (subtractDigits bits count))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          earlierCountMoves bits.length count before between current ⦄ := by
  dsimp only
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let source := List.replicate count tick
  let left := counterLeft (counterDigits zero one bits) before
  let resultLeft := counterLeft (counterDigits zero one (subtractDigits bits count)) before
  let countBound := subtractBlocksMoves 1 bits.length count (regionSpan before)
  have ha (place : ℤ) (steps : Nat) := subtractBlocks_spec (tm := tm) zero one hne tick []
    zeroState positiveState positiveState hstates bits count before
    (counterRight between current tail) place steps
  have hv := onEarlierWord_spec (tm := tm)
    (subtractBlocks tm zero one tick [] zeroState positiveState positiveState before.length)
    left.tail resultLeft.tail source between current tail tail
    (some positiveState) (some positiveState) countBound
    (by intro place steps; simpa [left, resultLeft, source, countBound] using ha place steps)
  have hp := onPrefixAtMark_spec (tm := tm)
    (onCounter tm (subtractBlocks tm zero one tick [] zeroState positiveState positiveState
      before.length) between.length)
    (counterLeft (counterDigits zero one bits) (between ++ source :: before))
    (counterLeft (counterDigits zero one (subtractDigits bits count)) (between ++ source :: before))
    (by simp) current tail tail (some positiveState) (some positiveState)
    (countBound + 2 * source.length + 2 * (between.map List.length).sum +
      4 * between.length + 4)
    (by intro place steps; simpa [left, resultLeft, Nat.add_assoc] using hv place steps)
    origin elapsed
  have hcost : elapsed + 2 * current.length + 2 + (countBound + 2 * count +
      2 * (between.map List.length).sum + 4 * between.length + 4) =
        elapsed + earlierCountMoves bits.length count before between current := by
    dsimp [earlierCountMoves, countBound, subtractBlocksMoves, countBlocksMoves]
    ring
  simpa only [subtractEarlierAtMark, markedUnaryTape, tail, source, List.length_replicate,
    hcost] using hp

private noncomputable def subtractTime (zero one tick : Γ) (zeroState positiveState : tm.State) :
    Prog (TMQuery tm) Unit :=
  subtractEarlierAtMark zero one tick zeroState positiveState 1 6

private theorem subtractTime_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (choice : ActiveChoices) (input output : List Γ) (bits : List Bool) (size : Nat)
    (hsize : choice.size ≤ size) (hbits : bits.length ≤ size) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice input output (counterDigits zero one bits)
        (some positiveState) origin current ∧ cost.steps ≤ elapsed ⦄
      subtractTime (tm := tm) zero one tick zeroState positiveState
    ⦃ fun _ cost final => AtPairCounter tick choice input output
        (counterDigits zero one (subtractDigits bits choice.time.2))
        (some positiveState) origin final ∧ cost.steps ≤ elapsed + 512 * (size + 16) ^ 2 ⦄ := by
  let before := [List.replicate choice.time.1 tick]
  let between := [List.replicate choice.secondPosition.2 tick,
    List.replicate choice.secondPosition.1 tick, List.replicate choice.firstState.2 tick,
    List.replicate choice.firstState.1 tick, List.replicate choice.firstPosition.2 tick,
    List.replicate choice.firstPosition.1 tick]
  have hc := subtractEarlierAtMark_spec (tm := tm) zero one hne tick zeroState positiveState
    hstates bits choice.time.2 before between (List.replicate choice.secondState.1 tick)
    (choice.rightWords tick input) output origin elapsed
  have hb : earlierCountMoves bits.length choice.time.2 before between
      (List.replicate choice.secondState.1 tick) ≤ 512 * (size + 16) ^ 2 := by
    calc
      _ ≤ 128 * (bits.length + choice.time.2 + regionSpan before + regionSpan between +
          (List.replicate choice.secondState.1 tick).length + 4) ^ 2 := earlierCountMoves_le ..
      _ ≤ 128 * (2 * (size + 16)) ^ 2 := by
        gcongr
        dsimp [before, between, regionSpan, ActiveChoices.size] at *
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          List.length_replicate] at *
        lia
      _ = _ := by ring
  norm_num only [before, between, List.length_cons, List.length_nil] at hc
  vcgen [subtractTime, hc]
  all_goals simp_all [AtPairCounter, pairTape, ActiveChoices.leftWords, markedUnaryTape]
  all_goals lia

private noncomputable def prepareIndex (zero one tick : Γ) (zeroState positiveState : tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  countPosition zero one tick
  subtractTime zero one tick zeroState positiveState

private def indexBits (choice : ActiveChoices) : List Bool :=
  subtractDigits (encodingNatBool.encode choice.firstPosition.1).reverse choice.time.2

private theorem prepareIndex_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (zeroState positiveState : tm.State) (hstates : zeroState ≠ positiveState)
    (choice : ActiveChoices) (input output : List Γ) (size : Nat) (hsize : choice.size ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output (some positiveState) origin current ∧
        cost.steps ≤ elapsed ⦄
      prepareIndex (tm := tm) zero one tick zeroState positiveState
    ⦃ fun _ cost final => AtPairCounter tick choice input output
        (counterDigits zero one (indexBits choice)) (some positiveState) origin final ∧
        cost.steps ≤ elapsed + 640 * (size + 16) ^ 2 ⦄ := by
  have hp : (encodingNatBool.encode choice.firstPosition.1).reverse.length ≤ size := by
    have hs : choice.firstPosition.1.size ≤ choice.firstPosition.1 :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [List.length_reverse, length_encodingNatBool]
    dsimp [ActiveChoices.size] at hsize
    lia
  have hs := subtractTime_spec (tm := tm) zero one hne tick zeroState positiveState hstates
    choice input output (encodingNatBool.encode choice.firstPosition.1).reverse size hsize hp origin
    (elapsed + 128 * (size + 16) ^ 2)
  vcgen [prepareIndex, countPosition_spec (tm := tm) zero one hne tick choice input output size
    hsize (some positiveState) origin elapsed, hs]
  all_goals simp_all [AtPairCounter, counterDigits, counterWord, indexBits]
  all_goals lia

private theorem indexBits_value (choice : ActiveChoices) :
    binaryValue (indexBits choice).reverse = choice.firstPosition.1 - choice.time.2 := by
  simp [indexBits, subtractDigits_value]

private def inputNear (tick : Γ) (choice : ActiveChoices) : List (List Γ) :=
  List.replicate choice.secondState.2 tick :: List.replicate choice.secondState.1 tick ::
    choice.leftWords tick

private def inputView (tick : Γ) (choice : ActiveChoices) (counter before after output : List Γ) :
    BiTape Γ :=
  BiTape.segment (StackTape.prepend before.reverse (counterLeft counter (inputNear tick choice)))
    after (StackTape.mapSome output)

private def toInput : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  nextRegion tm
  moveₜ .Right

private theorem toInput_spec (tick : Γ) (choice : ActiveChoices)
    (counter input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice (tick :: input) output counter label origin
        current ∧ cost.steps ≤ elapsed ⦄
      toInput (tm := tm)
    ⦃ fun _ cost final => final.config =
        ⟨label, inputView tick choice counter [tick] input output⟩ ∧
        final.headPos = origin + choice.secondState.2 + 3 ∧
        cost.steps ≤ elapsed + choice.secondState.2 + 3 ⦄ := by
  let left := StackTape.prepend (List.replicate choice.secondState.1 tick).reverse
    (counterLeft counter (choice.leftWords tick))
  vcgen [toInput, nextRegion_le_spec (tm := tm) (StackTape.cons none left)
    (List.replicate choice.secondState.2 tick) (tick :: input) (StackTape.mapSome output)
    label (origin + 1) (elapsed + 1)]
  all_goals simp_all [AtPairCounter, pairTape, markedUnaryTape, ActiveChoices.rightWords,
    inputView, inputNear, left, counterLeft, TMState.move, TMState.moveCost]
  all_goals lia

private def fromInput : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  previousRegion tm
  moveₜ .Left

private theorem fromInput_spec (tick : Γ) (choice : ActiveChoices)
    (counter before after output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, inputView tick choice counter (tick :: before) after output⟩ ∧
        current.headPos = origin + choice.secondState.2 + 3 + before.length ∧
        cost.steps ≤ elapsed ⦄
      fromInput (tm := tm)
    ⦃ fun _ cost final => AtPairCounter tick choice (tick :: (before ++ after)) output counter
        label origin final ∧ cost.steps ≤ elapsed + before.length + choice.secondState.2 + 7 ⦄ := by
  let near := inputNear tick choice
  let left := StackTape.prepend (List.replicate choice.secondState.1 tick).reverse
    (counterLeft counter (choice.leftWords tick))
  vcgen [fromInput, seekLeftEnd_le_spec (tm := tm) (counterLeft counter near).tail
    (StackTape.mapSome output) (tick :: before).reverse after label
    (origin + choice.secondState.2 + 3 + before.length) elapsed,
    previousRegion_le_spec (tm := tm) left (List.replicate choice.secondState.2 tick)
      (tick :: (before ++ after)) (StackTape.mapSome output) label
      (origin + choice.secondState.2 + 2) (elapsed + before.length + 3)]
  all_goals simp_all [AtPairCounter, pairTape, markedUnaryTape, ActiveChoices.rightWords,
    inputView, inputNear, near, left, counterLeft, TMState.move, TMState.moveCost]
  all_goals lia

private def recordHead (symbols : List Γ) (record : Option Γ → tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  ifₜ tape =ₜ none then
    state ←ₜ record none
  else
    select symbols (fun symbol => .tapeIs (some symbol))
      (fun symbol => do [TMQuery tm] state ←ₜ record (some symbol))

private theorem recordHead_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (record : Option Γ → tm.State) (view : BiTape Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      recordHead (tm := tm) symbols record
    ⦃ fun _ cost final => final.config = ⟨some (record view.head), view⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hb⟩
  cases hhead : view.head with
  | none =>
    vcgen [recordHead, Spec.branch_true_spec]
    refine ⟨by simp [hcfg, hhead], ?_⟩
    vcgen
    simp_all
  | some symbol =>
    vcgen [recordHead, Spec.branch_false_spec]
    refine ⟨by simp [hcfg, hhead], ?_⟩
    vcgen [Spec.select_spec (tm := tm) symbols (fun chosen => .tapeIs (some chosen))
      (fun chosen => do [TMQuery tm] state ←ₜ record (some chosen)) symbol (hcover symbol)]
    constructor
    · intro chosen
      simp [hcfg, hhead, eq_comm]
    · vcgen
      simp_all

private noncomputable def readInputIndex (symbols : List Γ) (zero one : Γ)
    (zeroState positiveState : tm.State) (record : Option Γ → tm.State) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  toInput
  seekCounterIndex tm symbols zero one zeroState positiveState 10
  recordHead symbols record
  fromInput

private theorem readInputIndex_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (zeroState positiveState : tm.State)
    (hstates : zeroState ≠ positiveState) (record : Option Γ → tm.State)
    (choice : ActiveChoices) (bits : List Bool) (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length + bits.length ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let index := binaryValue bits.reverse
    let visited := min index input.length
    ⦃ fun cost current => AtPairCounter tick choice (tick :: input) output
        (counterDigits zero one bits) label origin current ∧ cost.steps ≤ elapsed ⦄
      readInputIndex (tm := tm) symbols zero one zeroState positiveState record
    ⦃ fun _ cost final => AtPairCounter tick choice (tick :: input) output
        (counterDigits zero one (subtractDigits bits visited)) (some (record input[index]?))
        origin final ∧ cost.steps ≤ elapsed + 1024 * (size + 16) ^ 2 ⦄ := by
  dsimp only
  let index := binaryValue bits.reverse
  let visited := min index input.length
  let result := counterDigits zero one (subtractDigits bits visited)
  let near := inputNear tick choice
  let cap := bits.length + 1 + input.length + regionSpan near + 4
  let head := (input.drop visited).head?
  have hhead : head = input[index]? := by
    dsimp only [head, visited]
    rw [← List.drop_eq_drop_min]
    simp
  have hr := seekCounterIndex_spec (tm := tm) symbols hcover zero one hne zeroState positiveState
    hstates bits near [tick] input (StackTape.mapSome output) label
    (origin + choice.secondState.2 + 3) (elapsed + choice.secondState.2 + 3)
  have hrecord := recordHead_spec (tm := tm) symbols hcover record
    (inputView tick choice result (tick :: input.take visited) (input.drop visited) output)
    (some zeroState) (origin + choice.secondState.2 + 3 + visited)
    (elapsed + choice.secondState.2 + 3 + 64 * cap ^ 2)
  have hreturn := fromInput_spec (tm := tm) tick choice result (input.take visited)
    (input.drop visited) output (some (record head)) origin
    (elapsed + choice.secondState.2 + 3 + 64 * cap ^ 2)
  have hcap : cap ≤ size + 15 := by
    dsimp [cap, near, inputNear, regionSpan, ActiveChoices.leftWords, ActiveChoices.size] at *
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_replicate] at *
    lia
  have hvisited : visited ≤ input.length := Nat.min_le_right ..
  have ht : 2 * choice.secondState.2 + visited + 10 + 64 * cap ^ 2 ≤
      1024 * (size + 16) ^ 2 := by
    have hpow := Nat.pow_le_pow_left hcap 2
    have hlinear : size + 16 ≤ (size + 16) ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_self (size + 16)
    dsimp [ActiveChoices.size] at hsize
    ring_nf at hpow hlinear ⊢
    lia
  norm_num only [near, inputNear, ActiveChoices.leftWords, List.length_cons, List.length_nil]
    at hr
  vcgen [readInputIndex, toInput_spec (tm := tm) tick choice (counterDigits zero one bits)
    input output label origin elapsed, hr, hrecord, hreturn]
  all_goals
    simp_all [AtPairCounter, AtIndex, inputView, inputNear, ActiveChoices.leftWords, regionSpan,
      near, result, cap, visited, index, List.take_append_drop, hhead, head]
  all_goals lia


private def atCounter (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit :=
  onPrefixAtMark tm (onCounter tm action 8)

private theorem atCounter_spec (tick : Γ) (choice : ActiveChoices)
    (action : Prog (TMQuery tm) Unit) (input output counter resultCounter written : List Γ)
    (label result : Option tm.State) (bound : Nat)
    (haction : ∀ (place : ℤ) (steps : Nat),
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil counter
          (counterRight (choice.leftWords tick) (List.replicate choice.secondState.1 tick)
            (StackTape.separateWords (choice.rightWords tick input) (StackTape.mapSome output)))⟩ ∧
          current.headPos = place ∧ cost.steps ≤ steps ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment StackTape.nil resultCounter
          (counterRight (choice.leftWords tick) (List.replicate choice.secondState.1 tick)
            (StackTape.separateWords (choice.rightWords tick input)
              (StackTape.mapSome (output ++ written))))⟩ ∧
          final.headPos = place + counter.length - resultCounter.length ∧
          cost.steps ≤ steps + bound ⦄)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice input output counter label origin current ∧
        cost.steps ≤ elapsed ⦄
      atCounter action
    ⦃ fun _ cost final => AtPairCounter tick choice input (output ++ written) resultCounter
        result origin final ∧ cost.steps ≤ elapsed + bound + counter.length +
          resultCounter.length + 2 * choice.size + 38 ⦄ := by
  let near := choice.leftWords tick
  let crossed := List.replicate choice.secondState.1 tick
  let tail := StackTape.separateWords (choice.rightWords tick input) (StackTape.mapSome output)
  let resultTail := StackTape.separateWords (choice.rightWords tick input)
    (StackTape.mapSome (output ++ written))
  have hv := onCounter_spec (tm := tm) action counter resultCounter near crossed tail resultTail
    label result bound haction
  have hp := onPrefixAtMark_spec (tm := tm) (onCounter tm action 8)
    (counterLeft counter near) (counterLeft resultCounter near) (by simp) crossed tail resultTail
    label result (bound + counter.length + resultCounter.length +
      2 * (near.map List.length).sum + 4 * near.length + 4)
    (by
      intro place steps
      simpa [near, ActiveChoices.leftWords, Nat.add_assoc] using hv place steps)
    origin elapsed
  have hb : 2 * crossed.length + 2 + (bound + counter.length + resultCounter.length +
      2 * (near.map List.length).sum + 4 * near.length + 4) ≤
      bound + counter.length + resultCounter.length + 2 * choice.size + 38 := by
    dsimp [crossed, near, ActiveChoices.leftWords, ActiveChoices.size]
    simp only [List.length_replicate, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    lia
  vcgen [atCounter, hp]
  all_goals simp_all [AtPairCounter, pairTape, markedUnaryTape, near, crossed, tail, resultTail]
  all_goals lia

private def clearIndex : Prog (TMQuery tm) Unit := atCounter (eraseRight tm)

private theorem clearIndex_spec (zero one tick : Γ) (choice : ActiveChoices)
    (bits : List Bool) (input output : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice input output (counterDigits zero one bits)
        label origin current ∧ cost.steps ≤ elapsed ⦄
      clearIndex (tm := tm)
    ⦃ fun _ cost final => AtPair tick choice input output label origin final ∧
        cost.steps ≤ elapsed + 2 * bits.length + 2 * choice.size + 38 ⦄ := by
  have hp := atCounter_spec tick choice (eraseRight tm) input output
    (counterDigits zero one bits) [] [] label label bits.length (by
      intro place steps
      simpa [counterDigits] using eraseRight_segment_le_spec (tm := tm) StackTape.nil
        (counterRight (choice.leftWords tick) (List.replicate choice.secondState.1 tick)
          (StackTape.separateWords (choice.rightWords tick input) (StackTape.mapSome output)))
        (counterDigits zero one bits) label place steps) origin elapsed
  simpa [clearIndex, AtPair, AtPairCounter, counterDigits, two_mul, Nat.add_assoc] using hp



variable [Encodable Γ]

private def certificateWord (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (index : Fin problem.certificateLength) (symbol : Γ) : List Γ :=
  (literalPrefix (.neg (Variable.name (.certificate index symbol)))).flatMap code


private def certificateLiteral (zero one : Γ) (code : CodeSymbol → List Γ)
    (symbol : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  decrementLeft tm zero one
  normalizeCounter tm zero
  CertificateChoices.writeCertificateLiteralFromCounter tm zero one code 11 (.neg symbol)
  eraseRight tm

private theorem canonicalCertificate_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (problem : BoundedVerification Γ) (position : Fin problem.certificateLength) (symbol : Γ)
    (parts : List (List Γ)) (hparts : parts.length = 11) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (counterWord zero one position.val)
        (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      CertificateChoices.writeCertificateLiteralFromCounter tm zero one code 11 (.neg symbol)
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil
        (counterWord zero one position.val) (StackTape.separateWords parts
          (StackTape.mapSome (output ++ certificateWord code problem position symbol)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          CertificateChoices.literalMoves width position.val.size (regionSpan parts)
            output.length (Encodable.encode symbol).size ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hb⟩
  have hs := CertificateChoices.writeCertificateLiteralFromCounter_spec (tm := tm)
    zero one hne code width hwidth problem position (.neg symbol) parts output label origin
    initial.steps
  rw [hparts] at hs
  vcgen [hs]
  all_goals simp_all [Literal.rename, certificateWord]

private theorem certificateLiteral_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (codeWidth : Nat)
    (hcode : ∀ symbol, (code symbol).length = codeWidth)
    (problem : BoundedVerification Γ) (position : Fin problem.certificateLength) (symbol : Γ)
    (bits : List Bool) (hvalue : binaryValue bits.reverse = position.val + 1)
    (parts : List (List Γ)) (hparts : parts.length = 11) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let written := certificateWord code problem position symbol
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil
        (counterDigits zero one bits) (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      certificateLiteral (tm := tm) zero one code symbol
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment StackTape.nil []
        (StackTape.separateWords parts (StackTape.mapSome (output ++ written)))⟩ ∧
        final.headPos = origin + bits.length ∧ cost.steps ≤ elapsed + 6 * bits.length + 4 +
          CertificateChoices.literalMoves codeWidth position.val.size (regionSpan parts)
            output.length (Encodable.encode symbol).size ⦄ := by
  dsimp only
  let reduced := (decrementBits bits.reverse).reverse
  have hpositive : 0 < binaryValue bits.reverse := by lia
  have hlength : reduced.length = bits.length := by simp [reduced, length_decrementBits]
  have hnumber : binaryValue reduced.reverse = position.val := by
    have hd := binaryValue_decrementBits bits.reverse hpositive
    simp only [reduced, List.reverse_reverse]
    lia
  have hcanonical : position.val.size ≤ bits.length := by
    have ht := congrArg List.length (trimCounterBits reduced)
    have hb := List.length_dropWhile_le (fun bit : Bool => !bit) reduced
    simp only [List.length_reverse, length_encodingNatBool, hnumber, hlength] at ht hb
    lia
  have hcarry := carryCount_le_length (bits.reverse.map Bool.not)
  let moves := CertificateChoices.literalMoves codeWidth position.val.size (regionSpan parts)
    output.length (Encodable.encode symbol).size
  let middle := elapsed + 5 * bits.length + 4
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hb⟩
  vcgen [certificateLiteral,
    decrementLeft_spec (tm := tm) zero one hne bits hpositive
      (StackTape.separateWords parts (StackTape.mapSome output)) label origin initial.steps,
    normalizeCounter_spec (tm := tm) zero one hne reduced
      (StackTape.separateWords parts (StackTape.mapSome output)) label origin
      (elapsed + 4 * bits.length + 4),
    canonicalCertificate_spec (tm := tm) zero one hne code codeWidth hcode problem position
      symbol parts hparts output label (origin + bits.length - position.val.size) middle,
    eraseRight_segment_le_spec (tm := tm) StackTape.nil
      (StackTape.separateWords parts
        (StackTape.mapSome (output ++ certificateWord code problem position symbol)))
      (counterWord zero one position.val) label (origin + bits.length - position.val.size)
      (middle + moves)]
  all_goals simp_all [counterDigits, reduced, middle, moves, counterWord, length_decrementBits]
  all_goals lia


private def cellWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbol : Option (TapeSymbol Γ)) : List Γ :=
  tapeLiteralWord code choice true false false symbol ++ code (.inr 3) ++ code (.inr 4)

private def writeCell (zero one tick : Γ) (code : CodeSymbol → List Γ)
    (symbol : Option (TapeSymbol Γ)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeTapeLiteral tm zero one tick code true false false symbol
  appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2

private theorem writeCell_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (symbol : Option (TapeSymbol Γ)) (input output : List Γ)
    (size : Nat) (hsize : choice.size + input.length +
      (output ++ cellWord code choice symbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeCell (tm := tm) zero one tick code symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ cellWord code choice symbol) label origin final ∧
        cost.steps ≤ elapsed + 5 * markedNumberBudget width size ⦄ := by
  let first := output ++ tapeLiteralWord code choice true false false symbol
  have hs : choice.size + input.length + first.length + 32 ≤ size := by
    simp only [cellWord, first, List.length_append] at hsize ⊢
    lia
  have hl := writeTapeLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
    true false false symbol input output size hs label origin elapsed
  have he := appendPart_spec (tm := tm) (code (.inr 3) ++ code (.inr 4)) tick choice
    input first width size (by simpa [cellWord, first, List.append_assoc] using hsize)
    label origin (elapsed + 4 * markedNumberBudget width size)
  vcgen [writeCell, hl, he]
  all_goals simp_all [cellWord, first, tapeLiteralTime, List.append_assoc]
  all_goals lia

private noncomputable def testIndex (one : Γ) (positiveState zeroState : tm.State) :
    Prog (TMQuery tm) Unit :=
  atCounter (testZeroAndClear one positiveState zeroState)

omit [Encodable Γ] in
private theorem testIndex_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (positiveState zeroState : tm.State) (hstates : positiveState ≠ zeroState)
    (choice : ActiveChoices) (bits : List Bool) (input output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice input output
        (counterDigits zero one bits) label origin current ∧ cost.steps ≤ elapsed ⦄
      testIndex (tm := tm) one positiveState zeroState
    ⦃ fun _ cost final => AtPair tick choice input output
        (some (if binaryValue bits.reverse = 0 then zeroState else positiveState)) origin final ∧
        cost.steps ≤ elapsed + 4 * bits.length + 2 * choice.size + 40 ⦄ := by
  have hs := atCounter_spec tick choice (testZeroAndClear one positiveState zeroState)
    input output (counterDigits zero one bits) [] [] label
    (some (if binaryValue bits.reverse = 0 then zeroState else positiveState))
    (3 * bits.length + 2) (by
      intro place steps
      simpa [counterDigits, Nat.add_assoc] using
        testZeroAndClear_spec (tm := tm) zero one hne positiveState zeroState hstates bits _
          label place steps) origin elapsed
  vcgen [testIndex, hs]
  all_goals simp_all [AtPairCounter, AtPair, counterDigits]
  all_goals lia


private def writeCertificate (zero one : Γ) (code : CodeSymbol → List Γ)
    (symbol : Γ) : Prog (TMQuery tm) Unit :=
  atCounter (certificateLiteral zero one code symbol)

private theorem writeCertificate_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (problem : BoundedVerification Γ) (index : Fin problem.certificateLength) (symbol : Γ)
    (choice : ActiveChoices) (bits : List Bool) (hvalue : binaryValue bits.reverse = index.val + 1)
    (input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let distance := choice.size + input.length + 11
    ⦃ fun cost current => AtPairCounter tick choice input output
        (counterDigits zero one bits) label origin current ∧ cost.steps ≤ elapsed ⦄
      writeCertificate (tm := tm) zero one code symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ certificateWord code problem index symbol) label origin final ∧
        cost.steps ≤ elapsed + 7 * bits.length + 2 * choice.size + 42 +
          CertificateChoices.literalMoves width index.val.size distance output.length
            (Encodable.encode symbol).size ⦄ := by
  dsimp only
  let near := choice.leftWords tick
  let current := List.replicate choice.secondState.1 tick
  let parts := near.reverse ++ [current] ++ choice.rightWords tick input
  have hparts : parts.length = 11 := by
    simp [parts, near, ActiveChoices.leftWords, ActiveChoices.rightWords]
  have hspan : regionSpan parts = choice.size + input.length + 11 := by
    have hs := choice.source_span tick input
    simp [parts, regionSpan, List.map_append, List.sum_append, near, current] at *
    lia
  have ha (place : ℤ) (steps : Nat) := certificateLiteral_spec (tm := tm) zero one hne code
    width hwidth problem index symbol bits hvalue parts hparts output label place steps
  have hs := atCounter_spec tick choice (certificateLiteral zero one code symbol) input output
    (counterDigits zero one bits) [] (certificateWord code problem index symbol) label label
    (6 * bits.length + 4 + CertificateChoices.literalMoves width index.val.size
      (regionSpan parts) output.length (Encodable.encode symbol).size) (by
      intro place steps
      simpa [parts, counterRight, near, current, StackTape.separateWords_append,
        certificateWord, counterDigits, Nat.add_assoc] using ha place steps) origin elapsed
  vcgen [writeCertificate, hs]
  all_goals simp_all [AtPairCounter, AtPair, counterDigits, Nat.add_assoc]
  all_goals lia


private def remainingBits (choice : ActiveChoices) (input : List Γ) : List Bool :=
  subtractDigits (indexBits choice)
    (min (binaryValue (indexBits choice).reverse) input.length)

private theorem indexBits_length (choice : ActiveChoices) :
    (indexBits choice).length ≤ choice.firstPosition.1 := by
  have hs := Nat.size_le.mpr (Nat.lt_two_pow_self (n := choice.firstPosition.1))
  simpa [indexBits] using hs

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem remainingBits_length (choice : ActiveChoices) (input : List Γ) :
    (remainingBits choice input).length ≤ choice.firstPosition.1 := by
  simpa [remainingBits] using indexBits_length choice

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem remainingBits_value (choice : ActiveChoices) (input : List Γ) :
    binaryValue (remainingBits choice input).reverse =
      choice.firstPosition.1 - choice.time.2 - input.length := by
  simp only [remainingBits, subtractDigits_value, indexBits_value]
  by_cases h : choice.firstPosition.1 - choice.time.2 ≤ input.length
  · rw [Nat.min_eq_left h]
    lia
  · rw [Nat.min_eq_right (by lia)]

private def implicationWord (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (index : Fin problem.certificateLength) (choice : ActiveChoices) (symbol : Γ) : List Γ :=
  certificateWord code problem index symbol ++ cellWord code choice (some (.inl symbol))

private noncomputable def writeCertificateCase (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State)
    (symbol : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ positive
  prepareIndex zero one tick greater positive
  readInputIndex symbols zero one greater positive record
  writeCertificate zero one code symbol
  writeCell zero one tick code (some (.inl symbol))
  state ←ₜ greater

private def certificateMoves (width size symbolSize : Nat) : Nat :=
  262144 * (width + 1) * (symbolSize + 1) * (size + 16) ^ 2

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
/--
The literal writer has a quadratic move bound when its input words and output fit the size bound.
-/
private theorem initial_literal_moves_le (width size symbol digits distance output : Nat)
    (hdigits : digits ≤ size) (hdistance : distance ≤ size + 11) (houtput : output ≤ size) :
    CertificateChoices.literalMoves width digits distance output symbol ≤
      4096 * (width + 1) * (symbol + 1) * (size + 16) ^ 2 := by
  calc
    _ ≤ CertificateChoices.literalMoves width size (size + 11) size symbol := by
      dsimp [CertificateChoices.literalMoves, lengthHeaderMoves, copyBitsMoves]
      gcongr
    _ ≤ _ := by
      dsimp [CertificateChoices.literalMoves, lengthHeaderMoves, copyBitsMoves]
      ring_nf
      lia

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
/--
This bounds writing one certificate implication, including reading its position from the input.
-/
private theorem initial_certificate_moves_le
    (width size symbol first digits index distance output : Nat)
    (hfirst : first ≤ size) (hdigits : digits ≤ size) (hindex : index ≤ size)
    (hdistance : distance ≤ size + 11) (houtput : output ≤ size) :
    640 * (size + 16) ^ 2 + 1024 * (2 * size + 16) ^ 2 +
      7 * digits + 2 * first + 42 +
        CertificateChoices.literalMoves width index distance output symbol +
      5 * markedNumberBudget width size ≤
        262144 * (width + 1) * (symbol + 1) * (size + 16) ^ 2 := by
  have hl := initial_literal_moves_le width size symbol index distance output
    hindex hdistance houtput
  calc
    _ ≤ 640 * (size + 16) ^ 2 + 1024 * (2 * size + 16) ^ 2 +
        7 * size + 2 * size + 42 +
        4096 * (width + 1) * (symbol + 1) * (size + 16) ^ 2 +
        5 * markedNumberBudget width size := by gcongr
    _ ≤ _ := by
      dsimp [markedNumberBudget]
      ring_nf
      lia

private theorem writeCertificateCase_spec (symbols : List Γ)
    (hcover : ∀ symbol, symbol ∈ symbols) (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive) (record : Option Γ → tm.State)
    (problem : BoundedVerification Γ) (index : Fin problem.certificateLength)
    (choice : ActiveChoices) (input output : List Γ) (symbol : Γ)
    (hindex : choice.firstPosition.1 = choice.time.2 + input.length + 1 + index.val)
    (size : Nat) (hsize : choice.size + (tick :: input).length +
      (output ++ implicationWord code problem index choice symbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice (tick :: input) output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeCertificateCase (tm := tm) symbols zero one tick code greater positive record symbol
    ⦃ fun _ cost final => AtPair tick choice (tick :: input)
        (output ++ implicationWord code problem index choice symbol) (some greater) origin final ∧
        cost.steps ≤ elapsed + certificateMoves width size (Encodable.encode symbol).size ⦄ := by
  let word := certificateWord code problem index symbol
  let first := output ++ word
  let bits := remainingBits choice input
  let prepared := elapsed + 640 * (size + 16) ^ 2
  let read := prepared + 1024 * (2 * size + 16) ^ 2
  let written := read + 7 * bits.length + 2 * choice.size + 42 +
    CertificateChoices.literalMoves width index.val.size
      (choice.size + (tick :: input).length + 11) output.length (Encodable.encode symbol).size
  have hpSize : choice.size ≤ size := by lia
  have hrSize : choice.size + input.length + (indexBits choice).length ≤ 2 * size := by
    have hb := indexBits_length choice
    dsimp [ActiveChoices.size] at *
    lia
  have hbits : bits.length ≤ size := by
    have hb := remainingBits_length choice input
    dsimp [ActiveChoices.size] at hpSize
    lia
  have hvalue : binaryValue bits.reverse = index.val + 1 := by
    simp only [bits, remainingBits_value]
    lia
  have hnone : input[(binaryValue (indexBits choice).reverse)]? = none := by
    rw [indexBits_value]
    exact List.getElem?_eq_none (by lia)
  have hwSize : choice.size + (tick :: input).length +
      (first ++ cellWord code choice (some (.inl symbol))).length + 32 ≤ size := by
    simpa [first, word, implicationWord, List.append_assoc] using hsize
  have hp := prepareIndex_spec (tm := tm) zero one hne tick greater positive hstates choice
    (tick :: input) output size hpSize origin elapsed
  have hr := readInputIndex_spec (tm := tm) symbols hcover zero one hne tick greater positive
    hstates record choice (indexBits choice) input output (2 * size) hrSize (some positive)
    origin prepared
  have hw := writeCertificate_spec (tm := tm) zero one hne tick code width hwidth problem
    index symbol choice bits hvalue (tick :: input) output (some (record none)) origin read
  have hc := writeCell_spec (tm := tm) zero one hne tick code width hwidth choice
    (some (.inl symbol)) (tick :: input) first size hwSize (some (record none)) origin written
  have hiSize : index.val.size ≤ size := by
    have hi := Nat.size_le.mpr (Nat.lt_two_pow_self (n := index.val))
    dsimp [ActiveChoices.size] at hpSize
    lia
  have houtput : output.length ≤ size := by
    simp only [List.length_append] at hsize
    lia
  have hdistance : choice.size + (tick :: input).length + 11 ≤ size + 11 := by lia
  have htime : written + 5 * markedNumberBudget width size ≤
      elapsed + certificateMoves width size (Encodable.encode symbol).size := by
    have hb := initial_certificate_moves_le width size (Encodable.encode symbol).size
      choice.size bits.length index.val.size (choice.size + (tick :: input).length + 11)
      output.length hpSize hbits hiSize hdistance houtput
    simpa only [written, read, prepared, certificateMoves, Nat.add_assoc] using
      Nat.add_le_add_left hb elapsed
  dsimp only at hr hw
  simp only [hnone] at hr
  vcgen [writeCertificateCase, hp, hr, hw, hc]
  all_goals clear hp hr hw hc
  all_goals
    simp_all only [AtPair, AtPairCounter, implicationWord, first, word, bits, remainingBits,
      List.append_assoc, true_and, and_true]
  case vc5 =>
    rename_i hlast
    exact hlast.2.trans htime
  all_goals
    rename_i hlast
    exact hlast.2


private noncomputable def writeCertificates (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State) :
    List Γ → Prog (TMQuery tm) Unit
  | [] => pure ()
  | symbol :: rest => do [TMQuery tm]
    writeCertificateCase symbols zero one tick code greater positive record symbol
    writeCertificates symbols zero one tick code greater positive record rest

private theorem writeCertificates_spec (symbols : List Γ)
    (hcover : ∀ symbol, symbol ∈ symbols) (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive) (record : Option Γ → tm.State)
    (problem : BoundedVerification Γ) (index : Fin problem.certificateLength)
    (choice : ActiveChoices) (input : List Γ)
    (hindex : choice.firstPosition.1 = choice.time.2 + input.length + 1 + index.val)
    (remaining : List Γ) (size : Nat) (output : List Γ)
    (hsize : choice.size + (tick :: input).length +
      (output ++ remaining.flatMap (implicationWord code problem index choice)).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice (tick :: input) output (some greater) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeCertificates (tm := tm) symbols zero one tick code greater positive record remaining
    ⦃ fun _ cost final => AtPair tick choice (tick :: input)
        (output ++ remaining.flatMap (implicationWord code problem index choice))
        (some greater) origin final ∧ cost.steps ≤ elapsed +
          (remaining.map fun symbol =>
            certificateMoves width size (Encodable.encode symbol).size).sum ⦄ := by
  induction remaining generalizing output elapsed with
  | nil =>
    vcgen [writeCertificates]
    simp_all
  | cons symbol rest ih =>
    let first := output ++ implicationWord code problem index choice symbol
    let time := certificateMoves width size (Encodable.encode symbol).size
    have hs : choice.size + (tick :: input).length +
        (output ++ implicationWord code problem index choice symbol).length + 32 ≤ size := by
      simp only [List.flatMap_cons, List.length_append] at hsize ⊢
      lia
    have hr : choice.size + (tick :: input).length +
        (first ++ rest.flatMap (implicationWord code problem index choice)).length + 32 ≤ size := by
      simpa [first, List.append_assoc] using hsize
    have hh := writeCertificateCase_spec (tm := tm) symbols hcover zero one hne tick code width
      hwidth greater positive hstates record problem index choice input output symbol hindex size
      hs (some greater) origin elapsed
    have ht := ih first hr (elapsed + time)
    vcgen [writeCertificates, hh, ht]
    all_goals simp_all [first, time, List.append_assoc, Nat.add_assoc]


private def writeReadSymbol (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (record : Option Γ → tm.State) : Prog (TMQuery tm) Unit :=
  select symbols (fun symbol => .stateIs (record (some symbol))) fun symbol => do [TMQuery tm]
    clearIndex
    writeCell zero one tick code (some (.inl symbol))

private theorem writeReadSymbol_spec (symbols : List Γ)
    (hcover : ∀ symbol, symbol ∈ symbols) (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (choice : ActiveChoices) (bits : List Bool) (input output : List Γ) (symbol : Γ)
    (size : Nat) (hsize : choice.size + input.length +
      (output ++ cellWord code choice (some (.inl symbol))).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice input output
        (counterDigits zero one bits) (some (record (some symbol))) origin current ∧
        cost.steps ≤ elapsed ⦄
      writeReadSymbol (tm := tm) symbols zero one tick code record
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ cellWord code choice (some (.inl symbol)))
        (some (record (some symbol))) origin final ∧
        cost.steps ≤ elapsed + 2 * bits.length + 2 * choice.size + 38 +
          5 * markedNumberBudget width size ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hpair, hcost⟩
  have hc := clearIndex_spec (tm := tm) zero one tick choice bits input output
    (some (record (some symbol))) origin elapsed
  have hw := writeCell_spec (tm := tm) zero one hne tick code width hwidth choice
    (some (.inl symbol)) input output size hsize (some (record (some symbol))) origin
    (elapsed + 2 * bits.length + 2 * choice.size + 38)
  vcgen [writeReadSymbol, Spec.select_spec (tm := tm) symbols
    (fun chosen => .stateIs (record (some chosen)))
    (fun chosen => do [TMQuery tm]
      clearIndex
      writeCell zero one tick code (some (.inl chosen))) symbol (hcover symbol)]
  constructor
  · intro chosen
    simp_all [AtPairCounter, hrecord.eq_iff, eq_comm]
  · vcgen [hc, hw]
    all_goals simp_all [AtPairCounter, AtPair, Nat.add_assoc]


private def sourceWord (code : CodeSymbol → List Γ) (symbols : List Γ)
    (problem : BoundedVerification Γ) (position : Fin (NPToSAT.Computation.width problem))
    (choice : ActiveChoices) : List Γ :=
  match initialSource problem position with
  | .inl symbol => cellWord code choice symbol
  | .inr index => symbols.flatMap (implicationWord code problem index choice)

private noncomputable def finishRead (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  ifₜ state =ₜ record none then
    testIndex one positive greater
    ifₜ state =ₜ greater then
      writeCell zero one tick code (some (.inr 0))
    else
      state ←ₜ greater
      writeCertificates symbols zero one tick code greater positive record symbols
  else
    writeReadSymbol symbols zero one tick code record
  state ←ₜ greater

private def readRemainderMoves (width size : Nat) (symbols : List Γ) : Nat :=
  6 * size + 40 + 5 * markedNumberBudget width size +
    (symbols.map fun symbol => certificateMoves width size (Encodable.encode symbol).size).sum

private theorem finishRead_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (code : CodeSymbol → List Γ)
    (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (problem : BoundedVerification Γ) (position : Fin (NPToSAT.Computation.width problem))
    (choice : ActiveChoices) (hindex : choice.firstPosition.1 = position.val)
    (htime : choice.time.2 = problem.time)
    (hrest : position.val + 1 + choice.firstPosition.2 = NPToSAT.Computation.width problem)
    (hleft : problem.time ≤ position.val) (hright : problem.time ≤ choice.firstPosition.2)
    (bits : List Bool)
    (hvalue : binaryValue bits.reverse = position.val - problem.time - problem.input.length)
    (output : List Γ) (size : Nat) (hbits : bits.length ≤ size)
    (hsize : choice.size + (tick :: problem.input).length +
      (output ++ sourceWord code symbols problem position choice).length + 32 ≤ size)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPairCounter tick choice (tick :: problem.input) output
        (counterDigits zero one bits)
        (some (record problem.input[position.val - problem.time]?)) origin current ∧
        cost.steps ≤ elapsed ⦄
      finishRead (tm := tm) symbols zero one tick code greater positive record
    ⦃ fun _ cost final => AtPair tick choice (tick :: problem.input)
        (output ++ sourceWord code symbols problem position choice) (some greater) origin final ∧
        cost.steps ≤ elapsed + readRemainderMoves width size symbols ⦄ := by
  cases hlookup : problem.input[position.val - problem.time]? with
  | some symbol =>
    have hs := InitialSource.input problem position symbol hleft hlookup
    have hword : sourceWord code symbols problem position choice =
        cellWord code choice (some (.inl symbol)) := by simp [sourceWord, hs]
    have hw := writeReadSymbol_spec (tm := tm) symbols hcover zero one hne tick code width
      hwidth record hrecord choice bits (tick :: problem.input) output symbol size
      (by simpa only [hword] using hsize) origin elapsed
    vcgen [finishRead, Spec.branch_false_spec]
    constructor
    · simp_all [AtPairCounter, hrecord.eq_iff]
    · vcgen [hw]
      all_goals simp_all [AtPair, readRemainderMoves]
      all_goals lia
  | none =>
    have hended : problem.input.length ≤ position.val - problem.time := by
      simpa using hlookup
    let tested := elapsed + 4 * bits.length + 2 * choice.size + 40
    have ht := testIndex_spec (tm := tm) zero one hne tick positive greater
      (Ne.symm hstates) choice bits (tick :: problem.input) output (some (record none)) origin
      elapsed
    by_cases hz : binaryValue bits.reverse = 0
    · have hp : position.val = problem.time + problem.input.length := by lia
      have hs := InitialSource.separator problem position hp
      have hword : sourceWord code symbols problem position choice =
          cellWord code choice (some (.inr 0)) := by simp [sourceWord, hs]
      have hw := writeCell_spec (tm := tm) zero one hne tick code width hwidth choice
        (some (.inr 0)) (tick :: problem.input) output size
        (by simpa only [hword] using hsize) (some greater) origin tested
      vcgen [finishRead, Spec.branch_true_spec]
      constructor
      · simp_all [AtPairCounter]
      · vcgen [ht, Spec.branch_true_spec]
        all_goals try (solve | simp_all [AtPairCounter, AtPair])
        constructor
        · simp_all [AtPair, tested]
        · vcgen [hw]
          all_goals simp_all [AtPair, readRemainderMoves, tested]
          all_goals lia
    · have hremaining : 0 < position.val - problem.time - problem.input.length := by lia
      have hbound := InitialSource.certificate_index_lt problem position choice.firstPosition.2
        (by lia) hright hremaining
      let index : Fin problem.certificateLength :=
        ⟨position.val - problem.time - problem.input.length - 1, hbound⟩
      have hp : position.val = problem.time + problem.input.length + 1 + index.val := by
        dsimp [index]
        lia
      have hs := InitialSource.certificate problem position index hp
      have hword : sourceWord code symbols problem position choice =
          symbols.flatMap (implicationWord code problem index choice) := by simp [sourceWord, hs]
      have hw := writeCertificates_spec (tm := tm) symbols hcover zero one hne tick code width
        hwidth greater positive hstates record problem index choice problem.input (by lia)
        symbols size output (by simpa only [hword] using hsize) origin tested
      vcgen [finishRead, Spec.branch_true_spec]
      constructor
      · simp_all [AtPairCounter]
      · vcgen [ht, Spec.branch_false_spec]
        all_goals try (solve | simp_all [AtPairCounter, AtPair])
        constructor
        · simp_all [AtPair, tested, Ne.symm hstates]
        · vcgen [hw]
          all_goals simp_all [AtPair, readRemainderMoves, tested]
          all_goals lia


private noncomputable def writeInterior (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  state ←ₜ positive
  prepareIndex zero one tick greater positive
  readInputIndex symbols zero one greater positive record
  finishRead symbols zero one tick code greater positive record

private def interiorMoves (width size : Nat) (symbols : List Γ) : Nat :=
  640 * (size + 16) ^ 2 + 1024 * (2 * size + 16) ^ 2 + readRemainderMoves width size symbols

private theorem writeInterior_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (code : CodeSymbol → List Γ)
    (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (problem : BoundedVerification Γ) (position : Fin (NPToSAT.Computation.width problem))
    (choice : ActiveChoices) (hindex : choice.firstPosition.1 = position.val)
    (htime : choice.time.2 = problem.time)
    (hrest : position.val + 1 + choice.firstPosition.2 = NPToSAT.Computation.width problem)
    (hleft : problem.time ≤ position.val) (hright : problem.time ≤ choice.firstPosition.2)
    (output : List Γ) (size : Nat)
    (hsize : choice.size + (tick :: problem.input).length +
      (output ++ sourceWord code symbols problem position choice).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice (tick :: problem.input) output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeInterior (tm := tm) symbols zero one tick code greater positive record
    ⦃ fun _ cost final => AtPair tick choice (tick :: problem.input)
        (output ++ sourceWord code symbols problem position choice) (some greater) origin final ∧
        cost.steps ≤ elapsed + interiorMoves width size symbols ⦄ := by
  let prepared := elapsed + 640 * (size + 16) ^ 2
  let read := prepared + 1024 * (2 * size + 16) ^ 2
  let bits := remainingBits choice problem.input
  have hpSize : choice.size ≤ size := by lia
  have hrSize : choice.size + problem.input.length + (indexBits choice).length ≤ 2 * size := by
    have hb := indexBits_length choice
    dsimp [ActiveChoices.size] at *
    lia
  have hb : bits.length ≤ size := by
    have hb := remainingBits_length choice problem.input
    dsimp [ActiveChoices.size] at hpSize
    lia
  have hv : binaryValue bits.reverse = position.val - problem.time - problem.input.length := by
    simpa [bits, hindex, htime] using remainingBits_value choice problem.input
  have hp := prepareIndex_spec (tm := tm) zero one hne tick greater positive hstates choice
    (tick :: problem.input) output size hpSize origin elapsed
  have hr := readInputIndex_spec (tm := tm) symbols hcover zero one hne tick greater positive
    hstates record choice (indexBits choice) problem.input output (2 * size) hrSize
    (some positive) origin prepared
  have hf := finishRead_spec (tm := tm) symbols hcover zero one hne tick code width hwidth
    greater positive hstates record hrecord problem position choice hindex htime hrest hleft hright
    bits hv output size hb hsize origin read
  vcgen [writeInterior, hp, hr, hf]
  all_goals
    simp_all only [AtPair, AtPairCounter, prepared, read, bits, remainingBits,
      interiorMoves, indexBits_value, Nat.add_assoc, and_true]

private noncomputable def writeInitialCell (symbols : List Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  InitialComparison.compare tm zero one tick greater positive false
  ifₜ state =ₜ greater then
    writeCell zero one tick code none
  else
    InitialComparison.compare tm zero one tick greater positive true
    ifₜ state =ₜ greater then
      writeCell zero one tick code none
    else
      writeInterior symbols zero one tick code greater positive record
  state ←ₜ greater

private def cellMoves (width size : Nat) (symbols : List Γ) : Nat :=
  2 * comparisonTime size + interiorMoves width size symbols

private theorem writeInitialCell_spec (symbols : List Γ) (hcover : ∀ symbol, symbol ∈ symbols)
    (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (code : CodeSymbol → List Γ)
    (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (problem : BoundedVerification Γ) (position : Fin (NPToSAT.Computation.width problem))
    (choice : ActiveChoices) (hindex : choice.firstPosition.1 = position.val)
    (htime : choice.time.2 = problem.time)
    (hrest : position.val + 1 + choice.firstPosition.2 = NPToSAT.Computation.width problem)
    (output : List Γ) (size : Nat)
    (hsize : choice.size + (tick :: problem.input).length +
      (output ++ sourceWord code symbols problem position choice).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice (tick :: problem.input) output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeInitialCell (tm := tm) symbols zero one tick code greater positive record
    ⦃ fun _ cost final => AtPair tick choice (tick :: problem.input)
        (output ++ sourceWord code symbols problem position choice) (some greater) origin final ∧
        cost.steps ≤ elapsed + cellMoves width size symbols ⦄ := by
  have hcap : choice.size + (tick :: problem.input).length + output.length + 32 ≤ size := by
    simp only [List.length_append] at hsize
    lia
  have hc := InitialComparison.compare_spec (tm := tm) zero one hne tick greater positive
    hstates false choice (tick :: problem.input) output size hcap label origin elapsed
  by_cases hl : position.val < problem.time
  · have hs := InitialSource.blank_left problem position hl
    have hword : sourceWord code symbols problem position choice = cellWord code choice none := by
      simp [sourceWord, hs]
    have hw := writeCell_spec (tm := tm) zero one hne tick code width hwidth choice none
      (tick :: problem.input) output size (by simpa only [hword] using hsize) (some greater)
      origin (elapsed + comparisonTime size)
    vcgen [writeInitialCell, hc, Spec.branch_true_spec]
    constructor
    · simp_all [AtPair]
    · vcgen [hw]
      all_goals simp_all [AtPair, cellMoves, interiorMoves, readRemainderMoves]
      all_goals lia
  · have hc₂ := InitialComparison.compare_spec (tm := tm) zero one hne tick greater positive
      hstates true choice (tick :: problem.input) output size hcap (some positive) origin
      (elapsed + comparisonTime size)
    by_cases hr : choice.firstPosition.2 < problem.time
    · have hs := InitialSource.blank_right problem position choice.firstPosition.2 (by lia) hr
      have hword : sourceWord code symbols problem position choice = cellWord code choice none := by
        simp [sourceWord, hs]
      have hw := writeCell_spec (tm := tm) zero one hne tick code width hwidth choice none
        (tick :: problem.input) output size (by simpa only [hword] using hsize) (some greater)
        origin (elapsed + comparisonTime size + comparisonTime size)
      vcgen [writeInitialCell, hc, Spec.branch_false_spec]
      constructor
      · simp_all [AtPair, Ne.symm hstates]
      · vcgen [hc₂, Spec.branch_true_spec]
        all_goals try (solve | simp_all [AtPair])
        constructor
        · simp_all [AtPair]
        · vcgen [hw]
          all_goals simp_all [AtPair, cellMoves, interiorMoves, readRemainderMoves]
          all_goals lia
    · have hi := writeInterior_spec (tm := tm) symbols hcover zero one hne tick code width
        hwidth greater positive hstates record hrecord problem position choice hindex htime hrest
        (by lia) (by lia) output size hsize (some positive) origin
        (elapsed + comparisonTime size + comparisonTime size)
      vcgen [writeInitialCell, hc, Spec.branch_false_spec]
      constructor
      · simp_all [AtPair, Ne.symm hstates]
      · vcgen [hc₂, Spec.branch_false_spec]
        all_goals try (solve | simp_all [AtPair])
        constructor
        · simp_all [AtPair, Ne.symm hstates]
        · vcgen [hi]
          all_goals simp_all [AtPair, cellMoves, Nat.add_assoc]
          all_goals lia


omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ] in
private theorem initial_cells_moves_le (width size : Nat) (weights : List Nat) :
    PositionIteration.positionIterationMoves size
      (2 * NPToSAT.Computation.HeadChoices.comparisonTime size + 640 * (size + 16) ^ 2 +
        1024 * (2 * size + 16) ^ 2 + 6 * size + 40 + 5 * markedNumberBudget width size +
          (weights.map fun weight =>
            262144 * (width + 1) * weight * (size + 16) ^ 2).sum) + 2 ≤
      1048576 * (width + 1) * (weights.sum + 1) * (size + 16) ^ 3 := by
  simp only [List.sum_map_mul_right]
  rw [List.sum_map_mul_left weights (fun weight => weight) (262144 * (width + 1))]
  simp only [List.map_id']
  dsimp [PositionIteration.positionIterationMoves, NPToSAT.Computation.HeadChoices.comparisonTime,
    markedNumberBudget]
  ring_nf
  lia


omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem cellIterationMoves_le (width size : Nat) (symbols : List Γ) :
    positionIterationMoves size (cellMoves width size symbols) ≤
      1048576 * (width + 1) *
        ((symbols.map fun symbol => (Encodable.encode symbol).size + 1).sum + 1) *
          (size + 16) ^ 3 := by
  have h := initial_cells_moves_le width size
    (symbols.map fun symbol => (Encodable.encode symbol).size + 1)
  simp only [cellMoves, interiorMoves, readRemainderMoves, certificateMoves, List.map_map,
    Function.comp_def, Nat.add_assoc] at h ⊢
  lia

omit [Inhabited Γ] [DecidableEq Γ] in
private theorem sourceWord_eq (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (position : Fin (NPToSAT.Computation.width problem)) (choice : ActiveChoices)
    (htime : choice.time.1 = 0) (hposition : choice.firstPosition.1 = position.val) :
    sourceWord code (Finset.univ : Finset Γ).toList problem position choice =
      InitialSource.word code problem position := by
  rw [InitialSource.word_eq_selected code problem position choice htime hposition]
  cases hsource : initialSource problem position
  all_goals simp only [sourceWord, hsource, cellWord]
  congr 1
  funext symbol
  simp only [implicationWord, certificateWord, cellWord, List.append_assoc]

private noncomputable def cellPiece (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (index : Nat) : List Γ :=
  if h : index < NPToSAT.Computation.width problem then
    InitialSource.word code problem ⟨index, h⟩
  else []

omit [Inhabited Γ] [DecidableEq Γ] in
private theorem cellPiece_word (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ) :
    (List.range (NPToSAT.Computation.width problem)).flatMap (cellPiece code problem) =
      (List.finRange (NPToSAT.Computation.width problem)).flatMap
        (InitialSource.word code problem) := by
  have hi : (List.finRange (NPToSAT.Computation.width problem)).map Fin.val =
      List.range (NPToSAT.Computation.width problem) := by
    ext index
    simp
  rw [← hi, List.flatMap_map]
  congr 1
  funext position
  simp only [cellPiece, dite_eq_left position.isLt]

private theorem writeCells_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (problem : BoundedVerification Γ) (output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) +
      (tick :: problem.input).length + (output ++
        (List.finRange (NPToSAT.Computation.width problem)).flatMap
          (InitialSource.word code problem)).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) (tick :: problem.input) output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      InitialCells.writeCells tm tick greater
        (writeInitialCell (Finset.univ : Finset Γ).toList zero one tick code
          greater positive record)
    ⦃ fun _ cost final => final.config = ⟨some greater,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) (tick :: problem.input) (output ++
            (List.finRange (NPToSAT.Computation.width problem)).flatMap
              (InitialSource.word code problem))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + positionIterationMoves size
          (cellMoves width size (Finset.univ : Finset Γ).toList) ⦄ := by
  let symbols := (Finset.univ : Finset Γ).toList
  let action := writeInitialCell (tm := tm) symbols zero one tick code greater positive record
  let piece := cellPiece code problem
  have hp : 0 < NPToSAT.Computation.width problem := by simp only [NPToSAT.Computation.width]; lia
  have hs : 0 < problem.verifier.states + 2 := by lia
  have hleaf : PositionSpec tick 0 problem.time (NPToSAT.Computation.width problem)
      (problem.verifier.states + 2) (tick :: problem.input) piece (some greater) action size
      (cellMoves width size symbols) := by
    intro index rest hindex out hcap positionHead steps
    have hbound : index < NPToSAT.Computation.width problem := by lia
    let position : Fin (NPToSAT.Computation.width problem) := ⟨index, hbound⟩
    let choice : ActiveChoices := ⟨(0, problem.time), (index, rest),
      (0, problem.verifier.states + 2 - 1), (0, NPToSAT.Computation.width problem - 1),
      (0, problem.verifier.states + 2 - 1)⟩
    have hw : sourceWord code symbols problem position choice = piece index := by
      dsimp only [symbols]
      rw [sourceWord_eq code problem position choice rfl rfl]
      simp only [piece, cellPiece, dite_eq_left hbound]
      rfl
    have hd : choice.size + (tick :: problem.input).length +
        (out ++ sourceWord code symbols problem position choice).length + 32 ≤ size := by
      rw [hw]
      dsimp only [choice, ActiveChoices.size]
      lia
    have ha := writeInitialCell_spec (tm := tm) symbols (by simp [symbols]) zero one hne tick
      code width hwidth greater positive hstates record hrecord problem position choice rfl rfl
      (by dsimp only [position]; lia)
      out size hd (some greater) positionHead steps
    rw [hw] at ha
    simpa only [action, choice] using ha
  have hc := InitialCells.writeCells_spec (tm := tm) tick greater action problem.time
    (NPToSAT.Computation.width problem) (problem.verifier.states + 2) hp hs (tick :: problem.input)
    output piece size (cellMoves width size symbols) hleaf (by
      simpa only [piece, cellPiece_word] using hsize) label origin elapsed
  simpa only [action, piece, symbols, cellPiece_word] using hc

/-- This template writes the clauses describing the verifier's initial tape and head. -/
noncomputable def writeInitialClauses (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (greater positive : tm.State) (record : Option Γ → tm.State) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  HeadWriting.writeHead tm zero one tick code (Encodable.encode (some verifier.initial))
  InitialCells.writeCells tm tick greater
    (writeInitialCell (Finset.univ : Finset Γ).toList zero one tick code greater positive record)

/-- This polynomial bounds writing the initial head clause and all initial tape-cell clauses. -/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  HeadWriting.timeBound width +
    Polynomial.C (1048576 * (width + 1) *
      (((Finset.univ : Finset Γ).toList.map fun symbol => (Encodable.encode symbol).size + 1).sum +
        1)) * (Polynomial.X + 16) ^ 3

/--
The writer appends the initial clauses, preserves the original input and all bounds, and
returns to the first symbol of the time bound within the stated polynomial move bound.
-/
@[spec] theorem writeInitialClauses_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (zero one : Γ) (hne : zero ≠ one)
    (tick : Γ) (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (greater positive : tm.State) (hstates : greater ≠ positive)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (problem : BoundedVerification Γ) (hverifier : problem.verifier = verifier)
    (output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) +
      (tick :: problem.input).length + (output ++
        (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code).length +
          64 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) (tick :: problem.input) output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeInitialClauses tm verifier zero one tick code greater positive record
    ⦃ fun _ cost final => final.config = ⟨some greater,
        ChoiceIteration.layout tick (problem.time + 1) (NPToSAT.Computation.width problem)
          (problem.verifier.states + 2) (tick :: problem.input) (output ++
            (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code)⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + (timeBound (Γ := Γ) width).eval size ⦄ := by
  subst verifier
  let head := HeadWriting.word code (Encodable.encode (some problem.verifier.initial)) problem.time
  let cells :=
    (List.finRange (NPToSAT.Computation.width problem)).flatMap (InitialSource.word code problem)
  have hw : (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code =
      head ++ cells := InitialSource.initialClauses_word code problem
  have hhcap : problem.time + 2 * NPToSAT.Computation.width problem +
    2 * (problem.verifier.states + 2) +
      (tick :: problem.input).length + (output ++ head).length + 32 ≤ size := by
    rw [hw] at hsize
    simp only [List.length_append] at hsize ⊢
    lia
  have hccap : problem.time + 2 * NPToSAT.Computation.width problem +
    2 * (problem.verifier.states + 2) +
      (tick :: problem.input).length + ((output ++ head) ++ cells).length + 32 ≤ size := by
    rw [hw] at hsize
    simp only [List.length_append] at hsize ⊢
    lia
  have hh := HeadWriting.writeHead_spec (tm := tm) zero one hne tick code width hwidth
    (Encodable.encode (some problem.verifier.initial)) problem.time
    (NPToSAT.Computation.width problem)
    (problem.verifier.states + 2) (tick :: problem.input) output size hhcap label origin elapsed
  have hc := writeCells_spec (tm := tm) zero one hne tick code width hwidth greater positive
    hstates record hrecord problem (output ++ head) size hccap label origin
    (elapsed + (HeadWriting.timeBound width).eval size)
  have ht := cellIterationMoves_le width size (Finset.univ : Finset Γ).toList
  vcgen [writeInitialClauses, hh, hc]
  all_goals
    simp_all only [head, cells, timeBound, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat,
      List.append_assoc]
    all_goals lia

end Algolean.Algorithms.NPToSAT.InitialWriting
