/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Increment
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Reading
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing

/-!
# Visiting the positions of a unary count

* `forUnary` reads a count written as repetitions of one fixed, nonempty word. It runs the
  same action once for each repetition, with a binary position counter beginning at zero.
* The counter grows into blank cells to the left. The original unary word is preserved, and
  the counter is erased at the end. The head returns to the unary word's first cell.
* The action may append output beyond the unary word and other preserved regions.

The loop temporarily erases the first symbol of the current repetition to remember its place.
While the action runs, this divides the unary word into two parts. `counterTape` describes
the counter, these two parts, and the output. The action must preserve the counter and both
parts; it changes only the output. The loop increments the counter after each action.

This is a machine template. The repeated word and the action are fixed independently of the
count. The number of repetitions and every position are read or maintained on the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This writes a unary count using the chosen nonempty word for each unit. -/
@[expose] def unaryWord (unit : List Γ) (count : Nat) : List Γ :=
  (List.replicate count unit).flatten

/-- This is the existing binary number encoding, reversed to match a counter growing left. -/
@[expose] def counterWord (zero one : Γ) (index : Nat) : List Γ :=
  (encodingNatBool.encode index).reverse.map (fun bit => if bit then one else zero)

/-- This describes the counter and the two parts of the temporarily interrupted unary word. -/
@[expose] def counterTape (zero one : Γ) (index : Nat) (before after : List Γ)
    (extra : List (List Γ)) (output : List Γ) : BiTape Γ :=
  BiTape.segment StackTape.nil (counterWord zero one index)
    (StackTape.separateWords (before :: after :: extra) (StackTape.mapSome output))

private def loopTape (zero one : Γ) (unit : List Γ) (index done rest : Nat)
    (extra : List (List Γ)) (output : List Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend (unaryWord unit done).reverse
      (StackTape.cons none (StackTape.mapSome (counterWord zero one index).reverse)))
    (unaryWord unit rest) (StackTape.separateWords extra (StackTape.mapSome output))

private def step (zero one tick : Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  visitPreviousRegion tm tick (do [TMQuery tm]
    action
    incrementLeft tm zero one)

private def loop (zero one tick : Γ) (unitTail : List Γ) (action : Prog (TMQuery tm) Unit) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    step zero one tick action
    moveCells tm .Right (unitTail.length + 1)

private def finish (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftEnd tm
  previousRegion tm
  eraseRight tm
  moveₜ .Right

/--
This machine template runs `action` for each unit written on the tape. The action starts on
the binary counter and must preserve it and the unary word. The loop preserves every other
region, erases its counter, and restores the starting head position.
-/
def forUnary (tm : SingleTapeTM Γ) (zero one tick : Γ) (unitTail : List Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  loop zero one tick unitTail action
  finish tm

/-- This bounds the action calls, counter updates, scans, and final counter erasure. -/
@[expose] def forUnaryMoves (unit count actionBound : Nat) : Nat :=
  count * (actionBound + 8 * (unit + 1) * (count + 1)) + 4 * (unit + 1) * (count + 1)

private theorem incrementIndex_spec (zero one : Γ) (hne : zero ≠ one) (index : Nat)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment StackTape.nil (counterWord zero one index) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      incrementLeft tm zero one
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (counterWord zero one (index + 1)) tail⟩ ∧
        final.headPos = origin + index.size - (index + 1).size ∧
        cost.steps ≤ elapsed + 4 * index.size + 5 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  have hc := carryCount_le_length (encodingNatBool.encode index)
  have hl := length_incrementBits_le (encodingNatBool.encode index)
  vcgen [incrementLeft_spec zero one hne (encodingNatBool.encode index).reverse
    tail label origin initial.steps]
  all_goals
    simp_all [counterWord]
    all_goals lia

private theorem advance_spec (crossed rest : List Γ) (left tail : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left (crossed ++ rest) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      moveCells tm .Right crossed.length
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment (StackTape.prepend crossed.reverse left) rest tail⟩ ∧
        final.headPos = origin + crossed.length ∧ cost.steps ≤ elapsed + crossed.length ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [moveCells_spec .Right crossed.length (BiTape.segment left (crossed ++ rest) tail)
    label origin initial.steps]
  all_goals simp_all [BiTape.segment_moveRight_iterate]

/--
This states what the same action must do at each position. While it runs, a blank replaces
the first symbol of the current unit. The two neighboring parts of the unary word and all
extra regions are preserved. Only the output changes, from `output index` to `output (index + 1)`.
-/
@[expose] def UnaryAction (zero one tick : Γ) (unitTail : List Γ) (count : Nat)
    (extra : List (List Γ)) (output : Nat → List Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat) : Prop :=
  ∀ index rest, index + rest + 1 = count → ∀ (origin : ℤ) (elapsed : Nat),
    ⦃ fun cost current => current.config = ⟨label, counterTape zero one index
        (unaryWord (tick :: unitTail) index) (unitTail ++ unaryWord (tick :: unitTail) rest)
        extra (output index)⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      action
    ⦃ fun _ cost final => final.config = ⟨label, counterTape zero one index
        (unaryWord (tick :: unitTail) index) (unitTail ++ unaryWord (tick :: unitTail) rest)
        extra (output (index + 1))⟩ ∧ final.headPos = origin ∧ cost.steps ≤ elapsed + bound ⦄

private theorem step_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (unitTail : List Γ)
    (count index rest : Nat) (hcount : index + rest + 1 = count)
    (extra : List (List Γ)) (output : Nat → List Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat)
    (haction : UnaryAction zero one tick unitTail count extra output label action bound)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        loopTape zero one (tick :: unitTail) index index (rest + 1) extra (output index)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      step (tm := tm) zero one tick action
    ⦃ fun _ cost final => final.config = ⟨label,
        loopTape zero one (tick :: unitTail) (index + 1) index (rest + 1)
          extra (output (index + 1))⟩ ∧ final.headPos = origin ∧
        cost.steps ≤ elapsed + bound + 7 * (unitTail.length + 2) * (count + 1) ⦄ := by
  let before := unaryWord (tick :: unitTail) index
  let after := unitTail ++ unaryWord (tick :: unitTail) rest
  let tail := StackTape.separateWords extra (StackTape.mapSome (output index))
  let resultTail := StackTape.separateWords extra (StackTape.mapSome (output (index + 1)))
  have hact (position : ℤ) (steps : Nat) := haction index rest hcount position steps
  simp only [counterTape] at hact
  have hcompound (position : ℤ) (steps : Nat) :
      ⦃ fun cost current => current.config = ⟨label,
          BiTape.segment StackTape.nil (counterWord zero one index)
            (StackTape.separateWords (before :: after :: extra)
              (StackTape.mapSome (output index)))⟩ ∧
          current.headPos = position ∧ cost.steps ≤ steps ⦄
        (do [TMQuery tm] action; incrementLeft tm zero one)
      ⦃ fun _ cost final => final.config = ⟨label,
          BiTape.segment StackTape.nil (counterWord zero one (index + 1))
            (StackTape.separateWords (before :: after :: extra)
              (StackTape.mapSome (output (index + 1))))⟩ ∧
          final.headPos = position + index.size - (index + 1).size ∧
          cost.steps ≤ steps + (bound + 4 * index.size + 5) ⦄ := by
    vcgen [hact position steps,
      incrementIndex_spec zero one hne index
        (StackTape.separateWords (before :: after :: extra)
          (StackTape.mapSome (output (index + 1)))) label position (steps + bound)]
    all_goals
      simp_all [before, after]
      all_goals lia
  have hu : unaryWord (tick :: unitTail) (rest + 1) =
      tick :: (unitTail ++ unaryWord (tick :: unitTail) rest) := by
    simp [unaryWord, List.replicate_succ]
  have hs (n : Nat) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hi : index.size ≤ count := (hs index).trans (by lia)
  have hj : (index + 1).size ≤ count := (hs (index + 1)).trans (by lia)
  have hd : before.length ≤ (unitTail.length + 1) * count := by
    simp only [before, unaryWord, List.length_flatten, List.map_replicate, List.sum_replicate,
      List.length_cons]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_right (unitTail.length + 1) (show index ≤ count by lia)
  unfold step
  vcgen [visitPreviousRegion_tail_spec tick (do [TMQuery tm] action; incrementLeft tm zero one)
    (counterWord zero one index) (counterWord zero one (index + 1)) before after tail resultTail
    (bound + 4 * index.size + 5) label label origin elapsed (by
      intro position steps
      simpa [tail, resultTail, counterWord] using hcompound position steps)]
  all_goals
    simp_all [loopTape, before, after, tail, resultTail, counterWord]
    all_goals ring_nf at *
    all_goals lia

private theorem loop_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (unitTail : List Γ)
    (count : Nat) (extra : List (List Γ)) (output : Nat → List Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat)
    (haction : UnaryAction zero one tick unitTail count extra output label action bound)
    (index rest : Nat) (hcount : index + rest = count) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        loopTape zero one (tick :: unitTail) index index rest extra (output index)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      loop (tm := tm) zero one tick unitTail action
    ⦃ fun _ cost final => final.config = ⟨label,
        loopTape zero one (tick :: unitTail) count count 0 extra (output count)⟩ ∧
        final.headPos = origin + rest * (unitTail.length + 1) ∧
        cost.steps ≤ elapsed + rest * (bound + 8 * (unitTail.length + 2) * (count + 1)) ⦄ := by
  induction rest generalizing index origin elapsed with
  | zero =>
    have : index = count := by lia
    subst index
    unfold loop
    vcgen [Spec.while_false_spec]
    simp_all [loopTape, unaryWord, BiTape.segment]
  | succ rest ih =>
    have hu : unaryWord (tick :: unitTail) (rest + 1) =
        (tick :: unitTail) ++ unaryWord (tick :: unitTail) rest := by
      simp [unaryWord, List.replicate_succ]
    have hprefix : unaryWord (tick :: unitTail) (index + 1) =
        unaryWord (tick :: unitTail) index ++ (tick :: unitTail) := by
      simp [unaryWord, List.replicate_succ']
    let visit := bound + 7 * (unitTail.length + 2) * (count + 1)
    let total := bound + 8 * (unitTail.length + 2) * (count + 1)
    have ha := advance_spec (tm := tm) (tick :: unitTail)
      (unaryWord (tick :: unitTail) rest)
      (StackTape.prepend (unaryWord (tick :: unitTail) index).reverse
        (StackTape.cons none (StackTape.mapSome (counterWord zero one (index + 1)).reverse)))
      (StackTape.separateWords extra (StackTape.mapSome (output (index + 1))))
      label origin (elapsed + visit)
    simp only [List.length_cons] at ha
    unfold loop
    vcgen [Spec.while_step_spec (loop := loop (tm := tm) zero one tick unitTail action)
        (hloop := rfl),
      step_spec zero one hne tick unitTail count index rest (by lia) extra output label
        action bound haction origin elapsed,
      ha, ih (index + 1) (by lia) (origin + (unitTail.length + 1 : Nat)) (elapsed + total)]
    all_goals
      simp_all [loopTape, unaryWord, List.reverse_append,
        StackTape.prepend_append, visit, total, BiTape.segment]
      all_goals ring_nf at *
      all_goals lia

private theorem finish_spec (zero one tick : Γ) (unitTail : List Γ) (count : Nat)
    (extra : List (List Γ)) (output : List Γ) (label : Option tm.State)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        loopTape zero one (tick :: unitTail) count count 0 extra output⟩ ∧
        current.headPos = origin + (unaryWord (tick :: unitTail) count).length ∧
        cost.steps ≤ elapsed ⦄
      finish tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (unaryWord (tick :: unitTail) count)
          (StackTape.separateWords extra (StackTape.mapSome output))⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 4 * (unitTail.length + 2) * (count + 1) ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  let input := unaryWord (tick :: unitTail) count
  let counter := counterWord zero one count
  let tail := StackTape.separateWords extra (StackTape.mapSome output)
  have hs : count.size ≤ count := Nat.size_le.mpr Nat.lt_two_pow_self
  vcgen [finish,
    seekLeftEnd_segment_spec (StackTape.mapSome counter.reverse) tail input.reverse []
      label (origin + input.length) initial.steps,
    previousRegion_spec StackTape.nil counter input tail label origin
      (initial.steps + input.length + 2),
    eraseRight_segment_spec StackTape.nil (StackTape.prepend input (StackTape.cons none tail))
      counter label (origin - (counter.length + 1 : Nat))
      (initial.steps + input.length + 2 + counter.length + 3)]
  all_goals
    simp_all [loopTape, input, counter, tail, counterWord, unaryWord,
      List.length_flatten, TMState.move, TMState.moveCost]
    all_goals ring_nf at *
    all_goals lia

/--
The loop calls the same action at positions zero through `count - 1`, with the counter stored
on the tape. It preserves the unary word and extra regions, erases its counter, and restores
the original head position. The action's bound gives the stated bound for the whole loop.
-/
@[spec] theorem forUnary_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ) (unitTail : List Γ)
    (count : Nat) (extra : List (List Γ)) (output : Nat → List Γ) (label : Option tm.State)
    (action : Prog (TMQuery tm) Unit) (bound : Nat)
    (haction : UnaryAction zero one tick unitTail count extra output label action bound)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment StackTape.nil (unaryWord (tick :: unitTail) count)
          (StackTape.separateWords extra (StackTape.mapSome (output 0)))⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      forUnary tm zero one tick unitTail action
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment StackTape.nil (unaryWord (tick :: unitTail) count)
          (StackTape.separateWords extra (StackTape.mapSome (output count)))⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + forUnaryMoves (unitTail.length + 1) count bound ⦄ := by
  have hz : counterWord zero one 0 = [] := rfl
  vcgen [forUnary, loop_spec zero one hne tick unitTail count extra output label action bound
      haction 0 count (by simp) origin elapsed,
    finish_spec zero one tick unitTail count extra (output count) label origin
      (elapsed + count * (bound + 8 * (unitTail.length + 2) * (count + 1)))]
  all_goals
    simp_all [loopTape, unaryWord, forUnaryMoves, List.length_flatten]
    all_goals ring_nf at *
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines
