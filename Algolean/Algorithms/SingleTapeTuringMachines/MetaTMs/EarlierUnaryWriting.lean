/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.EarlierWords
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.UnaryWriting

/-!
# Writing the binary value of an earlier unary word

* `appendEarlierUnary` visits an earlier word that represents a number by repeating one symbol.
  It appends that number in binary to the output. It can first write the number of binary digits
  so that the decoder can distinguish consecutive numbers.
* All source words and the starting head position are preserved. The temporary counter is
  erased before the program returns.

This is a machine template. The output symbol words, digit symbols, and numbers of intervening
words are fixed once. The number being written is read from the tape.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This machine template writes the earlier unary word's number at the output. `before` counts
words between the counter and that source, `between` counts words from that source to the
current word, and `distance` counts words from the counter to the output.
-/
def appendEarlierUnary (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : Bool → List Γ) (header : Bool) (before between distance : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  onCounter tm (appendUnaryNumber tm zero one tick [] code header before distance) between

/-- This counts the number writer and the outward and return visits across preserved words. -/
@[expose] def earlierUnaryMoves (header : Bool) (width count : Nat)
    (before between : List (List Γ)) (current : List Γ) (parts : List (List Γ))
    (output : Nat) : Nat :=
  unaryNumberMoves header width 1 count before (between.reverse ++ current :: parts) output +
    2 * count + 2 * (between.map List.length).sum + 4 * between.length + 4

/--
Writing the earlier word's number appends exactly its existing binary encoding. All source
words, the control state, and the starting head position are preserved.
-/
@[spec] theorem appendEarlierUnary_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (header : Bool) (count : Nat) (before between : List (List Γ))
    (current : List Γ) (parts : List (List Γ)) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let left := counterLeft [] (between ++ List.replicate count tick :: before)
    ⦃ fun cost machineState => machineState.config =
        ⟨label, BiTape.segment left current
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        machineState.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      appendEarlierUnary tm zero one tick code header before.length between.length
        (before.length + between.length + parts.length + 2)
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment left current
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (unaryNumberBits header count).flatMap code)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed +
          earlierUnaryMoves header width count before between current parts output.length ⦄ := by
  dsimp only
  let source := List.replicate count tick
  let tail := StackTape.separateWords parts (StackTape.mapSome output)
  let written := output ++ (unaryNumberBits header count).flatMap code
  let resultTail := StackTape.separateWords parts (StackTape.mapSome written)
  let allParts := between.reverse ++ current :: parts
  let bound := unaryNumberMoves header width 1 count before allParts output.length
  have ha (position : ℤ) (steps : Nat) := appendUnaryNumber_spec (tm := tm) zero one hne tick []
    code width hwidth header count before allParts output label position steps
  have hv := onEarlierWord_spec (tm := tm)
    (appendUnaryNumber tm zero one tick [] code header before.length
      (before.length + between.length + parts.length + 2))
    (counterLeft [] before).tail (counterLeft [] before).tail source between current tail resultTail
    label label bound (by
      intro position steps
      simpa [allParts, source, counterRight, tail, resultTail, written, bound,
        List.length_append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ha position steps)
    origin elapsed
  vcgen [appendEarlierUnary, hv]
  all_goals
    simp_all [earlierLeft_counterLeft, earlierUnaryMoves, allParts, source, tail,
      resultTail, written, bound, Nat.add_assoc]

end Algolean.Algorithms.SingleTapeTuringMachines
