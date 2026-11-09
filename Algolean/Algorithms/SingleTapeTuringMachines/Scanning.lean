/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Basic
public import Algolean.Models.SingleTapeTM.Composition.While

/-!
# Moving across a contiguous block

This file supplies three Turing machine programs that move the head without changing any tape
symbols. `seekRightBlank` moves right until it reaches a blank, and `seekLeftBlank` does the same to
the left. Either program stops immediately if its starting cell is blank. `seekLeftEnd` first moves
left, scans to the blank before the block, and then moves right onto its first symbol. It can
therefore return from the blank immediately after a block as well as from inside it.

The correctness theorems state the final head position and exact number of head moves for each
program. They apply with the tape and cell histories left by an earlier computation.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
`seekRightBlank tm` is a Turing machine program that repeatedly moves the head right while the
current cell is occupied. It stops on the first blank without changing any tape symbols. If the
initial cell is blank, it finishes without moving.
-/
def seekRightBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Right

/--
Starting from `cursor left right`, the rightward scan crosses every symbol of `right` and stops on
the blank immediately after it. The tape contents are unchanged, the head moves right by
`right.length`, and the program uses exactly that many head moves.
-/
theorem seekRightBlank_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekRightBlank tm) s (cursor (right.reverse ++ left) [])
      (s.headPos + right.length) right.length := by
  induction right generalizing left s with
  | nil => simp [seekRightBlank, hs]
  | cons bit right ih =>
    unfold seekRightBlank
    apply runs_while_step (by simp [hs])
    have hm := move_correct s .Right
    have hm' : Runs (FreeM.lift (.move .Right)) s (cursor (bit :: left) right)
        (s.headPos + 1) 1 := by simpa [TMState.move, hs] using hm
    have hr := hm'.seq (q := seekRightBlank tm)
      (second := cursor ((bit :: right).reverse ++ left) [])
      (pos₂ := s.headPos + (bit :: right).length) (time₂ := right.length) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor (bit :: left) right := by simp [ht]
        simpa [List.reverse_cons, List.append_assoc, hp, add_assoc, add_comm, add_left_comm] using
          ih (bit :: left) t htape)
    simpa [seekRightBlank, Nat.add_comm] using hr

/--
`seekLeftBlank tm` is a Turing machine program that repeatedly moves the head left while the current
cell is occupied. It stops on the first blank and leaves all tape symbols unchanged. If it starts on
a blank, it does not move.
-/
def seekLeftBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Left

/--
Starting on the displayed `bit`, the leftward scan crosses that symbol and all of `left` before
stopping on the blank preceding the block. It preserves the entire block and uses exactly
`left.length + 1` head moves.
-/
theorem seekLeftBlank_correct (left : List Symbol) (bit : Symbol) (right : List Symbol)
    (s : TMState tm)
    (hs : s.config.BiTape = cursor left (bit :: right)) :
    Runs (seekLeftBlank tm) s (before (left.reverse ++ bit :: right))
      (s.headPos - (left.length + 1 : ℕ)) (left.length + 1) := by
  induction left generalizing bit right s with
  | nil =>
    unfold seekLeftBlank
    apply runs_while_step (by simp [hs])
    have hm : Runs (FreeM.lift (.move .Left)) s (before (bit :: right)) (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := seekLeftBlank tm) (time₂ := 0)
      (second := before (bit :: right)) (pos₂ := s.headPos - 1) (by
        intro t ht hp
        simp [ht, hp, seekLeftBlank])
    simpa [seekLeftBlank] using hr
  | cons prev left ih =>
    unfold seekLeftBlank
    apply runs_while_step (by simp [hs])
    have hm : Runs (FreeM.lift (.move .Left)) s (cursor left (prev :: bit :: right))
        (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := seekLeftBlank tm) (time₂ := left.length + 1)
      (second := before ((prev :: left).reverse ++ bit :: right))
      (pos₂ := s.headPos - ((prev :: left).length + 1 : ℕ)) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor left (prev :: bit :: right) := by simp [ht]
        convert ih prev (bit :: right) t htape using 1 <;>
          simp [List.reverse_cons, List.append_assoc, hp, sub_eq_add_neg, add_assoc]
        lia)
    simpa [seekLeftBlank, Nat.add_comm, Nat.add_left_comm] using hr

/--
`seekLeftEnd tm` is a Turing machine program that moves left once, scans left to a blank, and then
moves right once. For a contiguous block, it finishes on the first symbol even when it starts on the
blank just after the block. If the block is empty, it returns to its starting cell after two moves.
-/
def seekLeftEnd (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftBlank tm
  moveₜ .Right

/--
Starting from `cursor left right`, this program preserves the block and finishes on its first
symbol, or on the starting blank when the block is empty. Its final coordinate is `s.headPos -
left.length`, and it uses exactly `left.length + 2` head moves.
-/
theorem seekLeftEnd_correct (left right : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = cursor left right) :
    Runs (seekLeftEnd tm) s (cursor [] (left.reverse ++ right))
      (s.headPos - left.length) (left.length + 2) := by
  cases left with
  | nil =>
    have hm : Runs (FreeM.lift (.move .Left)) s (before right) (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := do seekLeftBlank tm; FreeM.lift (.move .Right)) (time₂ := 1)
      (second := cursor [] right) (pos₂ := s.headPos) (by
        intro t ht hp
        have hl : Runs (seekLeftBlank tm) t (before right) (s.headPos - 1) 0 := by
          simp [seekLeftBlank, ht, hp]
        simpa using hl.seq (q := FreeM.lift (.move .Right)) (time₂ := 1)
          (second := cursor [] right) (pos₂ := s.headPos) (by
            intro u hu hup
            simpa [TMState.move, hu, hup] using move_correct u .Right))
    simpa [seekLeftEnd] using hr
  | cons bit left =>
    have hm : Runs (FreeM.lift (.move .Left)) s (cursor left (bit :: right)) (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := do seekLeftBlank tm; FreeM.lift (.move .Right))
      (time₂ := left.length + 2) (second := cursor [] ((bit :: left).reverse ++ right))
      (pos₂ := s.headPos - (bit :: left).length) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor left (bit :: right) := by simp [ht]
        have hl := seekLeftBlank_correct left bit right t htape
        have hret := hl.seq (q := FreeM.lift (.move .Right)) (time₂ := 1)
          (second := cursor [] ((bit :: left).reverse ++ right))
          (pos₂ := s.headPos - (bit :: left).length) (by
            intro u hu hup
            convert move_correct u .Right using 1 <;>
              simp [TMState.move, hu, hup, hp, List.reverse_cons, List.append_assoc,
                sub_eq_add_neg, add_assoc])
        simpa [Nat.add_assoc] using hret)
    simpa [seekLeftEnd, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hr

end Algolean.Algorithms.SingleTapeTuringMachines
