/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Basic
public import Algolean.Models.SingleTapeTM.Composition.While

/-! # Scanning a contiguous block and returning to its left end -/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/-- Scan right until the first blank, without changing any tape contents. -/
def seekRightBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Right

/-- Scanning a suffix reaches its right blank in exactly its length many moves. -/
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

/-- Scan left over occupied cells, stopping at the blank preceding the block. -/
def seekLeftBlank (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    moveₜ .Left

/-- Scanning left from a bit crosses the reversed prefix and stops at its preceding blank. -/
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

/-- Return to the first bit of a block, including when starting at its right blank. -/
def seekLeftEnd (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftBlank tm
  moveₜ .Right

/-- Returning to the left end preserves all bits and takes `left.length + 2` moves. -/
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

/-- A verified scanning component; its prefix and suffix are logical contract parameters. -/
@[simps program]
def seekRightBlankComponent :
    Component tm (fun p : List Symbol × List Symbol => fun s => s.config.BiTape = cursor p.1 p.2)
      (fun p s cost final =>
        final.config = {s.config with BiTape := cursor (p.2.reverse ++ p.1) []} ∧
        final.headPos = s.headPos + p.2.length ∧ cost.steps = p.2.length) where
  program := seekRightBlank tm
  correct p s hs := seekRightBlank_correct p.1 p.2 s hs

/-- A verified return-to-start component, usable after another procedure without resetting space. -/
@[simps program]
def seekLeftEndComponent :
    Component tm (fun p : List Symbol × List Symbol => fun s => s.config.BiTape = cursor p.1 p.2)
      (fun p s cost final =>
        final.config = {s.config with BiTape := cursor [] (p.1.reverse ++ p.2)} ∧
        final.headPos = s.headPos - p.1.length ∧ cost.steps = p.1.length + 2) where
  program := seekLeftEnd tm
  correct p s hs := seekLeftEnd_correct p.1 p.2 s hs

end Algolean.Algorithms.SingleTapeTuringMachines
