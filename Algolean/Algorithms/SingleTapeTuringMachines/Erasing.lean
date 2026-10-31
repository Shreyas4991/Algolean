/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BitOperations
public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning

/-! # Erasing a Boolean block without losing its original head position -/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

@[simp] theorem nil_moveLeft : (BiTape.nil : BiTape Bool).moveLeft = BiTape.nil := rfl

@[simp] theorem nil_moveRight : (BiTape.nil : BiTape Bool).moveRight = BiTape.nil := rfl

/-- Erase from the last occupied cell towards the left boundary. -/
def eraseLeft (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ none
    moveₜ .Left

/-- Erasing from a last cell clears exactly the block to its left, then stops on blank. -/
theorem eraseLeft_correct (left : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left [bit]) :
    Runs (eraseLeft tm) s BiTape.nil (s.headPos - (left.length + 1 : ℕ)) (left.length + 1) := by
  induction left generalizing bit s with
  | nil =>
    unfold eraseLeft
    apply runs_while_step (by simp [hs])
    have hw : Runs (FreeM.lift (.write none)) s BiTape.nil s.headPos 0 := by
      simpa [hs] using write_correct s none
    have hb : Runs (do FreeM.lift (.write none); FreeM.lift (.move .Left)) s BiTape.nil
        (s.headPos - 1) 1 := by
      simpa using hw.seq (q := FreeM.lift (.move .Left)) (second := BiTape.nil)
        (pos₂ := s.headPos - 1) (time₂ := 1) (by
          intro t ht hp
          simpa [TMState.move, ht, hp, sub_eq_add_neg] using move_correct t .Left)
    have hr := hb.seq (q := eraseLeft tm) (second := BiTape.nil)
      (pos₂ := s.headPos - 1) (time₂ := 0) (by
        intro t ht hp
        simp [eraseLeft, ht, hp, BiTape.nil])
    simpa [eraseLeft] using hr
  | cons prev left ih =>
    unfold eraseLeft
    apply runs_while_step (by simp [hs])
    have hw : Runs (FreeM.lift (.write none)) s (cursor (prev :: left) []) s.headPos 0 := by
      simpa [hs] using write_correct s none
    have hb : Runs (do FreeM.lift (.write none); FreeM.lift (.move .Left)) s
        (cursor left [prev]) (s.headPos - 1) 1 := by
      simpa using hw.seq (q := FreeM.lift (.move .Left)) (second := cursor left [prev])
        (pos₂ := s.headPos - 1) (time₂ := 1) (by
          intro t ht hp
          simpa [TMState.move, ht, hp, sub_eq_add_neg] using move_correct t .Left)
    have hr := hb.seq (q := eraseLeft tm) (second := BiTape.nil)
      (pos₂ := s.headPos - ((prev :: left).length + 1 : ℕ)) (time₂ := left.length + 1) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor left [prev] := by simp [ht]
        convert ih prev t htape using 1
        simp [hp, sub_eq_add_neg, add_assoc]
        lia)
    simpa [eraseLeft, Nat.add_comm, Nat.add_left_comm] using hr

/-- Erase the block immediately to the left of the head, ending at its original first cell. -/
def eraseToLeft (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  eraseLeft tm
  moveₜ .Right

/-- This erasing phase handles empty blocks and retains the starting-cell convention. -/
theorem eraseToLeft_correct (left : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor left []) :
    Runs (eraseToLeft tm) s BiTape.nil (s.headPos - left.length) (left.length + 2) := by
  cases left with
  | nil =>
    have hm : Runs (FreeM.lift (.move .Left)) s BiTape.nil (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have h := hm.seq (q := do eraseLeft tm; FreeM.lift (.move .Right))
      (second := BiTape.nil) (pos₂ := s.headPos) (time₂ := 1) (by
        intro t ht hp
        have he : Runs (eraseLeft tm) t BiTape.nil (s.headPos - 1) 0 := by
          simp [eraseLeft, ht, hp, BiTape.nil]
        simpa using he.seq (q := FreeM.lift (.move .Right)) (second := BiTape.nil)
          (pos₂ := s.headPos) (time₂ := 1) (by
            intro u hu hup
            simpa [TMState.move, hu, hup] using move_correct u .Right))
    simpa [eraseToLeft] using h
  | cons bit left =>
    have hm : Runs (FreeM.lift (.move .Left)) s (cursor left [bit]) (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have h := hm.seq (q := do eraseLeft tm; FreeM.lift (.move .Right))
      (second := BiTape.nil) (pos₂ := s.headPos - (bit :: left).length)
      (time₂ := left.length + 2) (by
        intro t ht hp
        have htape : t.config.BiTape = cursor left [bit] := by simp [ht]
        have he := eraseLeft_correct left bit t htape
        have hr := he.seq (q := FreeM.lift (.move .Right)) (second := BiTape.nil)
          (pos₂ := s.headPos - (bit :: left).length) (time₂ := 1) (by
            intro u hu hup
            convert move_correct u .Right using 1 <;>
              simp [TMState.move, hu, hup, hp, sub_eq_add_neg, add_assoc])
        simpa [Nat.add_assoc] using hr)
    simpa [eraseToLeft, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/-- Clear an entire input block and return the head to its initial position. -/
def eraseBlock (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  eraseToLeft tm

/-- Erasing has exact linear time, with the head and control state restored. -/
theorem eraseBlock_correct (bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = cursor [] bits) :
    Runs (eraseBlock tm) s BiTape.nil s.headPos (2 * bits.length + 2) := by
  have hr : Runs (seekRightBlank tm) s (cursor bits.reverse [])
      (s.headPos + bits.length) bits.length := by
    simpa using seekRightBlank_correct [] bits s hs
  have h := hr.seq (q := eraseToLeft tm) (second := BiTape.nil) (pos₂ := s.headPos)
    (time₂ := bits.length + 2) (by
      intro t ht hp
      have htape : t.config.BiTape = cursor bits.reverse [] := by simp [ht]
      simpa [hp] using eraseToLeft_correct bits.reverse t htape)
  simpa [eraseBlock, two_mul, Nat.add_assoc] using h

end Algolean.Algorithms.SingleTapeTuringMachines
