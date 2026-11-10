/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Regions
public import Algolean.Algorithms.SingleTapeTuringMachines.Writing

/-!
# Tape regions for writing the TMSAT-to-SAT reduction

The tape contains working words, the original input, and the output, in that order. A blank
separates consecutive words. Each word begins with one fixed symbol `marker : Γ`, so an empty
working word or output still has an occupied first cell. The marker is part of the storage
format; the original input follows its marker without any changes to its symbols.

`prepare` creates empty working words and an empty output region, preserving every input
symbol. It finishes on the first region's marker. With `k` working regions and an input of
length `n`, it uses exactly `2 * n + 2 * k + 7` head moves.

The representation uses `BiTape.segment` and `StackTape.separateWords`. The programs
`nextRegion` and `previousRegion` move between neighboring regions. The output is last so
that the existing `appendWord` program can extend it without overwriting another region.

The marker and the number of working regions are fixed when constructing the containing
Query machine, independently of the input and its length. The words themselves are tape data.
Every occupied cell contains a symbol of `Γ`; region boundaries use physical blank cells.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Tape

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying
open scoped TMQuery

variable {Γ : Type}

/--
This describes the head at the first region's marker, with one blank between successive regions.
The lists contain the region contents without their markers. An empty list of regions is blank.
-/
@[expose] def layout (marker : Γ) : List (List Γ) → BiTape Γ
  | [] => BiTape.nil
  | current :: rest => BiTape.segment StackTape.nil (marker :: current)
      (StackTape.separateWords (rest.map (marker :: ·)) StackTape.nil)

variable [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This writes the input's marker and the empty output region and returns to the input marker. -/
private def frameInput (marker : Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  tape ←ₜ some marker
  moveₜ .Right
  seekRightBlank tm
  moveₜ .Right
  tape ←ₜ some marker
  moveₜ .Left
  seekLeftEnd tm

private theorem frameInput_correct (marker : Γ) (input : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.mk₁ input) :
    Runs (frameInput (tm := tm) marker) s (layout marker [input, []])
      (s.headPos - 1) (2 * input.length + 7) := by
  have hmarker : StackTape.cons (some marker) StackTape.nil = StackTape.mapSome [marker] := rfl
  have hp : Runs (do
      FreeM.lift (.move .Left)
      FreeM.lift (.write (some marker))
      FreeM.lift (.move .Right)) s
      (BiTape.segment (StackTape.cons (some marker) StackTape.nil) input StackTape.nil)
      s.headPos 2 := by
    have h := ((move_correct s .Left).append_write (some marker)).append_move .Right
    cases input <;>
      simpa [htape, bind_assoc, BiTape.segment, BiTape.mk₁, BiTape.nil, BiTape.moveLeft,
        BiTape.moveRight, BiTape.write, sub_eq_add_neg] using h
  have hs := hp.seq (q := seekRightBlank tm)
    (second := BiTape.segment (StackTape.prepend input.reverse
      (StackTape.cons (some marker) StackTape.nil)) [] StackTape.nil)
    (pos₂ := s.headPos + input.length) (time₂ := input.length) (by
      intro middle hmiddle hpos
      simpa [hpos] using seekRightBlank_segment
        (StackTape.cons (some marker) StackTape.nil) input StackTape.nil middle
        (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  have ho := ((hs.append_move .Right).append_write (some marker)).append_move .Left
  have hr := ho.seq (q := seekLeftEnd tm)
    (second := layout marker [input, []]) (pos₂ := s.headPos - 1)
    (time₂ := input.length + 3) (by
      intro middle hmiddle hpos
      have hleft : middle.config.BiTape = BiTape.segment
          (StackTape.prepend (input.reverse ++ [marker]) StackTape.nil) []
          (StackTape.mapSome [marker]) := by
        simpa [BiTape.segment, BiTape.moveRight, BiTape.moveLeft, BiTape.write,
          hmarker] using congrArg SingleTapeTM.Cfg.BiTape hmiddle
      simpa [layout, hmarker, hpos, List.reverse_append, sub_eq_add_neg, add_assoc,
        add_comm, add_left_comm] using
        seekLeftEnd_segment StackTape.nil (input.reverse ++ [marker]) []
          (StackTape.mapSome [marker]) middle (by simpa using hleft))
  simpa [frameInput, bind_assoc, two_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hr

/-- This places a fixed number of empty regions before the current first region. -/
private def prependEmpty (marker : Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => pure ()
  | count + 1 => do [TMQuery tm]
    moveₜ .Left
    tape ←ₜ none
    moveₜ .Left
    tape ←ₜ some marker
    prependEmpty marker count

private theorem prependEmpty_correct (marker : Γ) (count : Nat) (current : List Γ)
    (rest : List (List Γ)) (s : TMState tm)
    (htape : s.config.BiTape = layout marker (current :: rest)) :
    Runs (prependEmpty (tm := tm) marker count) s
      (layout marker (List.replicate count [] ++ current :: rest))
      (s.headPos - 2 * count) (2 * count) := by
  induction count generalizing current rest s with
  | zero =>
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    simp only [List.replicate_zero, List.nil_append]
    rw [← htape]
  | succ count ih =>
    have hf : Runs (do
        FreeM.lift (.move .Left)
        FreeM.lift (.write none)
        FreeM.lift (.move .Left)
        FreeM.lift (.write (some marker))) s
        (layout marker ([] :: current :: rest)) (s.headPos - 2) 2 := by
      have h := (((move_correct s .Left).append_write none).append_move .Left).append_write
        (some marker)
      simpa [htape, layout, bind_assoc, BiTape.segment, BiTape.moveLeft, BiTape.write,
        sub_eq_add_neg, add_assoc] using h
    have hr := hf.seq (q := prependEmpty marker count)
      (second := layout marker (List.replicate (count + 1) [] ++ current :: rest))
      (pos₂ := s.headPos - 2 * (count + 1)) (time₂ := 2 * count) (by
        intro middle hmiddle hpos
        simpa [List.replicate_succ', hpos, sub_eq_add_neg, mul_add, add_assoc] using
          ih [] (current :: rest) middle (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
    simpa [prependEmpty, bind_assoc, Nat.mul_add, Nat.add_comm] using hr

/--
This machine template preserves the input, places empty working regions before it, and places
an empty output region after it. It finishes at the first region's marker. The containing
machine fixes `marker` and `workCount` once, independently of the input and its length.
-/
def prepare (tm : SingleTapeTM Γ) (marker : Γ) (workCount : Nat) :
    Prog (TMQuery tm) Unit := do
  frameInput marker
  prependEmpty marker workCount

/--
Initialization preserves the input and control state and creates exactly the requested empty
working regions and one empty output region. The theorem gives the exact head position and
number of moves and applies after any earlier computation with the displayed input tape.
-/
theorem prepare_correct (marker : Γ) (workCount : Nat) (input : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.mk₁ input) :
    Runs (prepare tm marker workCount) s
      (layout marker (List.replicate workCount [] ++ [input, []]))
      (s.headPos - (2 * workCount + 1 : Nat)) (2 * input.length + 2 * workCount + 7) := by
  have hf := frameInput_correct marker input s htape
  have hr := hf.seq (q := prependEmpty marker workCount)
    (second := layout marker (List.replicate workCount [] ++ [input, []]))
    (pos₂ := s.headPos - (2 * workCount + 1 : Nat)) (time₂ := 2 * workCount) (by
      intro middle hmiddle hpos
      simpa [hpos, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        prependEmpty_correct marker workCount input [[]] middle
          (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  simpa [prepare, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

end Algolean.Algorithms.TMSATToSAT.Tape
