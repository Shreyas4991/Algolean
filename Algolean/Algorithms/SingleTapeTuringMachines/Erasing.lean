/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning

/-!
# Erasing a block and returning to its starting cell

The Turing machine program `eraseLeft` erases occupied cells while moving left and stops on the
first blank. `eraseToLeft` starts on the blank after a block, erases back through it, and finishes
at the coordinate where its first symbol used to be. `eraseBlock` first scans right from the
beginning of the input and then uses this backward erasure to clear the whole block and restore the
head.

The full program also handles empty input and uses exactly `2 * bits.length + 2` head moves. Erasing
a symbol does not remove its cell from the recorded tape range, so previously allocated space
remains part of the machine's history after the tape becomes blank.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery

open scoped TMQuery

variable {Symbol : Type}

/-- Moving left on a completely blank tape leaves it blank. -/
private theorem nil_moveLeft : (BiTape.nil : BiTape Symbol).moveLeft = BiTape.nil := rfl

/-- Moving right on a completely blank tape leaves it blank. -/
private theorem nil_moveRight : (BiTape.nil : BiTape Symbol).moveRight = BiTape.nil := rfl

attribute [local simp] nil_moveLeft nil_moveRight

variable [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This Turing machine program erases the current cell and moves right. If all cells to its left
are blank, the remaining word then begins under the head.
-/
def eraseAndMove (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right

/-- Erasing the first symbol and moving right leaves exactly the remaining word on the tape. -/
theorem eraseAndMove_correct (symbol : Symbol) (rest : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] (symbol :: rest)) :
    Runs (eraseAndMove tm) s (cursor [] rest) (s.headPos + 1) 1 := by
  simpa [eraseAndMove, htape, cursor, BiTape.write, BiTape.moveRight] using
    (write_correct s none).append_move .Right

/--
This Turing machine program erases symbols while moving right and stops on the first blank.
When started at the first symbol of a word on an otherwise blank tape, it clears the whole tape.
-/
def eraseRight (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    eraseAndMove tm

/-- Erasing a word to the right clears the tape and uses one head move for each input symbol. -/
theorem eraseRight_correct (word : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] word) :
    Runs (eraseRight tm) s BiTape.nil (s.headPos + word.length) word.length := by
  induction word generalizing s with
  | nil =>
    simpa [eraseRight, htape] using runs_while_false (.not (.tapeIs none))
      (eraseAndMove tm) s (by simp [htape, BiTape.nil])
  | cons symbol rest ih =>
    unfold eraseRight
    apply runs_while_step (by simp [htape])
    have hfirst := eraseAndMove_correct symbol rest s htape
    have hr := hfirst.seq (q := eraseRight tm) (by
      intro middle hmiddle hpos
      simpa [hpos] using ih middle (by simp [hmiddle]))
    simpa [eraseRight, add_assoc, add_comm, add_left_comm] using hr

/--
This Turing machine program erases cells while moving right until it reaches `ending`.
It leaves that symbol and everything after it untouched. Its correctness theorem requires
that an occurrence of `ending` lies at or to the right of the starting cell.
-/
def eraseUntil (tm : SingleTapeTM Symbol) (ending : Symbol) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  whileₜ (notₜ tape =ₜ some ending) do
    eraseAndMove tm

/--
If `crossed` contains no `ending`, the program erases exactly `crossed` and stops on the next
occurrence of `ending`. The remaining word is the only occupied part of the tape.
-/
theorem eraseUntil_correct (ending : Symbol) (crossed rest : List Symbol) (s : TMState tm)
    (htape : s.config.BiTape = cursor [] (crossed ++ ending :: rest))
    (hcrossed : ending ∉ crossed) :
    Runs (eraseUntil tm ending) s (cursor [] (ending :: rest))
      (s.headPos + crossed.length) crossed.length := by
  induction crossed generalizing s with
  | nil => simp [eraseUntil, htape]
  | cons symbol crossed ih =>
    have hparts : ending ≠ symbol ∧ ending ∉ crossed := by simpa using hcrossed
    unfold eraseUntil
    apply runs_while_step (by simp [htape, Ne.symm hparts.1])
    have hfirst := eraseAndMove_correct symbol (crossed ++ ending :: rest) s htape
    have hr := hfirst.seq (q := eraseUntil tm ending) (by
      intro middle hmiddle hpos
      simpa [hpos] using ih middle (by simp [hmiddle]) hparts.2)
    simpa [eraseUntil, add_assoc, add_comm, add_left_comm] using hr

/--
`eraseLeft tm` is a Turing machine program that replaces the current occupied cell with a blank and
moves left, repeating until it reaches an already blank cell. Starting on the last symbol of a
contiguous block erases the whole block and leaves the head on the blank just before it.
-/
def eraseLeft (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    tape ←ₜ none
    moveₜ .Left

/--
Starting on the last symbol `bit`, this program erases that cell and the entire prefix `left`,
leaving a completely blank tape. The head finishes `left.length + 1` cells to the left of its
starting coordinate, using exactly that many head moves.
-/
theorem eraseLeft_correct (left : List Symbol) (bit : Symbol) (s : TMState tm)
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

/--
`eraseToLeft tm` is a Turing machine program that starts on the blank immediately after a contiguous
block. It moves left, erases the block while moving backward, and then moves right onto the cell
that used to hold the first symbol. For an empty block, it returns to the starting blank after two
moves.
-/
def eraseToLeft (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  eraseLeft tm
  moveₜ .Right

/--
Starting from `cursor left []`, this program leaves the tape blank and finishes at `s.headPos -
left.length`. It uses exactly `left.length + 2` head moves and preserves the control state,
including when `left` is empty.
-/
theorem eraseToLeft_correct (left : List Symbol) (s : TMState tm)
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

/--
`eraseBlock tm` is a Turing machine program that starts at the beginning of the input block, scans
to the blank after it, and erases the symbols on the way back. It finishes at the original head
coordinate on a blank tape. The recorded allocation and visit histories are retained.
-/
def eraseBlock (tm : SingleTapeTM Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  eraseToLeft tm

/--
Erasing `bits` leaves a completely blank tape and restores the initial head coordinate. The program
preserves the control state and uses exactly `2 * bits.length + 2` head moves, even when the input
is empty.
-/
theorem eraseBlock_correct (bits : List Symbol) (s : TMState tm)
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
