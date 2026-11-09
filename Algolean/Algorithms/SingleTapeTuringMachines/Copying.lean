/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Pairing
public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning
public import Algolean.Models.SingleTapeTM.Composition.Branch
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Duplicating a Boolean word on one tape

The Turing machine program `duplicate` replaces an input word with a Boolean encoding of two copies.
For an input of length `n`, the output contains `n` true bits, a false delimiter, the original word,
and a second copy of that word. For example, `[true, false]` becomes `[true, true, false, true,
false, true, false]`. The head finishes on the first output cell, which is `n + 1` cells to the left
of its original coordinate.

The machine builds the output by repeatedly copying one source bit into a separate region to the
right and extending a unary length header to the left. During this loop, blanks separate the header,
the source word, and the copied prefix. A source bit is temporarily erased so the machine can find
and restore its position after returning from the copy region. After copying all bits, the machine
shifts the copy left to close the gap, replaces the blank between the header and source with a false
delimiter, and returns to the beginning of the header.

The tape views below describe these intermediate layouts for the correctness proofs. Their list
arguments are specification data; the running program finds its way by testing the current tape
cell. Duplication preserves the control state and uses exactly `4 * n ^ 2 + 11 * n + 5` head moves.
Previously recorded tape allocation remains part of the final space count.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.Copying

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

/--
`stackAppend bits tail` is a pure Lean function that puts the occupied cells for `bits` before the
existing stack `tail`. It preserves all cells of `tail`, including any internal blanks that separate
the regions used during copying.
-/
@[simp] def stackAppend : List Bool → StackTape Bool → StackTape Bool
  | [], tail => tail
  | bit :: bits, tail => StackTape.cons (some bit) (stackAppend bits tail)

theorem stackAppend_append (first second : List Bool) (tail : StackTape Bool) :
    stackAppend (first ++ second) tail = stackAppend first (stackAppend second tail) := by
  induction first <;> simp_all

@[simp] theorem stackAppend_nil (bits : List Bool) :
    stackAppend bits StackTape.nil = StackTape.mapSome bits := by
  induction bits <;> simp_all

/--
`segment left bits tail` is a pure Lean function that describes a tape whose head starts on the
first cell of `bits`. The stack `left` lies to the head's left, and a blank separates `bits` from
the region `tail` to its right. If `bits` is empty, the head is on that separating blank.
-/
@[simps head left right]
def segment (left : StackTape Bool) (bits : List Bool) (tail : StackTape Bool) : BiTape Bool where
  head := bits.head?
  left := left
  right := match bits with
    | [] => tail
    | _ :: rest => stackAppend rest (StackTape.cons none tail)

@[simp] theorem segment_moveRight (left : StackTape Bool) (bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment left (bit :: bits) tail).moveRight =
      segment (StackTape.cons (some bit) left) bits tail := by
  cases bits <;> simp [segment, BiTape.moveRight]

@[simp] theorem segment_moveLeft (left : StackTape Bool) (bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment (StackTape.cons (some bit) left) bits tail).moveLeft =
      segment left (bit :: bits) tail := by
  cases bits <;> simp [segment, BiTape.moveLeft]

@[simp] theorem segment_write (left : StackTape Bool) (old bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment left (old :: bits) tail).write (some bit) = segment left (bit :: bits) tail := rfl

@[simp] theorem segment_moveLeft_gap (left : StackTape Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment (StackTape.cons none left) bits tail).moveLeft =
      segment left [] (stackAppend bits (StackTape.cons none tail)) := by
  cases bits <;> simp [segment, BiTape.moveLeft]

@[simp] theorem segment_moveRight_gap (left : StackTape Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment left [] (stackAppend bits (StackTape.cons none tail))).moveRight =
      segment (StackTape.cons none left) bits tail := by
  cases bits <;> simp [segment, BiTape.moveRight]

@[simp] theorem segment_moveRight_word (left : StackTape Bool) (bits : List Bool) :
    (segment left [] (StackTape.mapSome bits)).moveRight =
      segment (StackTape.cons none left) bits StackTape.nil := by
  cases bits <;> simp [segment, BiTape.moveRight]

@[simp] theorem segment_erase_advance (left : StackTape Bool) (bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    ((segment left (bit :: bits) tail).write none).moveRight =
      segment (StackTape.cons none left) bits tail := by
  cases bits <;> simp [segment, BiTape.write, BiTape.moveRight]

@[simp] theorem segment_write_gap (left : StackTape Bool) (bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) :
    (segment left [] (stackAppend bits (StackTape.cons none tail))).write (some bit) =
      segment left (bit :: bits) tail := rfl

@[simp] theorem segment_write_end (left : StackTape Bool) (bit : Bool) :
    (segment left [] StackTape.nil).write (some bit) = segment left [bit] StackTape.nil := rfl

@[simp] theorem segment_write_word (left : StackTape Bool) (bit : Bool) (bits : List Bool) :
    (segment left [] (StackTape.mapSome bits)).write (some bit) =
      segment left (bit :: bits) StackTape.nil := by
  simp [segment, BiTape.write]

@[simp] theorem segment_start (bits : List Bool) :
    segment StackTape.nil bits StackTape.nil = BiTape.mk₁ bits := by
  cases bits <;> simp [segment, BiTape.mk₁, BiTape.nil]

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
`writeAdvance tm symbol` is a Turing machine program that writes `symbol` into the current cell and
moves the head one cell to the right. Passing `none` erases the current cell before moving; passing
`some bit` writes that Boolean value.
-/
def writeAdvance (tm : SingleTapeTM Bool) (symbol : Option Bool) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  tape ←ₜ symbol
  moveₜ .Right

/--
Writing and advancing changes only the original head cell and finishes one coordinate to its right.
It preserves the control state and uses exactly one head move.
-/
theorem writeAdvance_correct (s : TMState tm) (symbol : Option Bool) :
    Runs (writeAdvance tm symbol) s ((s.config.BiTape.write symbol).moveRight) (s.headPos + 1) 1 :=
  ⟨_, _, ⟨2, rfl⟩, rfl, rfl, rfl⟩

/--
The rightward scan crosses the displayed `bits` and stops on the blank separating them from `tail`.
It preserves the contents of both neighboring regions and uses exactly `bits.length` head moves.
-/
theorem seekRightBlank_segment (left : StackTape Bool) (bits : List Bool) (tail : StackTape Bool)
    (s : TMState tm) (hs : s.config.BiTape = segment left bits tail) :
    Runs (seekRightBlank tm) s (segment (stackAppend bits.reverse left) [] tail)
      (s.headPos + bits.length) bits.length := by
  induction bits generalizing left s with
  | nil =>
    simp [seekRightBlank, hs]
  | cons bit bits ih =>
    unfold seekRightBlank
    apply runs_while_step (by simp [hs])
    have hm : Runs (FreeM.lift (.move .Right)) s
        (segment (StackTape.cons (some bit) left) bits tail) (s.headPos + 1) 1 := by
      simpa [TMState.move, hs] using move_correct s .Right
    have hr := hm.seq (q := seekRightBlank tm) (time₂ := bits.length)
      (second := segment (stackAppend (bit :: bits).reverse left) [] tail)
      (pos₂ := s.headPos + (bit :: bits).length) (by
        intro t ht hp
        have htape : t.config.BiTape = segment (StackTape.cons (some bit) left) bits tail := by
          simp [ht]
        simpa [List.reverse_cons, stackAppend_append, hp, add_assoc, add_comm, add_left_comm] using
          ih (StackTape.cons (some bit) left) t htape)
    simpa [seekRightBlank, Nat.add_comm] using hr

/--
`seekLeftGap tm` is a Turing machine program that moves left at least once and then continues left
until it reaches a blank. The initial move lets it leave the current boundary even when it starts on
a blank. It never changes tape contents.
-/
def seekLeftGap (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftBlank tm

/--
This leftward scan crosses the displayed left prefix and stops on its preceding blank. It preserves
the regions on both sides of that blank and uses exactly `left.length + 1` head moves, including its
required initial move.
-/
theorem seekLeftGap_segment (base : StackTape Bool) (left bits : List Bool)
    (tail : StackTape Bool) (s : TMState tm)
    (hs : s.config.BiTape = segment (stackAppend left (StackTape.cons none base)) bits tail) :
    Runs (seekLeftGap tm) s
      (segment base [] (stackAppend (left.reverse ++ bits) (StackTape.cons none tail)))
      (s.headPos - (left.length + 1 : ℕ)) (left.length + 1) := by
  induction left generalizing bits s with
  | nil =>
    have hm : Runs (FreeM.lift (.move .Left)) s
        (segment base [] (stackAppend bits (StackTape.cons none tail))) (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := seekLeftBlank tm) (time₂ := 0)
      (second := segment base [] (stackAppend bits (StackTape.cons none tail)))
      (pos₂ := s.headPos - 1) (by
        intro t ht hp
        simp [seekLeftBlank, ht, hp])
    simpa [seekLeftGap] using hr
  | cons bit left ih =>
    have hm : Runs (FreeM.lift (.move .Left)) s
        (segment (stackAppend left (StackTape.cons none base)) (bit :: bits) tail)
        (s.headPos - 1) 1 := by
      simpa [TMState.move, hs, sub_eq_add_neg] using move_correct s .Left
    have hr := hm.seq (q := seekLeftBlank tm) (time₂ := left.length + 1)
      (second := segment base []
        (stackAppend ((bit :: left).reverse ++ bits) (StackTape.cons none tail)))
      (pos₂ := s.headPos - ((bit :: left).length + 1 : ℕ)) (by
        intro t ht hp
        unfold seekLeftBlank
        apply runs_while_step (by simp [ht])
        have htape : t.config.BiTape =
            segment (stackAppend left (StackTape.cons none base)) (bit :: bits) tail := by simp [ht]
        convert ih (bit :: bits) t htape using 1 <;>
          simp [seekLeftGap, seekLeftBlank, List.reverse_cons, List.append_assoc, hp,
            sub_eq_add_neg, add_assoc]
        lia)
    simpa [seekLeftGap, Nat.add_comm] using hr

/--
The return-to-start program finishes on the first cell of the current region, or its ending blank if
the region is empty. It preserves the arbitrary regions beyond the separating blanks and uses
exactly `left.length + 2` head moves.
-/
theorem seekLeftEnd_segment (base : StackTape Bool) (left bits : List Bool)
    (tail : StackTape Bool) (s : TMState tm)
    (hs : s.config.BiTape = segment (stackAppend left (StackTape.cons none base)) bits tail) :
    Runs (seekLeftEnd tm) s (segment (StackTape.cons none base) (left.reverse ++ bits) tail)
      (s.headPos - left.length) (left.length + 2) := by
  have hg := seekLeftGap_segment base left bits tail s hs
  have hr := hg.seq (q := FreeM.lift (.move .Right)) (time₂ := 1)
    (second := segment (StackTape.cons none base) (left.reverse ++ bits) tail)
    (pos₂ := s.headPos - left.length) (by
      intro t ht hp
      convert move_correct t .Right using 1 <;>
        simp [TMState.move, ht, hp, sub_eq_add_neg, add_assoc])
  simpa [seekLeftEnd, seekLeftGap, Nat.add_assoc] using hr

/--
`shiftBitLeft tm bit` is a Turing machine program that expects the current cell to contain `bit` and
the cell to its left to be blank. It erases the current cell, writes `bit` into that left blank, and
finishes one cell to the right of its original position, ready to process the next source bit.
-/
def shiftBitLeft (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Left
  tape ←ₜ some bit
  moveₜ .Right
  moveₜ .Right

/--
Shifting one bit fills the blank immediately to its left and leaves its former cell blank. The head
finishes on the next source cell after exactly three head moves, and the regions surrounding the
shifted bit remain unchanged.
-/
theorem shiftBitLeft_correct (left : StackTape Bool) (bit : Bool) (bits : List Bool)
    (tail : StackTape Bool) (s : TMState tm)
    (hs : s.config.BiTape = segment (StackTape.cons none left) (bit :: bits) tail) :
    Runs (shiftBitLeft tm bit) s
      (segment (StackTape.cons none (StackTape.cons (some bit) left)) bits tail)
      (s.headPos + 1) 3 := by
  refine ⟨_, _, ⟨5, rfl⟩, ?_, ?_, ?_⟩
  · cases bits <;> simp [TMQuery.step, hs, segment, BiTape.write, BiTape.moveLeft, BiTape.moveRight]
  · simp [TMQuery.step, sub_eq_add_neg, add_assoc]
  · rfl

/--
`shiftLeft tm` is a Turing machine program that starts on the first bit of a contiguous block with a
blank immediately to its left. It moves each bit into the preceding blank, shifting the whole block
left by one cell. It stops on the blank just after the block's original location, preserving the bit
order.
-/
def shiftLeft (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some true then
      shiftBitLeft tm true
    else
      shiftBitLeft tm false

/--
The block shift moves every bit of `bits` one cell left without changing its value or order. It
preserves the surrounding regions, finishes `bits.length` cells to the right of the starting
coordinate, and uses exactly `3 * bits.length` head moves.
-/
theorem shiftLeft_correct (left : StackTape Bool) (bits : List Bool) (tail : StackTape Bool)
    (s : TMState tm) (hs : s.config.BiTape = segment (StackTape.cons none left) bits tail) :
    Runs (shiftLeft tm) s
      (segment (StackTape.cons none (stackAppend bits.reverse left)) [] tail)
      (s.headPos + bits.length) (3 * bits.length) := by
  induction bits generalizing left s with
  | nil =>
    simp [shiftLeft, hs]
  | cons bit bits ih =>
    unfold shiftLeft
    apply runs_while_step (by simp [hs])
    have hb : Runs (branch (.tapeIs (some true)) (shiftBitLeft tm true) (shiftBitLeft tm false)) s
        (segment (StackTape.cons none (StackTape.cons (some bit) left)) bits tail)
        (s.headPos + 1) 3 := by
      apply Runs.branch
      cases bit <;> simpa [hs] using shiftBitLeft_correct left _ bits tail s hs
    have hr := hb.seq (q := shiftLeft tm) (time₂ := 3 * bits.length)
      (second := segment (StackTape.cons none (stackAppend (bit :: bits).reverse left)) [] tail)
      (pos₂ := s.headPos + (bit :: bits).length) (by
        intro t ht hp
        have htape : t.config.BiTape =
            segment (StackTape.cons none (StackTape.cons (some bit) left)) bits tail := by simp [ht]
        simpa [List.reverse_cons, stackAppend_append, hp, add_assoc, add_comm, add_left_comm] using
          ih (StackTape.cons (some bit) left) t htape)
    simpa [shiftLeft, Nat.mul_add, Nat.add_comm] using hr

/--
`header doneBits` is a pure Lean function that describes the unary length header built so far: it
contains one `true` for each bit already copied. The header is stored to the left of the original
word.
-/
def header (doneBits : List Bool) : List Bool := List.replicate doneBits.length true

/--
`sourceLeft doneBits` is a pure Lean function that describes the cells to the left of the next
source bit. Moving left from the head encounters the processed source prefix in reverse order, then
a blank, and then the unary length header.
-/
def sourceLeft (doneBits : List Bool) : StackTape Bool :=
  stackAppend doneBits.reverse (StackTape.cons none (StackTape.mapSome (header doneBits)))

/--
`layout doneBits rest` is a pure Lean function that describes the copying loop between iterations.
From left to right, the tape contains a unary header, a blank, the source word `doneBits ++ rest`,
another blank, and the copied prefix `doneBits`. The head is on the first bit of `rest`, or on the
blank after the source word when `rest` is empty.
-/
def layout (doneBits rest : List Bool) : BiTape Bool :=
  segment (sourceLeft doneBits) rest (StackTape.mapSome doneBits)

/--
`destinationLeft doneBits rest` is a pure Lean function that describes the stack to the left of a
newly appended copy bit. It records the older copy bits, the separating blank, the unprocessed
source suffix, the temporarily erased source cell, and the processed prefix and header farther to
the left.
-/
def destinationLeft (doneBits rest : List Bool) : StackTape Bool :=
  stackAppend doneBits.reverse
    (StackTape.cons none (stackAppend rest.reverse (StackTape.cons none (sourceLeft doneBits))))

/--
`headerStart doneBits rest bit` is a pure Lean function that describes the tape after copying `bit`
and returning to the blank immediately before the unary header. The copied word has gained `bit`,
while its original source cell is still blank. This is where `restoreSource` extends the header
before returning to repair that source cell.
-/
def headerStart (doneBits rest : List Bool) (bit : Bool) : BiTape Bool :=
  segment StackTape.nil [] (stackAppend (header doneBits)
    (StackTape.cons none (stackAppend doneBits (StackTape.cons none
      (stackAppend rest (StackTape.cons none (StackTape.mapSome (doneBits ++ [bit]))))))))

/--
`putCopy tm bit` is a Turing machine program that temporarily erases the current source bit, scans
right across the remaining source and the existing copy, and appends `bit` to the copy region. It
finishes on the newly written copy bit. The erased source cell marks where the bit must later be
restored.
-/
def putCopy (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeAdvance tm none
  seekRightBlank tm
  moveₜ .Right
  seekRightBlank tm
  tape ←ₜ some bit

/--
`returnHeader tm` is a Turing machine program that starts on the newly appended copy bit and makes
four leftward scans to successive blanks. These scans cross the copy, the remaining source suffix,
the processed source prefix, and the unary header. It finishes on the blank immediately before the
header without changing any cells.
-/
def returnHeader (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftGap tm
  seekLeftGap tm
  seekLeftGap tm
  seekLeftGap tm

/--
`restoreSource tm bit` is a Turing machine program that starts on the blank before the unary header
and writes a new `true` there to extend it. It then scans right to the temporarily erased source
cell, restores `bit`, and advances to the next source cell. The source word is intact again when it
finishes.
-/
def restoreSource (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ some true
  seekRightBlank tm
  moveₜ .Right
  seekRightBlank tm
  writeAdvance tm (some bit)

/--
The append phase adds `bit` after the existing copied prefix and leaves the head on that new bit.
The source cell remains temporarily erased, and the head travels right by `rest.length +
doneBits.length + 2` cells using exactly that many head moves.
-/
theorem putCopy_correct (doneBits rest : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = layout doneBits (bit :: rest)) :
    Runs (putCopy tm bit) s (segment (destinationLeft doneBits rest) [bit] StackTape.nil)
      (s.headPos + (rest.length + doneBits.length + 2 : ℕ))
      (rest.length + doneBits.length + 2) := by
  have h0 : Runs (writeAdvance tm none) s
      (segment (StackTape.cons none (sourceLeft doneBits)) rest (StackTape.mapSome doneBits))
      (s.headPos + 1) 1 := by simpa [hs, layout] using writeAdvance_correct s none
  have h := h0.seq (by
    intro t ht hp
    have h1 := seekRightBlank_segment (StackTape.cons none (sourceLeft doneBits)) rest
      (StackTape.mapSome doneBits) t (by simp [ht])
    have h2 := h1.seq (by
      intro u hu hup
      have hm : Runs (FreeM.lift (.move .Right)) u
          (segment (StackTape.cons none
            (stackAppend rest.reverse (StackTape.cons none (sourceLeft doneBits))))
            doneBits StackTape.nil) (u.headPos + 1) 1 := by
        simpa [TMState.move, hu] using move_correct u .Right
      have h3 := hm.seq (by
        intro v hv hvp
        have hr := seekRightBlank_segment
          (StackTape.cons none
            (stackAppend rest.reverse (StackTape.cons none (sourceLeft doneBits))))
          doneBits StackTape.nil v (by simp [hv])
        have hw := hr.seq (by
          intro w hw hwp
          simpa [hw, hwp] using write_correct w (some bit))
        simpa [hvp] using hw)
      simpa [hup] using h3)
    simpa [hp] using h2)
  convert h using 1 <;> first | rfl | lia

/--
The restoration phase extends the header, repairs the erased source bit, and returns to the
copying-loop layout with `doneBits ++ [bit]` processed. It finishes on the next source cell and uses
exactly `2 * doneBits.length + 3` head moves.
-/
theorem restoreSource_correct (doneBits rest : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = headerStart doneBits rest bit) :
    Runs (restoreSource tm bit) s (layout (doneBits ++ [bit]) rest)
      (s.headPos + (2 * doneBits.length + 3 : ℕ)) (2 * doneBits.length + 3) := by
  let copied := doneBits ++ [bit]
  let remaining := stackAppend rest (StackTape.cons none (StackTape.mapSome copied))
  let source := stackAppend doneBits (StackTape.cons none remaining)
  have hheader : (true :: header doneBits).reverse = header copied := by
    simp [header, copied, ← List.replicate_succ]
  have hw : Runs (FreeM.lift (.write (some true))) s
      (segment StackTape.nil (true :: header doneBits) source) s.headPos 0 := by
    simpa [hs, headerStart, source, remaining, copied] using write_correct s (some true)
  have h := hw.seq (by
    intro t ht hp
    have hr := seekRightBlank_segment StackTape.nil (true :: header doneBits) source t
      (by simp [ht])
    have h1 := hr.seq (by
      intro u hu hup
      have hm : Runs (FreeM.lift (.move .Right)) u
          (segment (StackTape.cons none (StackTape.mapSome (header copied))) doneBits remaining)
          (u.headPos + 1) 1 := by
        simpa [TMState.move, hu, hheader, source] using move_correct u .Right
      have h2 := hm.seq (by
        intro v hv hvp
        have hsuffix := seekRightBlank_segment
          (StackTape.cons none (StackTape.mapSome (header copied))) doneBits remaining v
          (by simp [hv])
        have h3 := hsuffix.seq (by
          intro w hw hwp
          simpa [hw, hwp, remaining] using writeAdvance_correct w (some bit))
        simpa [hvp] using h3)
      simpa [hup] using h2)
    simpa [hp] using h1)
  simp only [header, List.length_replicate] at h
  convert h using 1
  · rfl
  · simp [layout, sourceLeft, copied, header, List.reverse_cons]
  · lia
  · lia

/--
The four leftward scans preserve the source and copy regions and finish on the blank before the
header. Their total displacement to the left and exact head-move cost are both `rest.length + 3 *
doneBits.length + 4`.
-/
theorem returnHeader_correct (doneBits rest : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = segment (destinationLeft doneBits rest) [bit] StackTape.nil) :
    Runs (returnHeader tm) s (headerStart doneBits rest bit)
      (s.headPos - (rest.length + 3 * doneBits.length + 4 : ℕ))
      (rest.length + 3 * doneBits.length + 4) := by
  let copied := doneBits ++ [bit]
  let remaining := stackAppend rest (StackTape.cons none (StackTape.mapSome copied))
  let source := stackAppend doneBits (StackTape.cons none remaining)
  have h0 := seekLeftGap_segment
    (stackAppend rest.reverse (StackTape.cons none (sourceLeft doneBits)))
    doneBits.reverse [bit] StackTape.nil s (by simpa [destinationLeft] using hs)
  have h := h0.seq (by
    intro t ht hp
    have h1 := seekLeftGap_segment (sourceLeft doneBits) rest.reverse []
      (StackTape.mapSome copied) t (by simp [ht, copied])
    have h2 := h1.seq (by
      intro u hu hup
      have hr := seekLeftGap_segment (StackTape.mapSome (header doneBits)) doneBits.reverse []
        remaining u (by simp [hu, sourceLeft, remaining])
      have h3 := hr.seq (by
        intro v hv hvp
        have hg := seekLeftGap_segment StackTape.nil (header doneBits) [] source v
          (by simp [hv, source, stackAppend_nil])
        simpa [hvp] using hg)
      simpa [hup] using h3)
    simpa [hp] using h2)
  simp only [header, List.reverse_replicate, List.length_reverse, List.length_replicate] at h
  convert h using 1 <;> first | rfl | lia

/--
`copyBit tm bit` is a Turing machine program that copies the current source bit into the separate
region on the right, returns left to extend the unary header, and restores the original source bit.
It finishes on the next source cell, ready for another iteration.
-/
def copyBit (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  putCopy tm bit
  returnHeader tm
  restoreSource tm bit

/--
One copying iteration preserves the source word, extends the copied prefix and unary header by one
bit, and advances the head to the next source cell. Its exact cost is `2 * rest.length + 6 *
doneBits.length + 9` head moves.
-/
theorem copyBit_correct (doneBits rest : List Bool) (bit : Bool) (s : TMState tm)
    (hs : s.config.BiTape = layout doneBits (bit :: rest)) :
    Runs (copyBit tm bit) s (layout (doneBits ++ [bit]) rest) (s.headPos + 1)
      (2 * rest.length + 6 * doneBits.length + 9) := by
  have h := (putCopy_correct doneBits rest bit s hs).seq (by
    intro t ht hp
    have hr := returnHeader_correct doneBits rest bit t (by simp [ht])
    have hw := hr.seq (by
      intro u hu hup
      simpa [hup] using restoreSource_correct doneBits rest bit u (by simp [hu]))
    simpa [hp] using hw)
  convert h using 1 <;> first | rfl | lia

/--
`copyLoop tm` is a Turing machine program that processes every remaining source bit by selecting the
corresponding `copyBit` program through a tape-symbol test. Each iteration restores the source bit,
grows the copy and header, and advances to the next source cell. The loop stops on the blank after
the source word, leaving the copy separated from it by that blank.
-/
def copyLoop (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some true then
      copyBit tm true
    else
      copyBit tm false

/--
The copying loop extends the processed prefix from `doneBits` to `doneBits ++ bits` while preserving
the source and building the matching header and copy. It finishes on the blank after the source word
and uses exactly `4 * bits.length ^ 2 + 6 * doneBits.length * bits.length + 5 * bits.length` head
moves.
-/
theorem copyLoop_correct (doneBits bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = layout doneBits bits) :
    Runs (copyLoop tm) s (layout (doneBits ++ bits) []) (s.headPos + bits.length)
      (4 * bits.length ^ 2 + 6 * doneBits.length * bits.length + 5 * bits.length) := by
  induction bits generalizing doneBits s with
  | nil =>
    simp [copyLoop, hs, layout]
  | cons bit bits ih =>
    unfold copyLoop
    apply runs_while_step (by simp [hs, layout])
    have hb : Runs (branch (.tapeIs (some true)) (copyBit tm true) (copyBit tm false)) s
        (layout (doneBits ++ [bit]) bits) (s.headPos + 1)
        (2 * bits.length + 6 * doneBits.length + 9) := by
      apply Runs.branch
      cases bit <;> simpa [hs, layout] using copyBit_correct doneBits bits _ s hs
    have h := hb.seq (q := copyLoop tm)
      (second := layout (doneBits ++ bit :: bits) []) (pos₂ := s.headPos + 1 + bits.length)
      (time₂ := 4 * bits.length ^ 2 + 6 * (doneBits.length + 1) * bits.length + 5 * bits.length)
      (by
        intro t ht hp
        have htape : t.config.BiTape = layout (doneBits ++ [bit]) bits := by simp [ht]
        simpa [List.append_assoc, hp] using ih (doneBits ++ [bit]) t htape)
    convert h using 1 <;>
      first | rfl | (simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)

/--
`finishCopy tm` is a Turing machine program that starts on the blank between the completed source
and its copy. It shifts the copy one cell left to join the two words, then replaces the blank
between the unary header and source with `false`. It returns to the first header cell, producing the
contiguous Boolean pair encoding.
-/
def finishCopy (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  shiftLeft tm
  moveₜ .Left
  seekLeftGap tm
  tape ←ₜ some false
  seekLeftEnd tm

/--
`duplicate tm` is a Turing machine program that starts on the first cell of the input and builds an
encoding of two copies on the same tape. It first runs the copying loop and then joins the regions
into a word of the form `true` repeated `input.length` times, followed by `false`, the input, and
the input again. It finishes on the first output cell, to the left of the original input.
-/
def duplicate (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  copyLoop tm
  finishCopy tm

/--
Finishing the copy transforms the completed loop layout into `BooleanTapeEncoding.pair input input`
and puts the head on the first output cell. From the blank after the source, the head finishes `2 *
input.length + 1` cells to the left, using exactly `6 * input.length + 5` head moves.
-/
theorem finishCopy_correct (input : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = layout input []) :
    Runs (finishCopy tm) s (BiTape.mk₁ (BooleanTapeEncoding.pair input input))
      (s.headPos - (2 * input.length + 1 : ℕ)) (6 * input.length + 5) := by
  have hm : Runs (FreeM.lift (.move .Right)) s
      (segment (StackTape.cons none (sourceLeft input)) input StackTape.nil) (s.headPos + 1) 1 := by
    simpa [TMState.move, hs, layout] using move_correct s .Right
  have h := hm.seq (by
    intro t ht hp
    have hshift := shiftLeft_correct (sourceLeft input) input StackTape.nil t (by simp [ht])
    have h1 := hshift.seq (by
      intro u hu hup
      have hm' : Runs (FreeM.lift (.move .Left)) u
          (segment (stackAppend (input ++ input).reverse
            (StackTape.cons none (StackTape.mapSome (header input)))) [] StackTape.nil)
          (u.headPos - 1) 1 := by
        simpa [TMState.move, hu, sourceLeft, List.reverse_append, stackAppend_append,
          sub_eq_add_neg] using move_correct u .Left
      have h2 := hm'.seq (by
        intro v hv hvp
        have hg := seekLeftGap_segment (StackTape.mapSome (header input))
          (input ++ input).reverse [] StackTape.nil v (by simp [hv])
        have h3 := hg.seq (by
          intro w hw hwp
          have hw' : Runs (FreeM.lift (.write (some false))) w
              (segment (StackTape.mapSome (header input)) (false :: (input ++ input)) StackTape.nil)
              w.headPos 0 := by simpa [hw] using write_correct w (some false)
          have h4 := hw'.seq (by
            intro z hz hzp
            have hr := seekLeftEnd_segment StackTape.nil (header input)
              (false :: (input ++ input)) StackTape.nil z (by simp [hz])
            simpa [hzp] using hr)
          simpa [hwp] using h4)
        simpa [hvp] using h3)
      simpa [hup] using h2)
    simpa [hp] using h1)
  simp only [header, List.reverse_replicate, List.length_replicate] at h
  convert h using 1 <;> first | rfl | lia

/--
Duplication produces the Boolean pair encoding of `(input, input)`, preserves the control state, and
finishes `input.length + 1` cells to the left of the original coordinate. Its exact cost is `4 *
input.length ^ 2 + 11 * input.length + 5` head moves. Empty input produces the one-bit word
`[false]`.
-/
theorem duplicate_correct (input : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    Runs (duplicate tm) s (BiTape.mk₁ (BooleanTapeEncoding.pair input input))
      (s.headPos - (input.length + 1 : ℕ)) (4 * input.length ^ 2 + 11 * input.length + 5) := by
  have hl : Runs (copyLoop tm) s (layout input []) (s.headPos + input.length)
      (4 * input.length ^ 2 + 5 * input.length) := by
    simpa using copyLoop_correct [] input s (by simpa [layout, sourceLeft, header] using hs)
  have h := hl.seq (by
    intro t ht hp
    simpa [hp] using finishCopy_correct input t (by simp [ht]))
  convert h using 1 <;> first | rfl | lia

/--
This value packages the copying Turing machine program with its output and cost guarantees. It
produces the Boolean pair encoding of two copies, puts the head on the first output cell at `origin
- (input.length + 1)`, and obeys the quadratic bound `4 * input.length ^ 2 + 11 * input.length + 5`
on head moves.
-/
@[simps program]
def duplicateComputer : Duplicator (tm := tm)
    (fun input => 4 * input.length ^ 2 + 11 * input.length + 5)
    (fun input origin => origin - (input.length + 1 : ℕ)) where
  program := duplicate tm
  correct input s hs := by
    obtain ⟨cost, final, hc, ht, hp, htime⟩ := duplicate_correct input s hs
    exact ⟨cost, final, hc, ht, hp, htime.le⟩

/--
Duplication allocates no more new cells than its exact head-move count of `4 * input.length ^ 2 + 11
* input.length + 5`. Its final allocation count includes every cell already recorded in the initial
state, as well as any cells added during copying.
-/
theorem duplicate_space (input : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (duplicate tm) s cost final ∧
      cost.steps = 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      cost.cellsAllocated ≤ 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      final.cellsAllocated.card ≤
        s.cellsAllocated.card + (4 * input.length ^ 2 + 11 * input.length + 5) :=
  (duplicate_correct input s hs).space

/--
This value proves polynomial-time computability of producing the Boolean pair encoding of two copies
of the input. It uses the physical duplication program and its quadratic head-move bound, with the
head finishing at the beginning of the encoded output.
-/
noncomputable def duplicatePolyTimeComputable :
    TMQuery.PolyTimeComputable (fun input => BooleanTapeEncoding.pair input input) :=
  EncodedComputer.polyTimeComputable (tm := tm)
    (outputEncoding := fun p : List Bool × List Bool => BooleanTapeEncoding.pair p.1 p.2)
    (f := fun input => (input, input))
    (position := fun input origin => origin - (input.length + 1 : ℕ))
    (poly := 4 * Polynomial.X ^ 2 + 11 * Polynomial.X + 5)
    (EncodedComputer.mono (duplicateComputer (tm := tm)) (by intro input; simp))

end Algolean.Algorithms.SingleTapeTuringMachines.Copying
