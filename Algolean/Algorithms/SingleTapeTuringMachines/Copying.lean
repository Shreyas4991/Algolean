/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Scanning
public import Algolean.Algorithms.SingleTapeTuringMachines.BitOperations
public import Algolean.Models.SingleTapeTM.Composition.Pairing
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Copying Boolean words on a single tape

The auxiliary tape views expose contiguous regions separated by blanks. Their logical lists
occur only in contracts; the executable scans inspect one head symbol at a time.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.Copying

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

/-- Prepend a finite Boolean block to an arbitrary stack, retaining any internal blank markers. -/
@[simp] def stackAppend : List Bool → StackTape Bool → StackTape Bool
  | [], tail => tail
  | bit :: bits, tail => StackTape.cons (some bit) (stackAppend bits tail)

theorem stackAppend_append (first second : List Bool) (tail : StackTape Bool) :
    stackAppend (first ++ second) tail = stackAppend first (stackAppend second tail) := by
  induction first <;> simp_all

@[simp] theorem stackAppend_nil (bits : List Bool) :
    stackAppend bits StackTape.nil = StackTape.mapSome bits := by
  induction bits <;> simp_all

/-- A contiguous suffix followed by a blank separator and an arbitrary further region.
When the suffix is empty, the head is on the separator. -/
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

/-- Write a fixed symbol and advance right by one cell. -/
def writeAdvance (tm : SingleTapeTM Bool) (symbol : Option Bool) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  tape ←ₜ symbol
  moveₜ .Right

theorem writeAdvance_correct (s : TMState tm) (symbol : Option Bool) :
    Runs (writeAdvance tm symbol) s ((s.config.BiTape.write symbol).moveRight) (s.headPos + 1) 1 :=
  ⟨_, _, ⟨2, rfl⟩, rfl, rfl, rfl⟩

/-- A right scan preserves every cell beyond the first blank separator. -/
theorem seekRightBlank_segment (left : StackTape Bool) (bits : List Bool) (tail : StackTape Bool)
    (s : TMState tm) (hs : s.config.BiTape = segment left bits tail) :
    Runs (seekRightBlank tm) s (segment (stackAppend bits.reverse left) [] tail)
      (s.headPos + bits.length) bits.length := by
  induction bits generalizing left s with
  | nil =>
    simpa [seekRightBlank, hs] using runs_while_false (.not (.tapeIs none))
      (FreeM.lift (.move .Right)) s (by simp [hs])
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

/-- Move left at least once, then stop at the first blank. -/
def seekLeftGap (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftBlank tm

/-- Return to the blank before the current region, retaining both neighboring regions. -/
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
        simpa [seekLeftBlank, ht, hp] using runs_while_false (.not (.tapeIs none))
          (FreeM.lift (.move .Left)) t (by simp [ht]))
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

/-- Return to the first bit of a region, preserving arbitrary regions beyond its separators. -/
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

/-- Move one fixed bit into the blank to its left, then advance to the next source cell. -/
def shiftBitLeft (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Left
  tape ←ₜ some bit
  moveₜ .Right
  moveₜ .Right

/-- The local shift is implemented by two writes and three charged head moves. -/
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

/-- Shift a contiguous block left into an adjacent blank, leaving the next blank under the head. -/
def shiftLeft (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some true then
      shiftBitLeft tm true
    else
      shiftBitLeft tm false

/-- A left shift preserves both neighboring regions and costs exactly three moves per bit. -/
theorem shiftLeft_correct (left : StackTape Bool) (bits : List Bool) (tail : StackTape Bool)
    (s : TMState tm) (hs : s.config.BiTape = segment (StackTape.cons none left) bits tail) :
    Runs (shiftLeft tm) s
      (segment (StackTape.cons none (stackAppend bits.reverse left)) [] tail)
      (s.headPos + bits.length) (3 * bits.length) := by
  induction bits generalizing left s with
  | nil =>
    simpa [shiftLeft, hs] using runs_while_false (.not (.tapeIs none))
      (branch (.tapeIs (some true)) (shiftBitLeft tm true) (shiftBitLeft tm false)) s
      (by simp [hs])
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

/-- Unary length header accumulated to the left of the original word. -/
def header (doneBits : List Bool) : List Bool := List.replicate doneBits.length true

/-- Cells to the left of the current source bit: processed prefix, blank, and unary header. -/
def sourceLeft (doneBits : List Bool) : StackTape Bool :=
  stackAppend doneBits.reverse (StackTape.cons none (StackTape.mapSome (header doneBits)))

/-- Copy-loop invariant: a source suffix, a separated copied prefix, and a left unary header. -/
def layout (doneBits rest : List Bool) : BiTape Bool :=
  segment (sourceLeft doneBits) rest (StackTape.mapSome doneBits)

/-- Cells preceding the newly appended copy bit. -/
def destinationLeft (doneBits rest : List Bool) : StackTape Bool :=
  stackAppend doneBits.reverse
    (StackTape.cons none (stackAppend rest.reverse (StackTape.cons none (sourceLeft doneBits))))

/-- The leftmost blank where the next unary-header bit is written. -/
def headerStart (doneBits rest : List Bool) (bit : Bool) : BiTape Bool :=
  segment StackTape.nil [] (stackAppend (header doneBits)
    (StackTape.cons none (stackAppend doneBits (StackTape.cons none
      (stackAppend rest (StackTape.cons none (StackTape.mapSome (doneBits ++ [bit]))))))))

/-- Mark the source cell and append its fixed bit to the separate copy region. -/
def putCopy (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeAdvance tm none
  seekRightBlank tm
  moveₜ .Right
  seekRightBlank tm
  tape ←ₜ some bit

/-- Return through the four blank-separated regions to the start of the length header. -/
def returnHeader (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekLeftGap tm
  seekLeftGap tm
  seekLeftGap tm
  seekLeftGap tm

/-- Extend the unary header, restore the marked bit, and advance to the next source cell. -/
def restoreSource (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ some true
  seekRightBlank tm
  moveₜ .Right
  seekRightBlank tm
  writeAdvance tm (some bit)

/-- The append phase's exact tape, head position, and linear head-move cost. -/
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

/-- Extending the header restores the marked source and advances exactly one source cell. -/
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

/-- Four leftward scans reach the next header cell without disturbing the source or copy. -/
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

/-- Copy the current bit, extending the unary header and restoring the original source cell. -/
def copyBit (tm : SingleTapeTM Bool) (bit : Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  putCopy tm bit
  returnHeader tm
  restoreSource tm bit

/-- One complete copy iteration preserves the source and extends the copied prefix by one bit. -/
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

/-- Copy every source bit using only embedded head-symbol tests. -/
def copyLoop (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some true then
      copyBit tm true
    else
      copyBit tm false

/-- The full copying loop has a quadratic exact time bound and retains arbitrary prior space. -/
theorem copyLoop_correct (doneBits bits : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = layout doneBits bits) :
    Runs (copyLoop tm) s (layout (doneBits ++ bits) []) (s.headPos + bits.length)
      (4 * bits.length ^ 2 + 6 * doneBits.length * bits.length + 5 * bits.length) := by
  induction bits generalizing doneBits s with
  | nil =>
    simpa [copyLoop, hs, layout] using runs_while_false (.not (.tapeIs none))
      (branch (.tapeIs (some true)) (copyBit tm true) (copyBit tm false)) s (by simp [hs, layout])
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

/-- Close the copy separator, write the header delimiter, and return to the first output cell. -/
def finishCopy (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  shiftLeft tm
  moveₜ .Left
  seekLeftGap tm
  tape ←ₜ some false
  seekLeftEnd tm

/-- Duplicate a word into the Boolean pair encoding; the input is supplied only on the tape. -/
def duplicate (tm : SingleTapeTM Bool) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  copyLoop tm
  finishCopy tm

/-- Closing and encoding the copy costs linear time and positions the head on the unary header. -/
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

/-- Duplication produces the pair encoding, including empty input, and has exact quadratic time. -/
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

/-- A physical Boolean duplicator carrying its uniform correctness and complexity proof. -/
@[simps program]
def duplicateComputer : Duplicator (tm := tm)
    (fun input => 4 * input.length ^ 2 + 11 * input.length + 5)
    (fun input origin => origin - (input.length + 1 : ℕ)) where
  program := duplicate tm
  correct input s hs := by
    obtain ⟨cost, final, hc, ht, hp, htime⟩ := duplicate_correct input s hs
    exact ⟨cost, final, hc, ht, hp, htime.le⟩

/-- Duplication retains previous space history and charges no more new cells than its time. -/
theorem duplicate_space (input : List Bool) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (duplicate tm) s cost final ∧
      cost.steps = 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      cost.cellsAllocated ≤ 4 * input.length ^ 2 + 11 * input.length + 5 ∧
      final.cellsAllocated.card ≤
        s.cellsAllocated.card + (4 * input.length ^ 2 + 11 * input.length + 5) :=
  (duplicate_correct input s hs).space

/-- The physical duplication program supplies a uniform polynomial-time word transformation. -/
noncomputable def duplicatePolyTimeComputable :
    TMQuery.PolyTimeComputable (fun input => BooleanTapeEncoding.pair input input) :=
  EncodedComputer.polyTimeComputable (tm := tm)
    (outputEncoding := fun p : List Bool × List Bool => BooleanTapeEncoding.pair p.1 p.2)
    (f := fun input => (input, input))
    (position := fun input origin => origin - (input.length + 1 : ℕ))
    (poly := 4 * Polynomial.X ^ 2 + 11 * Polynomial.X + 5)
    (by simpa using duplicateComputer (tm := tm))

end Algolean.Algorithms.SingleTapeTuringMachines.Copying
