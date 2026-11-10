/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Copying

/-!
# Moving between words separated by blank cells

* `nextRegion` crosses the current word and its following blank.
* `previousRegion` crosses the preceding blank and returns to the preceding word's beginning.
* Both programs preserve the tape and control state. Their time bounds count every head move.

The correctness theorems describe the neighboring words explicitly and allow arbitrary tape
contents beyond their separating blanks. These are machine templates instantiated within a
containing Query program. Their instructions do not depend on the words or their lengths.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This machine template scans to the blank after the current word and moves right once.
The containing machine includes this fixed program independently of the input length.
-/
def nextRegion (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Right

/--
The head reaches the following word after crossing the current word and one blank.
Both words and the tape beyond them remain unchanged.
-/
theorem nextRegion_correct (left : StackTape Γ) (current following : List Γ)
    (tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left current
      (StackTape.prepend following (StackTape.cons none tail))) :
    Runs (nextRegion tm) s
      (BiTape.segment (StackTape.cons none (StackTape.prepend current.reverse left))
        following tail)
      (s.headPos + (current.length + 1 : Nat)) (current.length + 1) := by
  have h := (seekRightBlank_segment left current
    (StackTape.prepend following (StackTape.cons none tail)) s htape).append_move .Right
  cases following <;>
    simpa [nextRegion, Copying.segment, BiTape.segment, BiTape.moveRight,
      Nat.cast_add, add_assoc] using h

/--
This machine template moves left onto the separating blank and returns to the preceding word.
The containing machine includes this fixed program independently of the input length.
-/
def previousRegion (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftEnd tm

/--
The head returns to the preceding word's first cell, or its ending blank if that word is empty.
It preserves both words and their neighbors and uses the preceding word's length plus three moves.
-/
theorem previousRegion_correct (left : StackTape Γ) (preceding current : List Γ)
    (tail : StackTape Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.cons none (StackTape.prepend preceding.reverse (StackTape.cons none left)))
      current tail) :
    Runs (previousRegion tm) s
      (BiTape.segment (StackTape.cons none left) preceding
        (StackTape.prepend current (StackTape.cons none tail)))
      (s.headPos - (preceding.length + 1 : Nat)) (preceding.length + 3) := by
  have hm : Runs (FreeM.lift (.move .Left)) s
      (BiTape.segment (StackTape.prepend preceding.reverse (StackTape.cons none left)) []
        (StackTape.prepend current (StackTape.cons none tail)))
      (s.headPos - 1) 1 := by
    simpa [htape, sub_eq_add_neg] using move_correct s .Left
  have hr := hm.seq (q := seekLeftEnd tm)
    (second := BiTape.segment (StackTape.cons none left) preceding
      (StackTape.prepend current (StackTape.cons none tail)))
    (pos₂ := s.headPos - (preceding.length + 1 : Nat))
    (time₂ := preceding.length + 2) (by
      intro middle hmiddle hpos
      simpa [hpos, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        seekLeftEnd_segment left preceding.reverse []
          (StackTape.prepend current (StackTape.cons none tail)) middle
          (congrArg SingleTapeTM.Cfg.BiTape hmiddle))
  simpa [previousRegion, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

end Algolean.Algorithms.SingleTapeTuringMachines
