/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Copying

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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/--
This machine template scans to the blank after the current word and moves right once.
The containing machine includes this fixed program independently of the input length.
-/
def nextRegion (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  moveₜ .Right

/-- Crossing the word and its following blank reaches the next word in exactly that many moves. -/
@[spec] theorem nextRegion_spec (left : StackTape Γ) (current following : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label, BiTape.segment left current
        (StackTape.prepend following (StackTape.cons none tail))⟩ ∧
        initial.headPos = origin ∧ cost.steps = elapsed ⦄
      nextRegion tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none (StackTape.prepend current.reverse left))
          following tail⟩ ∧
        final.headPos = origin + (current.length + 1 : Nat) ∧
        cost.steps = elapsed + current.length + 1 ⦄ := by
  vcgen [nextRegion, seekRightBlank_segment_spec left
    (StackTape.prepend following (StackTape.cons none tail)) current label origin elapsed]
  all_goals
    simp_all [TMState.move, TMState.moveCost]
    all_goals lia

/-- Crossing the current word preserves the tape and increases an upper bound on time. -/
theorem nextRegion_le_spec (left : StackTape Γ) (current following : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label, BiTape.segment left current
        (StackTape.prepend following (StackTape.cons none tail))⟩ ∧
        initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      nextRegion tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none (StackTape.prepend current.reverse left))
          following tail⟩ ∧
        final.headPos = origin + (current.length + 1 : Nat) ∧
        cost.steps ≤ elapsed + current.length + 1 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial machineState ⟨hcfg, hpos, hcost⟩
  vcgen [nextRegion_spec left current following tail label origin initial.steps]
  all_goals simp_all

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
  apply Spec.runs
  vcgen [nextRegion_spec left current following tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template moves left onto the separating blank and returns to the preceding word.
The containing machine includes this fixed program independently of the input length.
-/
def previousRegion (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Left
  seekLeftEnd tm

/-- Returning to the preceding word preserves both words and counts every move. -/
@[spec] theorem previousRegion_spec (left : StackTape Γ) (preceding current : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label, BiTape.segment
        (StackTape.cons none (StackTape.prepend preceding.reverse (StackTape.cons none left)))
        current tail⟩ ∧ initial.headPos = origin ∧ cost.steps = elapsed ⦄
      previousRegion tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left) preceding
          (StackTape.prepend current (StackTape.cons none tail))⟩ ∧
        final.headPos = origin - (preceding.length + 1 : Nat) ∧
        cost.steps = elapsed + preceding.length + 3 ⦄ := by
  vcgen [previousRegion, seekLeftEnd_segment_spec left
    (StackTape.prepend current (StackTape.cons none tail)) preceding.reverse []
    label (origin - 1) (elapsed + 1)]
  all_goals
    simp_all [TMState.move, TMState.moveCost]
    all_goals lia

/-- Returning to the preceding word preserves the tape and increases its upper time bound. -/
theorem previousRegion_le_spec (left : StackTape Γ) (preceding current : List Γ)
    (tail : StackTape Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost initial => initial.config = ⟨label, BiTape.segment
        (StackTape.cons none (StackTape.prepend preceding.reverse (StackTape.cons none left)))
        current tail⟩ ∧ initial.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      previousRegion tm
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left) preceding
          (StackTape.prepend current (StackTape.cons none tail))⟩ ∧
        final.headPos = origin - (preceding.length + 1 : Nat) ∧
        cost.steps ≤ elapsed + preceding.length + 3 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial machineState ⟨hcfg, hpos, hcost⟩
  vcgen [previousRegion_spec left preceding current tail label origin initial.steps]
  all_goals simp_all

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
  apply Spec.runs
  vcgen [previousRegion_spec left preceding current tail s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

/--
This machine template temporarily erases the scanned symbol, runs a fixed program on the
preceding region, and returns to restore that symbol. The blank marks the return position.
The containing machine fixes `restore` and `action` once for each of its finite symbol cases.
-/
def visitPreviousRegion (tm : SingleTapeTM Γ) (restore : Γ)
    (action : Prog (TMQuery tm) Unit) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  seekLeftEnd tm
  previousRegion tm
  action
  nextRegion tm
  seekRightBlank tm
  tape ←ₜ some restore

/--
The visit may change both the preceding word and the tape beyond the current region. The
current symbol and the words crossed during the visit are preserved. The preceding word's
right boundary must stay at the same coordinate, so the program can return to its starting cell.
-/
theorem visitPreviousRegion_tail_spec (restore : Γ) (action : Prog (TMQuery tm) Unit)
    (input output crossed suffix : List Γ) (tail resultTail : StackTape Γ) (bound : Nat)
    (label result : Option tm.State) (origin : ℤ) (elapsed : Nat)
    (haction : ∀ (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil input
          (StackTape.prepend crossed (StackTape.cons none
            (StackTape.prepend suffix (StackTape.cons none tail))))⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment StackTape.nil output
          (StackTape.prepend crossed (StackTape.cons none
            (StackTape.prepend suffix (StackTape.cons none resultTail))))⟩ ∧
          final.headPos = origin + input.length - output.length ∧ cost.steps ≤ elapsed + bound ⦄) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome input.reverse)))
        (restore :: suffix) tail⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitPreviousRegion tm restore action
    ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome output.reverse)))
        (restore :: suffix) resultTail⟩ ∧ final.headPos = origin ∧
        cost.steps ≤ elapsed + bound + 2 * crossed.length + input.length + output.length + 6 ⦄ := by
  let rest := StackTape.prepend suffix (StackTape.cons none tail)
  let after := StackTape.prepend suffix (StackTape.cons none resultTail)
  unfold visitPreviousRegion
  iterate 3 rw [← bind_assoc]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨result, BiTape.segment StackTape.nil output
      (StackTape.prepend crossed (StackTape.cons none after))⟩ ∧
    current.headPos = origin - crossed.length - (output.length + 1 : Nat) ∧
    cost.steps ≤ elapsed + crossed.length + input.length + bound + 5)
  · apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    vcgen [seekLeftEnd_segment_spec (StackTape.mapSome input.reverse) rest
        crossed.reverse [] label origin initial.steps,
      previousRegion_spec StackTape.nil input crossed rest label (origin - crossed.length)
        (initial.steps + crossed.length + 2),
      haction (origin - crossed.length - (input.length + 1 : Nat))
        (initial.steps + crossed.length + 2 + input.length + 3)]
    all_goals
      simp_all [TMState.write, rest, after, BiTape.segment, BiTape.write]
      all_goals lia
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    vcgen [nextRegion_spec StackTape.nil output crossed after result
        (origin - crossed.length - (output.length + 1 : Nat)) initial.steps,
      seekRightBlank_segment_spec (StackTape.cons none (StackTape.mapSome output.reverse))
        after crossed result (origin - crossed.length) (initial.steps + output.length + 1)]
    all_goals
      simp_all [TMState.write, after, BiTape.segment, BiTape.write]
      all_goals lia

/--
The visit changes the preceding word, preserves its neighbors, and restores the head.
The assertion about `action` states its output, result state, and move bound. The end of its
output must remain at the same coordinate as the end of its input.
-/
@[spec] theorem visitPreviousRegion_spec (restore : Γ) (action : Prog (TMQuery tm) Unit)
    (input output crossed suffix : List Γ) (tail : StackTape Γ) (bound : Nat)
    (label result : Option tm.State) (origin : ℤ) (elapsed : Nat)
    (haction : ∀ (tail : StackTape Γ) (origin : ℤ) (elapsed : Nat),
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil input tail⟩ ∧
          current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment StackTape.nil output tail⟩ ∧
          final.headPos = origin + input.length - output.length ∧ cost.steps ≤ elapsed + bound ⦄) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome input.reverse)))
        (restore :: suffix) tail⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitPreviousRegion tm restore action
    ⦃ fun _ cost final => final.config = ⟨result, BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome output.reverse)))
        (restore :: suffix) tail⟩ ∧ final.headPos = origin ∧
        cost.steps ≤ elapsed + bound + 2 * crossed.length + input.length + output.length + 6 ⦄ := by
  apply visitPreviousRegion_tail_spec restore action input output crossed suffix tail tail bound
    label result origin elapsed
  intro position steps
  exact haction (StackTape.prepend crossed (StackTape.cons none
    (StackTape.prepend suffix (StackTape.cons none tail)))) position steps

/--
A visit may also record its answer in the control state. The inserted program changes the
preceding word, keeps its right boundary fixed, and sets the stated result. The visit restores
the scanned symbol and head position while keeping that result.
-/
theorem visitPreviousRegion_completes (restore : Γ) (action : Prog (TMQuery tm) Unit)
    (input output crossed suffix : List Γ) (tail : StackTape Γ)
    (result : Option tm.State) (bound : Nat)
    (haction : ∀ (s : TMState tm) (tail : StackTape Γ),
      s.config.BiTape = BiTape.segment StackTape.nil input tail →
      ∃ cost final, Completes action s cost final ∧
        final.config = ⟨result, BiTape.segment StackTape.nil output tail⟩ ∧
        final.headPos = s.headPos + input.length - output.length ∧ cost.steps ≤ bound)
    (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome input.reverse)))
      (restore :: suffix) tail) :
    ∃ cost final, Completes (visitPreviousRegion tm restore action) s cost final ∧
      final.config = ⟨result, BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome output.reverse)))
        (restore :: suffix) tail⟩ ∧ final.headPos = s.headPos ∧
      cost.steps ≤ bound + 2 * crossed.length + input.length + output.length + 6 := by
  apply Spec.completes
  have ha (neighbor : StackTape Γ) (position : ℤ) (elapsed : Nat) :
      ⦃ fun cost current => current.config =
          ⟨s.config.state, BiTape.segment StackTape.nil input neighbor⟩ ∧
          current.headPos = position ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config =
          ⟨result, BiTape.segment StackTape.nil output neighbor⟩ ∧
          final.headPos = position + input.length - output.length ∧
          cost.steps ≤ elapsed + bound ⦄ := by
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    obtain ⟨cost, final, hc, hf, hh, hb⟩ := haction current neighbor (by simp [hcfg])
    vcgen [Spec.steps hc initial.steps]
    all_goals
      simp_all
      all_goals lia
  vcgen [visitPreviousRegion_spec restore action input output crossed suffix tail bound
    s.config.state result s.headPos 0 ha]
  all_goals
    cases hcfg : s.config
    simp_all

/--
Visiting the preceding region changes only that region and restores the scanned cell and head.
The inserted program must preserve its right neighbor and leave the blank after its output at
the same absolute coordinate. Its bound and the lengths of the crossed words bound the visit.
-/
theorem visitPreviousRegion_correct (restore : Γ) (action : Prog (TMQuery tm) Unit)
    (input output crossed suffix : List Γ) (tail : StackTape Γ) (bound : Nat)
    (haction : ∀ (s : TMState tm) (tail : StackTape Γ),
      s.config.BiTape = BiTape.segment StackTape.nil input tail →
      ∃ moves, Runs action s (BiTape.segment StackTape.nil output tail)
        (s.headPos + input.length - output.length) moves ∧ moves ≤ bound)
    (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome input.reverse)))
      (restore :: suffix) tail) :
    ∃ moves, Runs (visitPreviousRegion tm restore action) s
      (BiTape.segment
        (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome output.reverse)))
        (restore :: suffix) tail) s.headPos moves ∧
      moves ≤ bound + 2 * crossed.length + input.length + output.length + 6 := by
  have ha (neighbor : StackTape Γ) (position : ℤ) (elapsed : Nat) :
      ⦃ fun cost current => current.config =
          ⟨s.config.state, BiTape.segment StackTape.nil input neighbor⟩ ∧
          current.headPos = position ∧ cost.steps ≤ elapsed ⦄
        action
      ⦃ fun _ cost final => final.config =
          ⟨s.config.state, BiTape.segment StackTape.nil output neighbor⟩ ∧
          final.headPos = position + input.length - output.length ∧
          cost.steps ≤ elapsed + bound ⦄ := by
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hbound⟩
    obtain ⟨moves, ⟨cost, final, hc, hf, hh, hb⟩, htime⟩ :=
      haction current neighbor (by simp [hcfg])
    vcgen [Spec.steps hc initial.steps]
    all_goals
      simp_all
      all_goals lia
  obtain ⟨cost, final, hc, hf, hh, hb⟩ :
      ∃ cost final, Completes (visitPreviousRegion tm restore action) s cost final ∧
        final.config = ⟨s.config.state, BiTape.segment
          (StackTape.prepend crossed.reverse
            (StackTape.cons none (StackTape.mapSome output.reverse))) (restore :: suffix) tail⟩ ∧
        final.headPos = s.headPos ∧
        cost.steps ≤ bound + 2 * crossed.length + input.length + output.length + 6 := by
    apply Spec.completes
    vcgen [visitPreviousRegion_spec restore action input output crossed suffix tail bound
      s.config.state s.config.state s.headPos 0 ha]
    all_goals
      cases hcfg : s.config
      simp_all
  exact ⟨cost.steps, ⟨cost, final, hc, hf, hh, rfl⟩, hb⟩

end Algolean.Algorithms.SingleTapeTuringMachines
