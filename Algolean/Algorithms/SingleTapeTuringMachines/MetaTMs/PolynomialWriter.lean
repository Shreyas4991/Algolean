/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.RegionWriting
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Writing a polynomial number of copies of a fixed word

The program preserves an input word and writes its output beyond a separating blank. Each
nested loop selects a position to the left of the position selected by its caller. Every set
of `k` input positions is visited once, so a word of length `n` gives `n.choose k` copies.
A fixed combination of these loops writes any polynomial number of copies when the polynomial
has natural-number coefficients.

The selected positions are temporarily blank. Each selected symbol is restored before the loop
continues. The loop depth and the finite alphabet comparisons are fixed with the program.

The time bound is quadratic in the input length, the final output length, the copied word
length, and the number of requested copies. The coefficient depends only on the chosen
polynomial. Counting copies separately also covers an empty word, whose copies add no symbols.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter

open Cslib Cslib.Turing TMQuery Copying Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private def chain (parts : List (List Symbol)) (output : List Symbol) : StackTape Symbol :=
  StackTape.separateWords parts (StackTape.mapSome output)

private abbrev span (parts : List (List Symbol)) : Nat := regionSpan parts

private def picked (rest : Prog (TMQuery tm) Unit) (symbol : Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  seekLeftEnd tm
  rest
  tape ←ₜ some symbol
  moveₜ .Right

private def chooseProgram (symbols : List Symbol) (word : List Symbol) (total : Nat) :
    Nat → Prog (TMQuery tm) Unit
  | 0 => do [TMQuery tm]
    seekRightBlank tm
    appendAcross tm word total
  | depth + 1 => do [TMQuery tm]
    whileₜ (notₜ tape =ₜ none) do
      select symbols (fun symbol => .tapeIs (some symbol))
        (picked (chooseProgram symbols word total depth))

private def visits (depth n : Nat) : Nat :=
  ∑ k ∈ Finset.range (depth + 1), n.choose k

private def visitSums (depth start count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, visits depth (start + i)

private def runtime (depth N n : Nat) : Nat := (2 * depth + 4) * (N + 2) * visits depth n

private def chooseFactor (depth : Nat) : Nat := (2 * depth + 4) * 2 ^ depth

private theorem visits_pos (depth n : Nat) : 1 ≤ visits depth n := by
  have h := Finset.single_le_sum (fun k _ => Nat.zero_le (n.choose k))
    (show 0 ∈ Finset.range (depth + 1) by simp)
  simpa [visits] using h

private theorem visits_le (depth n : Nat) :
    visits depth n ≤ 2 ^ depth * (n.choose depth + 1) := by
  by_cases hn : depth ≤ n
  · calc
      visits depth n ≤ ∑ k ∈ Finset.range (depth + 1), n.choose depth * depth.choose k := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' : k ≤ depth := by simpa using hk
        have hpos := Nat.choose_pos (Nat.sub_le_sub_right hn k)
        have h := Nat.mul_le_mul_left (n.choose k) hpos
        simpa only [Nat.mul_one, ← Nat.choose_mul hk'] using h
      _ = n.choose depth * 2 ^ depth := by rw [← Finset.mul_sum, Nat.sum_range_choose]
      _ ≤ 2 ^ depth * (n.choose depth + 1) := by rw [Nat.mul_add]; lia
  · calc
      visits depth n ≤ ∑ k ∈ Finset.range (depth + 1), depth.choose k :=
        Finset.sum_le_sum fun k _ => Nat.choose_le_choose k (by lia)
      _ = 2 ^ depth := Nat.sum_range_choose depth
      _ ≤ 2 ^ depth * (n.choose depth + 1) := Nat.le_mul_of_pos_right _ (by lia)

private theorem visitSums_succ (depth start count : Nat) :
    visitSums depth start (count + 1) =
      visits depth start + visitSums depth (start + 1) count := by
  simp [visitSums, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm]

private theorem runtime_le_quadratic (depth N n : Nat) :
    runtime depth N n ≤ chooseFactor depth * (N + n.choose depth + 2) ^ 2 := by
  calc
    runtime depth N n ≤ (2 * depth + 4) * (N + 2) *
        (2 ^ depth * (n.choose depth + 1)) :=
      Nat.mul_le_mul_left _ (visits_le depth n)
    _ = chooseFactor depth * ((N + 2) * (n.choose depth + 1)) := by
      unfold chooseFactor
      ring
    _ ≤ chooseFactor depth * ((N + n.choose depth + 2) * (N + n.choose depth + 2)) := by
      apply Nat.mul_le_mul_left
      exact Nat.mul_le_mul (by lia) (by lia)
    _ = chooseFactor depth * (N + n.choose depth + 2) ^ 2 := by rw [pow_two]

private def copies (word : List Symbol) (count : Nat) : List Symbol :=
  (List.replicate count word).flatten

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private theorem copies_add (word : List Symbol) (a b : Nat) :
    copies word (a + b) = copies word a ++ copies word b := by
  unfold copies
  rw [← List.replicate_append_replicate, List.flatten_append]

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
@[simp] private theorem length_copies (word : List Symbol) (count : Nat) :
    (copies word count).length = count * word.length := by
  simp [copies, List.length_flatten]

private def sums (depth start count : Nat) : Nat :=
  ∑ i ∈ Finset.range count, (start + i).choose depth

private theorem sums_succ (depth start count : Nat) :
    sums depth start (count + 1) = start.choose depth + sums depth (start + 1) count := by
  simp [sums, Finset.sum_range_succ', Nat.add_comm, Nat.add_left_comm]

private theorem sums_root (depth count : Nat) : sums depth 0 count = count.choose (depth + 1) := by
  induction count with
  | zero => simp [sums]
  | succ count ih =>
    calc
      sums depth 0 (count + 1) = sums depth 0 count + count.choose depth := by
        simp [sums, Finset.sum_range_succ]
      _ = count.choose (depth + 1) + count.choose depth := by rw [ih]
      _ = (count + 1).choose (depth + 1) := by
        simp [Nat.choose_succ_succ, Nat.add_comm]

private theorem visitSums_root (depth n : Nat) :
    visitSums depth 0 n + 1 = visits (depth + 1) n := by
  have heq : visitSums depth 0 n =
      ∑ k ∈ Finset.range (depth + 1), n.choose (k + 1) := by
    unfold visitSums visits
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact sums_root k n
  rw [heq, visits, Finset.sum_range_succ' (fun k => n.choose k) (depth + 1)]
  simp only [Nat.choose_zero_right]

private def Correct (symbols word : List Symbol) (total depth N : Nat) : Prop :=
  ∀ (input : List Symbol) (parts : List (List Symbol)) (output : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat),
    total = parts.length + depth →
    input.length + span parts + (output ++ copies word (input.length.choose depth)).length +
      word.length + 1 ≤ N →
    ⦃ fun cost current => current.config =
        ⟨label, segment StackTape.nil input (chain parts output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      chooseProgram (tm := tm) symbols word total depth
    ⦃ fun _ cost final => final.config = ⟨label,
        segment (StackTape.mapSome input.reverse) []
          (chain parts (output ++ copies word (input.length.choose depth)))⟩ ∧
        final.headPos = origin + input.length ∧
        cost.steps ≤ elapsed + runtime depth N input.length ⦄

private theorem choose_zero (symbols word : List Symbol) (total N : Nat) :
    Correct (tm := tm) symbols word total 0 N := by
  intro input parts output label origin elapsed htotal hN
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  have htime : input.length + (2 * (span parts + output.length + word.length) + 8) ≤
      runtime 0 N input.length := by
    simp only [Nat.choose_zero_right, List.length_append, length_copies, Nat.one_mul] at hN
    simp [runtime, visits]
    lia
  unfold chooseProgram
  rw [htotal, Nat.add_zero]
  vcgen [seekRightBlank_segment_spec StackTape.nil (chain parts output) input
      label origin initial.steps,
    appendAcross_spec word parts output (StackTape.mapSome input.reverse)
      label (origin + input.length) (initial.steps + input.length)]
  all_goals simp_all [copies, chain, regionSpan]
  all_goals lia

private theorem choose_iteration_spec (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (total depth N : Nat)
    (hchild : Correct (tm := tm) symbols word total depth N)
    (done : List Symbol) (symbol : Symbol) (remaining : List Symbol)
    (parts : List (List Symbol)) (output : List Symbol)
    (htotal : total = parts.length + (depth + 1))
    (hN : done.length + (remaining.length + 1) + span parts +
      (output ++ copies word (sums depth done.length (remaining.length + 1))).length +
        word.length + 1 ≤ N)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        segment (StackTape.mapSome done.reverse) (symbol :: remaining) (chain parts output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      select symbols (fun candidate => .tapeIs (some candidate))
        (picked (chooseProgram (tm := tm) symbols word total depth))
    ⦃ fun _ cost final => final.config = ⟨label,
        segment (StackTape.mapSome (done ++ [symbol]).reverse) remaining
          (chain parts (output ++ copies word (done.length.choose depth)))⟩ ∧
        final.headPos = origin + 1 ∧ cost.steps ≤ elapsed +
          (2 * depth + 6) * (N + 2) * visits depth done.length ⦄ := by
  have hinnerN : done.length + span (remaining :: parts) +
      (output ++ copies word (done.length.choose depth)).length + word.length + 1 ≤ N := by
    simp only [List.length_append, length_copies, sums_succ, Nat.add_mul] at hN
    dsimp only [span, regionSpan] at hN ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_append, length_copies]
    lia
  have htotal' : total = (remaining :: parts).length + depth := by
    simp only [List.length_cons]
    lia
  have hdone : done.length ≤ N := by lia
  have hunit : done.length + 3 ≤ 2 * (N + 2) := by lia
  have hcharged := Nat.mul_le_mul_left (2 * (N + 2)) (visits_pos depth done.length)
  have htime : runtime depth N done.length + done.length + 3 ≤
      (2 * depth + 6) * (N + 2) * visits depth done.length := by
    calc
      _ ≤ runtime depth N done.length + 2 * (N + 2) * visits depth done.length := by lia
      _ = _ := by unfold runtime; ring
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  vcgen [Spec.select_spec symbols (fun candidate => .tapeIs (some candidate))
    (picked (chooseProgram (tm := tm) symbols word total depth)) symbol (hcover symbol)]
  constructor
  · intro candidate
    simp [hcfg, eq_comm]
  · vcgen [picked,
      seekLeftEnd_segment_spec StackTape.nil (chain (remaining :: parts) output) done.reverse []
        label origin initial.steps,
      hchild done (remaining :: parts) output label (origin - done.length)
        (initial.steps + done.length + 2) htotal' hinnerN]
    all_goals cases remaining
    all_goals simp_all [TMState.write, TMState.move, TMState.moveCost, chain,
      BiTape.segment, BiTape.write, BiTape.moveRight, List.reverse_append]
    all_goals lia

private theorem choose_loop (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (total depth N : Nat)
    (hchild : Correct (tm := tm) symbols word total depth N)
    (done remaining : List Symbol) (parts : List (List Symbol)) (output : List Symbol)
    (htotal : total = parts.length + (depth + 1))
    (hN : done.length + remaining.length + span parts +
      (output ++ copies word (sums depth done.length remaining.length)).length +
        word.length + 1 ≤ N)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment (StackTape.mapSome done.reverse) remaining (chain parts output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      chooseProgram (tm := tm) symbols word total (depth + 1)
    ⦃ fun _ cost final => final.config = ⟨label,
        segment (StackTape.mapSome (done ++ remaining).reverse) []
          (chain parts (output ++ copies word (sums depth done.length remaining.length)))⟩ ∧
        final.headPos = origin + remaining.length ∧ cost.steps ≤ elapsed +
          (2 * depth + 6) * (N + 2) * visitSums depth done.length remaining.length ⦄ := by
  induction remaining generalizing done output origin elapsed with
  | nil =>
    unfold chooseProgram
    vcgen [Spec.while_false_spec]
    simp_all [sums, copies, visitSums]
  | cons symbol remaining ih =>
    let nextOutput := output ++ copies word (done.length.choose depth)
    have hrestN : (done ++ [symbol]).length + remaining.length + span parts +
        (nextOutput ++ copies word (sums depth (done ++ [symbol]).length remaining.length)).length +
          word.length + 1 ≤ N := by
      simp only [List.length_cons, List.length_append, length_copies, sums_succ, Nat.add_mul] at hN
      simp only [nextOutput, List.length_append, List.length_cons, List.length_nil, length_copies]
      lia
    unfold chooseProgram
    vcgen [Spec.while_step_spec
        (loop := chooseProgram (tm := tm) symbols word total (depth + 1)) (hloop := rfl),
      choose_iteration_spec symbols word hcover total depth N hchild done symbol remaining parts
        output htotal (by simpa using hN) label origin elapsed,
      ih (done ++ [symbol]) nextOutput hrestN (origin + 1)
        (elapsed + (2 * depth + 6) * (N + 2) * visits depth done.length)]
    all_goals simp_all [nextOutput, List.append_assoc, sums_succ, copies_add,
      visitSums_succ, Nat.mul_add]
    all_goals lia

private theorem choose_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (depth : Nat) :
    ∀ total N, Correct (tm := tm) symbols word total depth N := by
  induction depth with
  | zero => exact choose_zero symbols word
  | succ depth ih =>
    intro total N input parts output label origin elapsed htotal hN
    have hsum : visitSums depth 0 input.length ≤ visits (depth + 1) input.length := by
      have := visitSums_root depth input.length
      lia
    have htime : (2 * depth + 6) * (N + 2) * visitSums depth 0 input.length ≤
        runtime (depth + 1) N input.length := by
      simpa [runtime, Nat.mul_add, Nat.add_assoc] using
        Nat.mul_le_mul_left ((2 * depth + 6) * (N + 2)) hsum
    vcgen [choose_loop symbols word hcover total depth N (ih total N) [] input parts output
      htotal (by simpa [sums_root] using hN) label origin elapsed]
    all_goals simp_all [sums_root]
    all_goals lia

/--
This appends one copy of `word` for every choice of `count` input positions. The copies are
written beyond the blank ending the input. The input is preserved, and the head stops on that
blank. The count and alphabet comparisons are fixed independently of the input length.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def writeChoose (tm : SingleTapeTM Symbol) (symbols word : List Symbol) (count : Nat) :
    Prog (TMQuery tm) Unit := chooseProgram symbols word count count

/-- This polynomial bounds the head moves when writing one copy for each set of input positions. -/
noncomputable def writeChooseTime (count : Nat) : Polynomial Nat :=
  C (chooseFactor count) * (X + 2) ^ 2

/-- Writing the chosen copies preserves the input and records the polynomial time bound. -/
@[spec] theorem writeChoose_spec (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (count : Nat) (input output : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment StackTape.nil input (StackTape.mapSome output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeChoose tm symbols word count
    ⦃ fun _ cost final => final.config = ⟨label,
        segment (StackTape.mapSome input.reverse) [] (StackTape.mapSome
          (output ++ (List.replicate (input.length.choose count) word).flatten))⟩ ∧
        final.headPos = origin + input.length ∧ cost.steps ≤ elapsed +
          (writeChooseTime count).eval (input.length +
            (output ++ (List.replicate (input.length.choose count) word).flatten).length +
              word.length + input.length.choose count + 1) ⦄ := by
  let N := input.length + (output ++ copies word (input.length.choose count)).length +
    word.length + 1
  have htime := runtime_le_quadratic count N input.length
  vcgen [writeChoose, choose_correct symbols word hcover count count N input [] output
    label origin elapsed (by simp) (by simp [N, span, regionSpan])]
  all_goals simp_all [writeChooseTime, N, chain, copies,
    add_assoc, add_comm, add_left_comm]
  all_goals lia

/--
The machine writes exactly one copy for every set of `count` input positions. It preserves the
input and the old output, and stops on the blank after the input. The time bound uses the input
length, the final output length, the copied word length, and the number of copies requested.
-/
theorem writeChoose_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (count : Nat) (input output : List Symbol)
    (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output)) :
    let result := output ++ (List.replicate (input.length.choose count) word).flatten
    ∃ moves, Runs (writeChoose tm symbols word count) s
      (segment (StackTape.mapSome input.reverse) [] (StackTape.mapSome result))
      (s.headPos + input.length) moves ∧
      moves ≤ (writeChooseTime count).eval
        (input.length + result.length + word.length + input.length.choose count + 1) := by
  apply Spec.runs_le
  vcgen [writeChoose_spec symbols word hcover count input output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

private noncomputable def terms (p : Polynomial Nat) : List Nat :=
  p.support.toList.flatMap fun degree =>
    (List.range (degree + 1)).flatMap fun k =>
      List.replicate (p.coeff degree * Nat.stirlingSecond degree k * k.factorial) k

private def count (terms : List Nat) (n : Nat) : Nat :=
  (terms.map (fun k => n.choose k)).sum

private theorem sum_flatMap_nat {α : Type} (xs : List α) (f : α → List Nat) :
    (xs.flatMap f).sum = (xs.map fun x => (f x).sum).sum := by
  induction xs <;> simp_all

private theorem sum_range_eq (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

private theorem count_terms (p : Polynomial Nat) (n : Nat) : count (terms p) n = p.eval n := by
  classical
  simp only [count, terms, List.map_flatMap, sum_flatMap_nat, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  rw [Finset.sum_map_toList, eval_eq_sum, Polynomial.sum]
  apply Finset.sum_congr rfl
  intro degree hdegree
  rw [sum_range_eq]
  simp only [Nat.mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.descFactorial_eq_factorial_mul_choose]

private def writeTerms (symbols word : List Symbol) : List Nat → Prog (TMQuery tm) Unit
  | [] => pure ()
  | k :: rest => do [TMQuery tm]
    writeChoose tm symbols word k
    seekLeftEnd tm
    writeTerms symbols word rest

private def termsFactor (terms : List Nat) : Nat :=
  (terms.map fun k => chooseFactor k + 1).sum

private noncomputable def termsTime (terms : List Nat) : Polynomial Nat :=
  C (termsFactor terms) * (X + 2) ^ 2

private theorem writeTerms_spec (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (terms : List Nat) (input output : List Symbol)
    (N : Nat) (hN : input.length + (output ++ copies word (count terms input.length)).length +
      word.length + count terms input.length + 1 ≤ N)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment StackTape.nil input (StackTape.mapSome output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeTerms (tm := tm) symbols word terms
    ⦃ fun _ cost final => final.config = ⟨label, segment StackTape.nil input
        (StackTape.mapSome (output ++ copies word (count terms input.length)))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (termsTime terms).eval N ⦄ := by
  induction terms generalizing output elapsed with
  | nil =>
    vcgen [writeTerms]
    simp_all [count, copies, termsTime, termsFactor]
  | cons k rest ih =>
    have hfirstN : input.length +
        (output ++ copies word (input.length.choose k)).length + word.length +
          input.length.choose k + 1 ≤ N := by
      simp only [count, List.map_cons, List.sum_cons, List.length_append,
        length_copies, Nat.add_mul] at hN
      simp only [List.length_append, length_copies]
      lia
    have hfirst := (writeChooseTime k).eval_mono hfirstN
    have hrestN : input.length +
        ((output ++ copies word (input.length.choose k)) ++
          copies word (count rest input.length)).length +
            word.length + count rest input.length + 1 ≤ N := by
      simp only [count, List.map_cons, List.sum_cons, List.length_append,
        length_copies, Nat.add_mul] at hN ⊢
      lia
    have hn : input.length ≤ N := by lia
    have hlinear : input.length + 2 ≤ (N + 2) ^ 2 := by
      have h := Nat.le_mul_of_pos_right (N + 2) (show 0 < N + 2 by lia)
      rw [pow_two]
      lia
    unfold writeTerms
    apply Std.WP.Triple.bind (mid := fun _ cost current => current.config = ⟨label,
      segment (StackTape.mapSome input.reverse) []
        (StackTape.mapSome (output ++ copies word (input.length.choose k)))⟩ ∧
      current.headPos = origin + input.length ∧ cost.steps ≤ elapsed + (writeChooseTime k).eval N)
    · vcgen [writeChoose_spec symbols word hcover k input output label origin elapsed]
      all_goals simp_all [copies]
      all_goals lia
    · intro _
      apply Std.WP.Triple.intro
      rintro initial current ⟨hcfg, hpos, hsteps⟩
      vcgen [seekLeftEnd_segment_spec StackTape.nil
          (StackTape.mapSome (output ++ copies word (input.length.choose k))) input.reverse []
          label (origin + input.length) initial.steps,
        ih (output ++ copies word (input.length.choose k)) hrestN
          (initial.steps + input.length + 2)]
      all_goals simp_all [count, copies_add, List.append_assoc, termsTime,
        writeChooseTime, termsFactor, Nat.add_mul]
      all_goals lia

/--
This is a machine template for appending a polynomial number of copies of a fixed word beyond
one blank after the input. It preserves the input and returns to its first cell. Another
machine fixes the polynomial, the word, and the alphabet comparisons once when including
this template. These parameters stay fixed for every input; the input length is read from the
tape and does not select a different program.
-/
noncomputable def writePolynomial (tm : SingleTapeTM Symbol) (symbols word : List Symbol)
    (p : Polynomial Nat) : Prog (TMQuery tm) Unit := writeTerms symbols word (terms p)

/-- This constant depends only on the fixed polynomial and counts the costs of its loops. -/
noncomputable def writePolynomialFactor (p : Polynomial Nat) : Nat := termsFactor (terms p)

/-- This quadratic polynomial bounds the writing time in the stated input and output size. -/
noncomputable def writePolynomialTime (p : Polynomial Nat) : Polynomial Nat :=
  C (writePolynomialFactor p) * (X + 2) ^ 2

/-- The writing-time polynomial is quadratic, with a constant fixed by the chosen polynomial. -/
@[simp] theorem eval_writePolynomialTime (p : Polynomial Nat) (n : Nat) :
    (writePolynomialTime p).eval n = writePolynomialFactor p * (n + 2) ^ 2 := by
  simp [writePolynomialTime]

/-- Writing the polynomial number of copies preserves the input and restores the head. -/
@[spec] theorem writePolynomial_spec (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (p : Polynomial Nat) (input output : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment StackTape.nil input (StackTape.mapSome output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writePolynomial tm symbols word p
    ⦃ fun _ cost final => final.config = ⟨label, segment StackTape.nil input
        (StackTape.mapSome (output ++ (List.replicate (p.eval input.length) word).flatten))⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + (writePolynomialTime p).eval
          (input.length + (output ++ (List.replicate (p.eval input.length) word).flatten).length +
            word.length + p.eval input.length + 1) ⦄ := by
  simpa [writePolynomial, writePolynomialTime, writePolynomialFactor, termsTime,
    count_terms, copies] using
    writeTerms_spec symbols word hcover (terms p) input output
      (input.length + (output ++ copies word (p.eval input.length)).length +
        word.length + p.eval input.length + 1) (by rw [count_terms]) label origin elapsed

/--
The template appends exactly `p.eval input.length` copies and restores the input and starting
head position. The bound counts the old output, the new output, the fixed word length, and
the requested copies. Counting copies also covers an empty word, whose copies add no symbols.
-/
theorem writePolynomial_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (p : Polynomial Nat) (input output : List Symbol)
    (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output)) :
    let result := output ++ (List.replicate (p.eval input.length) word).flatten
    ∃ moves, Runs (writePolynomial tm symbols word p) s
      (segment StackTape.nil input (StackTape.mapSome result)) s.headPos moves ∧
      moves ≤ (writePolynomialTime p).eval
        (input.length + result.length + word.length + p.eval input.length + 1) := by
  apply Spec.runs_le
  vcgen [writePolynomial_spec symbols word hcover p input output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter
