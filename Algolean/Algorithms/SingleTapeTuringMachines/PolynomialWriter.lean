/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Writing
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
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter

open Cslib Cslib.Turing TMQuery Copying Polynomial
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private def chain (parts : List (List Symbol)) (output : List Symbol) : StackTape Symbol :=
  StackTape.separateWords parts (StackTape.mapSome output)

private def span (parts : List (List Symbol)) : Nat :=
  (parts.map List.length).sum + parts.length

private def across (word : List Symbol) : Nat → Prog (TMQuery tm) Unit
  | 0 => do [TMQuery tm]
    moveₜ .Right
    appendWord tm none word
    moveₜ .Left
  | n + 1 => do [TMQuery tm]
    moveₜ .Right
    seekRightBlank tm
    across word n
    seekLeftGap tm

private theorem across_correct (word : List Symbol) (parts : List (List Symbol))
    (output : List Symbol) (left : StackTape Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment left [] (chain parts output)) :
    Runs (across (tm := tm) word parts.length) s
      (segment left [] (chain parts (output ++ word))) s.headPos
      (2 * (span parts + output.length + word.length) + 8) := by
  induction parts generalizing left s with
  | nil =>
    have hm : Runs (FreeM.lift (.move .Right)) s
        (segment (StackTape.cons none left) output StackTape.nil) (s.headPos + 1) 1 := by
      simpa [hs, chain] using move_correct s .Right
    have ha := hm.seq (q := appendWord tm none word)
      (second := segment (StackTape.cons none left) (output ++ word) StackTape.nil)
      (pos₂ := s.headPos + 1) (time₂ := 2 * (output.length + word.length) + 6) (by
        intro middle ht hp
        simpa [hp] using appendWord_correct none left output word middle
          (congrArg SingleTapeTM.Cfg.BiTape ht))
    have hf := ha.append_move .Left
    convert hf using 1
    · simp [across, bind_assoc]
    · simp only [chain, StackTape.separateWords, Copying.segment_moveLeft_gap,
        cons_none_nil, stackAppend_nil]
    · simp
    · simp only [span, List.map_nil, List.sum_nil, List.length_nil]
      lia
  | cons part parts ih =>
    have hm : Runs (FreeM.lift (.move .Right)) s
        (segment (StackTape.cons none left) part (chain parts output)) (s.headPos + 1) 1 := by
      simpa [hs, chain] using move_correct s .Right
    have hsweep := hm.seq (q := seekRightBlank tm)
      (second := segment (stackAppend part.reverse (StackTape.cons none left)) []
        (chain parts output))
      (pos₂ := s.headPos + 1 + part.length) (time₂ := part.length) (by
        intro middle ht hp
        simpa [hp] using seekRightBlank_segment (StackTape.cons none left) part
          (chain parts output) middle (congrArg SingleTapeTM.Cfg.BiTape ht))
    have hinner := hsweep.seq (q := across word parts.length)
      (second := segment (stackAppend part.reverse (StackTape.cons none left)) []
        (chain parts (output ++ word)))
      (pos₂ := s.headPos + 1 + part.length)
      (time₂ := 2 * (span parts + output.length + word.length) + 8) (by
        intro middle ht hp
        simpa [hp] using ih (stackAppend part.reverse (StackTape.cons none left)) middle
          (congrArg SingleTapeTM.Cfg.BiTape ht))
    have hf := hinner.seq (q := seekLeftGap tm)
      (second := segment left [] (chain (part :: parts) (output ++ word)))
      (pos₂ := s.headPos) (time₂ := part.length + 1) (by
        intro middle ht hp
        convert seekLeftGap_segment left part.reverse [] (chain parts (output ++ word)) middle
          (congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
          simp [chain, hp, add_comm, add_left_comm])
    convert hf using 1
    · simp [across, bind_assoc]
    · simp only [span, List.map_cons, List.sum_cons, List.length_cons]
      lia

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
    across word total
  | depth + 1 => do [TMQuery tm]
    whileₜ (notₜ tape =ₜ none) do
      select symbols (fun symbol => .tapeIs (some symbol))
        (picked (chooseProgram symbols word total depth))

private noncomputable def runtime : Nat → Polynomial Nat
  | 0 => 4 * (X + 2)
  | depth + 1 => (X + 1) * (runtime depth + X + 3)

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
  induction count <;> simp_all [copies, List.replicate_succ, Nat.add_mul, Nat.add_comm]

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

private def Correct (symbols word : List Symbol) (total depth N : Nat) : Prop :=
  ∀ (input : List Symbol) (parts : List (List Symbol)) (output : List Symbol) (s : TMState tm),
    total = parts.length + depth →
    s.config.BiTape = segment StackTape.nil input (chain parts output) →
    input.length + span parts + (output ++ copies word (input.length.choose depth)).length +
      word.length + 1 ≤ N →
    ∃ moves, Runs (chooseProgram (tm := tm) symbols word total depth) s
      (segment (StackTape.mapSome input.reverse) []
        (chain parts (output ++ copies word (input.length.choose depth))))
      (s.headPos + input.length) moves ∧ moves ≤ (runtime depth).eval N

private theorem choose_zero (symbols word : List Symbol) (total N : Nat) :
    Correct (tm := tm) symbols word total 0 N := by
  intro input parts output s htotal hs hN
  have hr := seekRightBlank_segment StackTape.nil input (chain parts output) s hs
  have hf := hr.seq (q := across word total)
    (second := segment (StackTape.mapSome input.reverse) [] (chain parts (output ++ word)))
    (pos₂ := s.headPos + input.length)
    (time₂ := 2 * (span parts + output.length + word.length) + 8) (by
      intro middle ht hp
      simpa [htotal, hp] using across_correct word parts output (StackTape.mapSome input.reverse)
        middle (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht))
  refine ⟨input.length + (2 * (span parts + output.length + word.length) + 8), ?_, ?_⟩
  · simpa [chooseProgram, copies] using hf
  · simp only [Nat.choose_zero_right, List.length_append, length_copies, Nat.one_mul] at hN
    simp only [runtime, eval_mul, eval_ofNat, eval_add, eval_X] at *
    lia

private theorem choose_loop (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (total depth N : Nat)
    (hchild : Correct (tm := tm) symbols word total depth N)
    (done remaining : List Symbol) (parts : List (List Symbol)) (output : List Symbol)
    (s : TMState tm) (htotal : total = parts.length + (depth + 1))
    (hs : s.config.BiTape = segment (StackTape.mapSome done.reverse) remaining (chain parts output))
    (hN : done.length + remaining.length + span parts +
      (output ++ copies word (sums depth done.length remaining.length)).length +
        word.length + 1 ≤ N) :
    ∃ moves, Runs (chooseProgram (tm := tm) symbols word total (depth + 1)) s
      (segment (StackTape.mapSome (done ++ remaining).reverse) []
        (chain parts (output ++ copies word (sums depth done.length remaining.length))))
      (s.headPos + remaining.length) moves ∧
      moves ≤ remaining.length * ((runtime depth).eval N + N + 3) := by
  induction remaining generalizing done output s with
  | nil =>
    refine ⟨0, ?_, by simp⟩
    simp [chooseProgram, hs, sums, copies]
  | cons symbol remaining ih =>
    have hm : Runs (FreeM.lift (.write none)) s
        (segment (StackTape.mapSome done.reverse) [] (chain (remaining :: parts) output))
        s.headPos 0 := by
      simpa [hs, chain, Copying.segment, BiTape.segment, BiTape.write] using write_correct s none
    have hstart := hm.seq (q := seekLeftEnd tm)
      (second := segment StackTape.nil done (chain (remaining :: parts) output))
      (pos₂ := s.headPos - done.length) (time₂ := done.length + 2) (by
        intro middle ht hp
        simpa [hp] using seekLeftEnd_segment StackTape.nil done.reverse []
          (chain (remaining :: parts) output) middle
          (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht))
    obtain ⟨a, start, ha, ht, hp, hsteps⟩ := hstart
    have hinnerN : done.length + span (remaining :: parts) +
        (output ++ copies word (done.length.choose depth)).length + word.length + 1 ≤ N := by
      simp only [List.length_cons, List.length_append, length_copies, sums_succ, Nat.add_mul] at hN
      dsimp only [span] at hN ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.length_append, length_copies]
      lia
    obtain ⟨innerMoves, hinner, hb⟩ := hchild done (remaining :: parts) output start
      (by simp only [List.length_cons]; lia) (congrArg SingleTapeTM.Cfg.BiTape ht) hinnerN
    let nextOutput := output ++ copies word (done.length.choose depth)
    have hrestore : Runs (do
        chooseProgram symbols word total depth
        FreeM.lift (.write (some symbol))
        FreeM.lift (.move .Right)) start
        (segment (StackTape.mapSome (done ++ [symbol]).reverse) remaining (chain parts nextOutput))
        (s.headPos + 1) (innerMoves + 1) := by
      have h := (hinner.append_write (some symbol)).append_move .Right
      simpa [chain, nextOutput, hp, List.reverse_append, List.append_assoc,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    have haction := hrestore.prepend ha (by simp [ht])
    obtain ⟨cost, middle, hc, hcfg, hpos, hcost⟩ := haction
    have hselected : Completes
        (select symbols (fun candidate => .tapeIs (some candidate))
          (picked (chooseProgram symbols word total depth))) s cost middle := by
      apply select_correct _ _ _ symbol s middle cost (hcover symbol)
      · intro candidate
        simp [hs, eq_comm]
      · simpa [picked, bind_assoc] using hc
    have hrestN : (done ++ [symbol]).length + remaining.length + span parts +
        (nextOutput ++ copies word (sums depth (done ++ [symbol]).length remaining.length)).length +
          word.length + 1 ≤ N := by
      simp only [List.length_cons, List.length_append, length_copies, sums_succ, Nat.add_mul] at hN
      simp only [nextOutput, List.length_append, List.length_cons, List.length_nil,
        length_copies]
      lia
    obtain ⟨moreMoves, hrest, hbound⟩ := ih (done ++ [symbol]) nextOutput middle
      (congrArg SingleTapeTM.Cfg.BiTape hcfg) hrestN
    have hjoined := hrest.prepend hselected (by simp [hcfg])
    have hloop : Runs (chooseProgram (tm := tm) symbols word total (depth + 1)) s
        (segment (StackTape.mapSome ((done ++ [symbol]) ++ remaining).reverse) []
          (chain parts (nextOutput ++
            copies word (sums depth (done ++ [symbol]).length remaining.length))))
        (middle.headPos + remaining.length) (cost.steps + moreMoves) := by
      unfold chooseProgram
      apply runs_while_step (by simp [hs])
      simpa only [chooseProgram, bind_assoc] using hjoined
    refine ⟨cost.steps + moreMoves, ?_, ?_⟩
    · convert hloop using 1
      · simp [List.append_assoc, sums_succ, copies_add, nextOutput]
      · simp [hpos, add_comm, add_left_comm]
    · have hcostBound : cost.steps ≤ (runtime depth).eval N + N + 3 := by
        have hdone : done.length ≤ N := by lia
        lia
      have hsum := Nat.add_le_add hcostBound hbound
      simpa only [List.length_cons, List.length_append, List.length_singleton,
        Nat.add_mul, Nat.one_mul, Nat.add_comm] using hsum

private theorem choose_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (depth : Nat) :
    ∀ total N, Correct (tm := tm) symbols word total depth N := by
  induction depth with
  | zero => exact choose_zero symbols word
  | succ depth ih =>
    intro total N input parts output s htotal hs hN
    obtain ⟨moves, hr, hb⟩ := choose_loop symbols word hcover total depth N (ih total N)
      [] input parts output s htotal (by simpa using hs) (by simpa [sums_root] using hN)
    refine ⟨moves, by simpa [sums_root] using hr, ?_⟩
    have hn : input.length ≤ N + 1 := by lia
    exact hb.trans (by simpa [runtime] using
      Nat.mul_le_mul_right ((runtime depth).eval N + N + 3) hn)

/--
This appends one copy of `word` for every choice of `count` input positions. The copies are
written beyond the blank ending the input. The input is preserved, and the head stops on that
blank. The count and alphabet comparisons are fixed independently of the input length.

This is a machine template. The containing Turing machine fixes its parameters once when
including it. The same finite program runs on every input length.
-/
def writeChoose (tm : SingleTapeTM Symbol) (symbols word : List Symbol) (count : Nat) :
    Prog (TMQuery tm) Unit := chooseProgram symbols word count count

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

private noncomputable def termsTime (terms : List Nat) : Polynomial Nat :=
  (terms.map fun k => runtime k + X + 2).sum

private theorem writeTerms_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (terms : List Nat) (input output : List Symbol)
    (N : Nat) (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output))
    (hN : input.length + (output ++ copies word (count terms input.length)).length +
      word.length + 1 ≤ N) :
    ∃ moves, Runs (writeTerms (tm := tm) symbols word terms) s
      (segment StackTape.nil input
        (StackTape.mapSome (output ++ copies word (count terms input.length))))
      s.headPos moves ∧ moves ≤ (termsTime terms).eval N := by
  induction terms generalizing output s with
  | nil =>
    refine ⟨0, ?_, by simp [termsTime]⟩
    simp only [writeTerms, count, List.map_nil, List.sum_nil, copies,
      List.replicate_zero, List.flatten_nil, List.append_nil]
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    change s.config =
      {s.config with BiTape := Copying.segment StackTape.nil input (StackTape.mapSome output)}
    rw [← hs]
  | cons k rest ih =>
    have hfirstN : input.length + span (Symbol := Symbol) [] +
        (output ++ copies word (input.length.choose k)).length + word.length + 1 ≤ N := by
      simp only [count, List.map_cons, List.sum_cons, List.length_append,
        length_copies, Nat.add_mul] at hN
      simp only [span, List.map_nil, List.sum_nil, List.length_nil, Nat.add_zero,
        List.length_append, length_copies]
      lia
    obtain ⟨firstMoves, hf, hb⟩ := choose_correct symbols word hcover k k N input [] output s
      (by simp) (by simpa [chain] using hs) hfirstN
    have hreturn := hf.seq (q := seekLeftEnd tm)
      (second := segment StackTape.nil input
        (StackTape.mapSome (output ++ copies word (input.length.choose k))))
      (pos₂ := s.headPos) (time₂ := input.length + 2) (by
        intro middle ht hp
        convert seekLeftEnd_segment StackTape.nil input.reverse []
          (StackTape.mapSome (output ++ copies word (input.length.choose k))) middle
          (by simpa [chain] using congrArg SingleTapeTM.Cfg.BiTape ht) using 1 <;>
          simp [hp])
    obtain ⟨cost, middle, hc, ht, hp, hm⟩ := hreturn
    obtain ⟨restMoves, hr, hrb⟩ := ih (output ++ copies word (input.length.choose k)) middle
      (congrArg SingleTapeTM.Cfg.BiTape ht) (by
        simpa [count, copies_add, List.append_assoc] using hN)
    have hjoined := hr.prepend hc (by simp [ht])
    refine ⟨cost.steps + restMoves, ?_, ?_⟩
    · simpa [writeTerms, writeChoose, count, copies_add, List.append_assoc, hp,
        bind_assoc] using hjoined
    · have hn : input.length ≤ N := by lia
      simp only [termsTime, List.map_cons, List.sum_cons, eval_add,
        eval_X, eval_ofNat]
      have hrest : restMoves ≤ (termsTime rest).eval N := hrb
      change cost.steps + restMoves ≤ (runtime k).eval N + N + 2 + (termsTime rest).eval N
      lia

/--
This is a machine template for appending a polynomial number of copies of a fixed word beyond
one blank after the input. It preserves the input and returns to its first cell. Another
machine fixes the polynomial, the word, and the alphabet comparisons once when including
this template. These parameters stay fixed for every input; the input length is read from the
tape and does not select a different program.
-/
noncomputable def writePolynomial (tm : SingleTapeTM Symbol) (symbols word : List Symbol)
    (p : Polynomial Nat) : Prog (TMQuery tm) Unit := writeTerms symbols word (terms p)

/-- The number of moves has a polynomial bound in the input length and the final output length. -/
noncomputable def writePolynomialTime (p : Polynomial Nat) : Polynomial Nat := termsTime (terms p)

/--
The template appends exactly `p.eval input.length` copies and restores the input and starting
head position. The bound includes the old output, the new copies, and the fixed word length.
-/
theorem writePolynomial_correct (symbols word : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (p : Polynomial Nat) (input output : List Symbol)
    (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output)) :
    ∃ moves, Runs (writePolynomial tm symbols word p) s
      (segment StackTape.nil input
        (StackTape.mapSome (output ++ (List.replicate (p.eval input.length) word).flatten)))
      s.headPos moves ∧
      moves ≤ (writePolynomialTime p).eval (input.length +
        (output ++ (List.replicate (p.eval input.length) word).flatten).length +
          word.length + 1) := by
  simpa [writePolynomial, writePolynomialTime, count_terms, copies] using
    writeTerms_correct symbols word hcover (terms p) input output
      (input.length + (output ++ copies word (p.eval input.length)).length +
        word.length + 1) s hs (by rw [count_terms])

end Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter
