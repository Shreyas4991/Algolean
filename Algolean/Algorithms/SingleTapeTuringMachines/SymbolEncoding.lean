/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Expanding

/-!
# Replacing input symbols with fixed words

The encoder processes the input from right to left. Each symbol is replaced by its nonempty
code word, and the already written output is shifted to make room. A blank separates the
unprocessed input from that output. The output retains the original symbol order.

These are machine templates. A containing machine fixes the symbol codes and the finite list
of alphabet comparisons once. Those choices do not depend on the input or its length.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/--
This machine starts on the last input symbol and replaces symbols while moving left. A blank
must separate the last input symbol from the output already written to its right. Every
replacement word must be nonempty, and `symbols` must contain every alphabet symbol. The head
finishes one cell to the left of the blank before the completed output.

The containing machine fixes all replacement words and the list of symbols once. It includes
one fixed case for each symbol and uses tape tests to choose a case during execution. The
input and its length never change the program.
-/
def encodeLeft (tm : SingleTapeTM Symbol) (symbols : List Symbol) (code : Symbol → List Symbol) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    select symbols (fun symbol => .tapeIs (some symbol))
      (fun symbol => replaceBeforeBlank tm symbols (code symbol))

/--
Encoding preserves the symbol order and the existing output. The input is described by the list
of symbols encountered while moving left. A bound on the code lengths and final output length
bounds the number of head moves.
-/
theorem encodeLeft_correct (symbols : List Symbol) (code : Symbol → List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (hne : ∀ symbol, code symbol ≠ [])
    (W : Nat) (hW : ∀ symbol, (code symbol).length ≤ W)
    (input suffix : List Symbol) (N : Nat) (s : TMState tm)
    (hs : s.config.BiTape =
      (segment (StackTape.cons none (StackTape.mapSome suffix)) input StackTape.nil).mirror)
    (hN : (input.reverse.flatMap code ++ suffix).length ≤ N) :
    ∃ moves, Runs (encodeLeft tm symbols code) s
      (segment (StackTape.cons none (StackTape.mapSome (input.reverse.flatMap code ++ suffix)))
        [] StackTape.nil).mirror
      (s.headPos - input.length) moves ∧
      moves ≤ input.length * (W * (4 * N + 3) + W + 2) := by
  induction input generalizing suffix s with
  | nil =>
    refine ⟨0, ?_, by simp⟩
    simp [encodeLeft, hs]
  | cons symbol input ih =>
    obtain ⟨first, rest, hcode⟩ := List.exists_cons_of_ne_nil (hne symbol)
    have hbody := replaceBeforeBlank_correct symbols hcover first rest symbol input suffix s hs
    rw [← hcode] at hbody
    obtain ⟨cost, middle, hc, ht, hp, hm⟩ := hbody
    have hselect : Completes
        (select symbols (fun candidate => .tapeIs (some candidate))
          (fun candidate => replaceBeforeBlank tm symbols (code candidate))) s cost middle := by
      exact select_correct _ _ _ symbol s middle cost (hcover symbol)
        (by intro candidate; simp [hs, eq_comm]) hc
    obtain ⟨moreMoves, hrest, hbound⟩ := ih (code symbol ++ suffix) middle
      (congrArg SingleTapeTM.Cfg.BiTape ht) (by
        simpa [List.reverse_cons, List.flatMap_append, List.append_assoc] using hN)
    have hjoined := hrest.prepend hselect (by simp [ht])
    have hloop : Runs (encodeLeft tm symbols code) s
        (segment (StackTape.cons none (StackTape.mapSome
          (input.reverse.flatMap code ++ (code symbol ++ suffix)))) [] StackTape.nil).mirror
        (middle.headPos - input.length) (cost.steps + moreMoves) := by
      unfold encodeLeft
      apply runs_while_step (by simp [hs])
      simpa [encodeLeft] using hjoined
    refine ⟨cost.steps + moreMoves, ?_, ?_⟩
    · convert hloop using 1
      · simp [List.reverse_cons, List.flatMap_append, List.append_assoc]
      · simp [hp, sub_eq_add_neg, add_comm, add_left_comm]
    · have hsuffix : suffix.length ≤ N := by
        simp only [List.length_append] at hN
        lia
      have hlen := hW symbol
      have htail : rest.length ≤ W := by simp only [hcode, List.length_cons] at hlen; lia
      have hmul := Nat.mul_le_mul htail (show 4 * suffix.length + 3 ≤ 4 * N + 3 by lia)
      have hbodyBound : cost.steps ≤ W * (4 * N + 3) + W + 2 := by
        simp only [hcode, List.length_cons] at hm hlen
        lia
      have hsum := Nat.add_le_add hbodyBound hbound
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm] using hsum

end Algolean.Algorithms.SingleTapeTuringMachines
