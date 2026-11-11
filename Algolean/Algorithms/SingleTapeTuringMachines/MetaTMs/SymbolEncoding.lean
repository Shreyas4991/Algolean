/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Expanding

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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

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

private theorem encodeSymbol_spec (symbols : List Symbol) (code : Symbol → List Symbol)
    (symbol : Symbol) (hmem : symbol ∈ symbols) (first : Symbol) (rest : List Symbol)
    (hcode : code symbol = first :: rest) (hcover : ∀ symbol, symbol ∈ symbols)
    (input suffix : List Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome suffix))
          (symbol :: input) StackTape.nil).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      select symbols (fun symbol => .tapeIs (some symbol))
        (fun symbol => replaceBeforeBlank tm symbols (code symbol))
    ⦃ fun _ cost final => final.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome (code symbol ++ suffix)))
          input StackTape.nil).mirror⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps =
          elapsed + rest.length * (4 * suffix.length + 3) + (code symbol).length + 2 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hsteps⟩
  vcgen [Spec.select_spec symbols (fun symbol => .tapeIs (some symbol))
    (fun symbol => replaceBeforeBlank tm symbols (code symbol)) symbol hmem]
  constructor
  · intro candidate
    simp [hcfg, eq_comm]
  · rw [hcode]
    vcgen [replaceBeforeBlank_spec symbols hcover first rest symbol input suffix
      label origin elapsed]
    all_goals simp_all

/--
Encoding preserves the symbol order and the existing output. Bounds on the code lengths and
final output length bound every iteration and therefore the whole computation.
-/
@[spec] theorem encodeLeft_spec (symbols : List Symbol) (code : Symbol → List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (hne : ∀ symbol, code symbol ≠ [])
    (W : Nat) (hW : ∀ symbol, (code symbol).length ≤ W)
    (input suffix : List Symbol) (N : Nat)
    (hN : (input.reverse.flatMap code ++ suffix).length ≤ N)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome suffix)) input StackTape.nil).mirror⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      encodeLeft tm symbols code
    ⦃ fun _ cost final => final.config = ⟨label,
        (segment (StackTape.cons none (StackTape.mapSome
          (input.reverse.flatMap code ++ suffix))) [] StackTape.nil).mirror⟩ ∧
        final.headPos = origin - input.length ∧
        cost.steps ≤ elapsed + input.length * (W * (4 * N + 3) + W + 2) ⦄ := by
  induction input generalizing suffix origin elapsed with
  | nil =>
    unfold encodeLeft
    vcgen [Spec.while_false_spec]
    simp_all
  | cons symbol input ih =>
    obtain ⟨first, rest, hcode⟩ := List.exists_cons_of_ne_nil (hne symbol)
    have hsuffix : suffix.length ≤ N := by
      simp only [List.length_append] at hN
      lia
    have hlen := hW symbol
    have htail : rest.length ≤ W := by simp only [hcode, List.length_cons] at hlen; lia
    have hmul := Nat.mul_le_mul htail (show 4 * suffix.length + 3 ≤ 4 * N + 3 by lia)
    have hbody : rest.length * (4 * suffix.length + 3) + (code symbol).length + 2 ≤
        W * (4 * N + 3) + W + 2 := by
      simp only [hcode, List.length_cons] at hlen ⊢
      lia
    have hnext : (input.reverse.flatMap code ++ (code symbol ++ suffix)).length ≤ N := by
      simpa [List.reverse_cons, List.flatMap_append, List.append_assoc] using hN
    unfold encodeLeft
    vcgen [Spec.while_step_spec (loop := encodeLeft tm symbols code) (hloop := rfl),
      encodeSymbol_spec symbols code symbol (hcover symbol) first rest hcode hcover input suffix
        label origin elapsed,
      ih (code symbol ++ suffix) hnext (origin - 1)
        (elapsed + rest.length * (4 * suffix.length + 3) + (code symbol).length + 2)]
    all_goals simp_all [List.reverse_cons, List.flatMap_append, List.append_assoc,
      sub_eq_add_neg, add_assoc, Nat.add_mul]
    all_goals lia

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
  obtain ⟨cost, final, hc, hf, hh, hb⟩ :
      ∃ cost final, Completes (encodeLeft tm symbols code) s cost final ∧
        final.config = ⟨s.config.state,
          (segment (StackTape.cons none (StackTape.mapSome
            (input.reverse.flatMap code ++ suffix))) [] StackTape.nil).mirror⟩ ∧
        final.headPos = s.headPos - input.length ∧
        cost.steps ≤ input.length * (W * (4 * N + 3) + W + 2) := by
    apply Spec.completes
    vcgen [encodeLeft_spec symbols code hcover hne W hW input suffix N hN
      s.config.state s.headPos 0]
    all_goals
      cases hcfg : s.config
      simp_all
  exact ⟨cost.steps, ⟨cost, final, hc, hf, hh, rfl⟩, hb⟩

end Algolean.Algorithms.SingleTapeTuringMachines
