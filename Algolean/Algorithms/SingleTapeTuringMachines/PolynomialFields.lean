/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter

/-!
# Writing several parts whose lengths depend on the input length

Each pair `(word, p)` describes one output part. On an input of length `n`, the machine writes
`p.eval n` copies of `word`. It writes the parts in order beyond the blank after the input and
preserves the input. The list of pairs is fixed when constructing the machine and remains the
same for every input length.

The time bound is quadratic in the input length, the output length, and the number of requested
copies. Each polynomial is evaluated at the original input length throughout the proof.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter

open Cslib Cslib.Turing TMQuery Copying Polynomial
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

/-- This is the word obtained by repeating each field's word the specified number of times. -/
@[expose] def fieldsWord (fields : List (List Symbol × Polynomial Nat)) (n : Nat) : List Symbol :=
  fields.flatMap fun field => (List.replicate (field.2.eval n) field.1).flatten

/-- This polynomial counts the total number of symbols written by the fields. -/
noncomputable def fieldsSize (fields : List (List Symbol × Polynomial Nat)) : Polynomial Nat :=
  (fields.map fun field => C field.1.length * field.2).sum

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- The size polynomial gives the exact output length. -/
@[simp] theorem length_fieldsWord (fields : List (List Symbol × Polynomial Nat)) (n : Nat) :
    (fieldsWord fields n).length = (fieldsSize fields).eval n := by
  induction fields with
  | nil => simp [fieldsWord, fieldsSize]
  | cons field fields ih =>
    simp only [fieldsWord, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [fieldsSize, List.length_flatten, Nat.mul_comm]

/--
This machine template writes the specified fields beyond the blank after the input and returns
to the input's first cell. The containing machine fixes the complete field list and alphabet
comparisons once. The same finite program runs for every input length.
-/
noncomputable def writeFields (tm : SingleTapeTM Symbol) (symbols : List Symbol) :
    List (List Symbol × Polynomial Nat) → Prog (TMQuery tm) Unit
  | [] => pure ()
  | (word, p) :: rest => do [TMQuery tm]
    writePolynomial tm symbols word p
    writeFields tm symbols rest

/--
This polynomial counts the symbols written and the requested copies. A copy is counted even
when its word is empty, since the machine still performs its counting loops.
-/
@[expose] noncomputable def fieldsWork (fields : List (List Symbol × Polynomial Nat)) :
    Polynomial Nat := (fields.map fun field => C (field.1.length + 1) * field.2).sum

private def width (fields : List (List Symbol × Polynomial Nat)) : Nat :=
  (fields.map fun field => field.1.length).sum

private noncomputable def factor (fields : List (List Symbol × Polynomial Nat)) : Nat :=
  (fields.map fun field => writePolynomialFactor field.2).sum

/-- This constant depends only on the fixed words and polynomials used to write the fields. -/
noncomputable def fieldsTimeFactor (fields : List (List Symbol × Polynomial Nat)) : Nat :=
  factor fields * (width fields + 3) ^ 2

/--
This bounds the writing time when there is no previous output. It is quadratic in the input
length plus `fieldsWork`, with a constant fixed when constructing the machine.
-/
noncomputable def fieldsTime (fields : List (List Symbol × Polynomial Nat)) : Polynomial Nat :=
  C (fieldsTimeFactor fields) * (X + fieldsWork fields + 1) ^ 2

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- The output length never exceeds the count that also includes the requested copies. -/
theorem fieldsSize_le_fieldsWork (fields : List (List Symbol × Polynomial Nat)) (n : Nat) :
    (fieldsSize fields).eval n ≤ (fieldsWork fields).eval n := by
  induction fields with
  | nil => simp [fieldsSize, fieldsWork]
  | cons field fields ih =>
    simp only [fieldsSize, fieldsWork, List.map_cons, List.sum_cons, eval_add, eval_mul,
      eval_C] at ih ⊢
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by lia)) ih

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
/-- Evaluating the time bound keeps the input length separate from the amount written. -/
@[simp] theorem eval_fieldsTime (fields : List (List Symbol × Polynomial Nat)) (n : Nat) :
    (fieldsTime fields).eval n =
      fieldsTimeFactor fields * (n + (fieldsWork fields).eval n + 1) ^ 2 := by
  simp [fieldsTime]

private theorem writeFields_with_bound (symbols : List Symbol)
    (hcover : ∀ symbol, symbol ∈ symbols) (fields : List (List Symbol × Polynomial Nat))
    (input output : List Symbol) (N : Nat) (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output))
    (hN : input.length + output.length + (fieldsWork fields).eval input.length +
      width fields + 1 ≤ N) :
    ∃ moves, Runs (writeFields tm symbols fields) s
      (segment StackTape.nil input (StackTape.mapSome (output ++ fieldsWord fields input.length)))
      s.headPos moves ∧ moves ≤ factor fields * (N + 2) ^ 2 := by
  induction fields generalizing output s with
  | nil =>
    refine ⟨0, ?_, by simp [factor]⟩
    simp only [writeFields, fieldsWord, List.flatMap_nil, List.append_nil]
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    change s.config =
      {s.config with BiTape := Copying.segment StackTape.nil input (StackTape.mapSome output)}
    rw [← hs]
  | cons field fields ih =>
    obtain ⟨word, p⟩ := field
    have hwork : (fieldsWork ((word, p) :: fields)).eval input.length =
        (word.length + 1) * p.eval input.length + (fieldsWork fields).eval input.length := by
      simp [fieldsWork]
    simp only [hwork, width, List.map_cons, List.sum_cons] at hN
    change input.length + output.length +
      ((word.length + 1) * p.eval input.length + (fieldsWork fields).eval input.length) +
        (word.length + width fields) + 1 ≤ N at hN
    have hlength : (List.replicate (p.eval input.length) word).flatten.length =
        p.eval input.length * word.length := by simp [List.length_flatten]
    obtain ⟨firstMoves, hf, hb⟩ := writePolynomial_correct symbols word hcover p input output s hs
    have hfirstN : input.length +
        (output ++ (List.replicate (p.eval input.length) word).flatten).length +
          word.length + p.eval input.length + 1 ≤ N := by
      rw [List.length_append, hlength]
      rw [Nat.add_mul, Nat.one_mul] at hN
      lia
    have hfirst : firstMoves ≤ writePolynomialFactor p * (N + 2) ^ 2 := by
      simpa only [eval_writePolynomialTime] using
        hb.trans ((writePolynomialTime p).eval_mono hfirstN)
    obtain ⟨cost, middle, hc, ht, hp, hm⟩ := hf
    obtain ⟨restMoves, hr, hrb⟩ :=
      ih (output ++ (List.replicate (p.eval input.length) word).flatten) middle
        (congrArg SingleTapeTM.Cfg.BiTape ht) (by
          rw [List.length_append, hlength]
          rw [Nat.add_mul, Nat.one_mul] at hN
          lia)
    have hjoined := hr.prepend hc (by simp [ht])
    refine ⟨cost.steps + restMoves, ?_, ?_⟩
    · simpa [writeFields, fieldsWord, List.append_assoc, hp] using hjoined
    · have hsum := Nat.add_le_add hfirst hrb
      simpa only [factor, List.map_cons, List.sum_cons, Nat.add_mul, hm] using hsum

/--
Writing all fields preserves the input and has a quadratic time bound in the input length,
the previous output length, the output symbols requested, and the number of requested copies.
Every polynomial is evaluated only at the original input length.
-/
theorem writeFields_correct (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (fields : List (List Symbol × Polynomial Nat)) (input output : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output)) :
    ∃ moves, Runs (writeFields tm symbols fields) s
      (segment StackTape.nil input (StackTape.mapSome (output ++ fieldsWord fields input.length)))
      s.headPos moves ∧ moves ≤ fieldsTimeFactor fields *
        (input.length + output.length + (fieldsWork fields).eval input.length + 1) ^ 2 := by
  let A := input.length + output.length + (fieldsWork fields).eval input.length
  let N := A + width fields + 1
  obtain ⟨moves, hr, hb⟩ := writeFields_with_bound symbols hcover fields input output N s hs le_rfl
  refine ⟨moves, hr, ?_⟩
  have hwidth : 1 ≤ width fields + 3 := by lia
  have hmul := Nat.mul_le_mul_right A hwidth
  have hN : N + 2 ≤ (width fields + 3) * (A + 1) := by
    dsimp [N]
    rw [Nat.mul_add, Nat.mul_one]
    lia
  calc
    moves ≤ factor fields * (N + 2) ^ 2 := hb
    _ ≤ factor fields * ((width fields + 3) * (A + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
    _ = fieldsTimeFactor fields * (A + 1) ^ 2 := by
      simp only [fieldsTimeFactor, mul_pow, Nat.mul_assoc]

end Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter
