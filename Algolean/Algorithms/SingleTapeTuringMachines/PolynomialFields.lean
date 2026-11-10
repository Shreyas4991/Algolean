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

/-- This polynomial bounds the field-writing time in the input length plus the old output length. -/
noncomputable def fieldsTime : List (List Symbol × Polynomial Nat) → Polynomial Nat
  | [] => 0
  | (word, p) :: rest =>
    (writePolynomialTime p).comp (X + C word.length * p + C (word.length + 1)) +
      (fieldsTime rest).comp (X + C word.length * p)

/-- Writing all fields preserves the input and has the stated polynomial bound. -/
theorem writeFields_correct (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (fields : List (List Symbol × Polynomial Nat)) (input output : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome output)) :
    ∃ moves, Runs (writeFields tm symbols fields) s
      (segment StackTape.nil input (StackTape.mapSome (output ++ fieldsWord fields input.length)))
      s.headPos moves ∧ moves ≤ (fieldsTime fields).eval (input.length + output.length) := by
  induction fields generalizing output s with
  | nil =>
    refine ⟨0, ?_, by simp [fieldsTime]⟩
    simp only [writeFields, fieldsWord, List.flatMap_nil, List.append_nil]
    refine ⟨0, s, completes_pure s, ?_, by simp, rfl⟩
    change s.config =
      {s.config with BiTape := Copying.segment StackTape.nil input (StackTape.mapSome output)}
    rw [← hs]
  | cons field fields ih =>
    obtain ⟨word, p⟩ := field
    obtain ⟨firstMoves, hf, hb⟩ := writePolynomial_correct symbols word hcover p input output s hs
    obtain ⟨cost, middle, hc, ht, hp, hm⟩ := hf
    obtain ⟨restMoves, hr, hrb⟩ :=
      ih (output ++ (List.replicate (p.eval input.length) word).flatten) middle
        (congrArg SingleTapeTM.Cfg.BiTape ht)
    have hjoined := hr.prepend hc (by simp [ht])
    refine ⟨cost.steps + restMoves, ?_, ?_⟩
    · simpa [writeFields, fieldsWord, List.append_assoc, hp] using hjoined
    · have hpmono := p.eval_mono (Nat.le_add_right input.length output.length)
      have hfirst : firstMoves ≤ ((writePolynomialTime p).comp
          (X + C word.length * p + C (word.length + 1))).eval
            (input.length + output.length) := by
        apply hb.trans
        rw [eval_comp]
        apply (writePolynomialTime p).eval_mono
        simp [List.length_flatten, Nat.mul_comm]
        have hmul := Nat.mul_le_mul_left word.length hpmono
        lia
      have hrest : restMoves ≤ ((fieldsTime fields).comp (X + C word.length * p)).eval
          (input.length + output.length) := by
        apply hrb.trans
        rw [eval_comp]
        apply (fieldsTime fields).eval_mono
        simp [List.length_flatten, Nat.mul_comm]
        have hmul := Nat.mul_le_mul_left word.length hpmono
        lia
      simpa only [fieldsTime, eval_add, hm] using Nat.add_le_add hfirst hrest

end Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter
