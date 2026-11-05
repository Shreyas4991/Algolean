/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Augmented
public import Algolean.Models.SingleTapeTM.Alphabet.Lift
public import Algolean.Models.SingleTapeTM.Composition.MachineComposition

/-!
# Polynomial verification of encoded input-certificate pairs

The definition of `NP` in `PolytimeBasicClasses` supplies a verifier with the separator encoding
`Alphabet.wordPair`. This file proves `P ⊆ NP` by constructing a Turing machine program that
ignores the certificate: it erases the separator and suffix, restores the head to the first input
cell, and runs the original decider with its tape symbols tagged by `Sum.inl`.

The original tape alphabet and finite control remain generic. Preparing the first word costs at
most `2 * n + 4` head moves on an encoded word of length `n`. The original polynomial is evaluated
at that length, giving a polynomial bound for the complete verifier. The program also terminates
on words with missing or repeated separators, so its polynomial-time witness covers every input
over the extended alphabet.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing Polynomial TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

namespace TMQuery

private theorem firstWord_outputs {tm : SingleTapeTM Symbol} [DecidableEq Symbol]
    [DecidableEq tm.State] {p : Prog (TMQuery tm) Unit}
    {input : List (Alphabet.Extended Symbol 1)} {output : List Symbol} {time : ℕ → ℕ}
    (mono : Monotone time)
    (h : OutputsWithinTime p (Alphabet.firstWord input) output
      (time (Alphabet.firstWord input).length)) :
    OutputsWithinTime (do
      SingleTapeTuringMachines.firstWord (tm.extendAlphabet (markers := 1))
      p.reduceProg (alphabetReduction (markers := 1))) input (output.map Sum.inl)
      (2 * input.length + 4 + time input.length) := by
  apply ((SingleTapeTuringMachines.firstWord_computes
    (tm := tm.extendAlphabet (markers := 1))).outputsWithinTime_seq
      (h.extendAlphabet (markers := 1))).mono
  have hl := Alphabet.lengths_firstWord_afterMarker_le input
  exact Nat.add_le_add_left (mono (by omega)) _

/--
This value constructs a Turing machine program that runs `machine` on the ordinary word before
the first separator and discards the remaining input. It first erases the separator and suffix,
then runs the alphabet-lifted original program. A missing separator retains the whole word.
The bound includes preparation and uses the supplied monotonicity proof to bound the original
computation by the encoded input length.
-/
@[simps! tm program timeBound]
def TimeComputable.onFirstWord {f : List Symbol → List Symbol} (machine : TimeComputable f)
    (mono : Monotone machine.timeBound) :
    TimeComputable (fun input : List (Alphabet.Extended Symbol 1) =>
      (f (Alphabet.firstWord input)).map Sum.inl) := by
  letI := machine.symbolDecidableEq
  letI := machine.stateDecidableEq
  exact {
    tm := machine.tm.extendAlphabet (markers := 1)
    program := do
      SingleTapeTuringMachines.firstWord (machine.tm.extendAlphabet (markers := 1))
      machine.program.reduceProg (alphabetReduction (markers := 1))
    timeBound n := 2 * n + 4 + machine.timeBound n
    outputsFunInTime input := by
      exact firstWord_outputs mono (machine.outputsFunInTime (Alphabet.firstWord input)) }

/--
This value adds the first-word preparation program to a polynomial-time Turing machine program.
The complete program computes the original function on the prefix before the first separator,
tags its output symbols, and has polynomial bound `2 * X + 4 + machine.poly` on head moves.
-/
noncomputable def PolyTimeComputable.onFirstWord {f : List Symbol → List Symbol}
    (machine : PolyTimeComputable f) :
    PolyTimeComputable (fun input : List (Alphabet.Extended Symbol 1) =>
      (f (Alphabet.firstWord input)).map Sum.inl) where
  toTimeComputable := machine.polynomialBound.onFirstWord
    (fun _ _ h => machine.poly.eval_mono h)
  poly := 2 * X + 4 + machine.poly
  bounds _ := by simp [PolyTimeComputable.polynomialBound]

end TMQuery

/--
For a language in `P`, this theorem supplies a polynomial-time verifier language over the
extended alphabet. Its Turing machine program keeps the word before the first separator and
runs the original decider on that word. The verifier is defined on all extended-alphabet words,
including malformed pair encodings.
-/
theorem P.onFirstWord {L : Language Symbol} (h : P L) :
    P (fun input : List (Alphabet.Extended Symbol 1) => L (Alphabet.firstWord input)) := by
  obtain ⟨f, yes, ⟨machine⟩, hcorrect⟩ := h
  refine ⟨_, yes.map Sum.inl, ⟨machine.onFirstWord⟩, ?_⟩
  intro input
  constructor
  · intro h
    apply (hcorrect _).mp
    exact (List.map_inj_right (fun _ _ h => Sum.inl.inj h)).mp h
  · intro h
    exact congrArg (List.map Sum.inl) ((hcorrect _).mpr h)

/--
Every language in `P` belongs to `NP`. The verifier receives the actual separator-encoded pair,
removes the separator and certificate with the first-word program, and runs the original decider.
A certificate-length bound of zero makes the empty certificate sufficient.
-/
theorem NP.ofP {L : Language Symbol} (h : P L) : NP L := by
  exact ⟨_, 0, h.onFirstWord, by simp⟩

end Algolean.Algorithms
