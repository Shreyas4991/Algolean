/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Augmented
public import Algolean.Complexity.Classes.P
public import Algolean.Models.SingleTapeTM.Alphabet.Pair
public import Algolean.Models.SingleTapeTM.Alphabet.Lift
public import Algolean.Models.SingleTapeTM.Composition.MachineComposition
public import Algolean.Models.SingleTapeTM.Composition.KarpReduction

/-!
# The class NP, hardness, and completeness

* `NP` contains languages with polynomially bounded certificates checked in polynomial time.
* `NPHard` contains languages to which every language in NP has a polynomial-time Karp reduction.
* `NPComplete` contains the NP-hard languages that also belong to NP.
* `P_subset_NP` proves that every language in P belongs to NP.

The definition of `NP` gives a verifier with the separator encoding
`Alphabet.wordPair`. This file proves `P ⊆ NP` by constructing a Turing machine program that
ignores the certificate: it erases the separator and suffix, restores the head to the first input
cell, and runs the original decider with its tape symbols tagged by `Sum.inl`.

The language classes require at least two ordinary symbols. The program constructions also work
with an alphabet containing only one ordinary symbol, and the finite control remains generic.
Preparing the first word costs at most `2 * n + 4` head moves on an encoded word of length `n`.
The original polynomial is evaluated at that length, giving a polynomial bound for the complete
verifier. The program also terminates
on words with missing or repeated separators, so its polynomial-time witness covers every input
over the extended alphabet.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing Polynomial TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A language belongs to `NP` when a language in `P` checks encoded input-certificate pairs and a
polynomial in the original input length bounds the certificate length. The pair encoding uses
`Alphabet.Extended Symbol 1` and preserves the boundary with a dedicated separator, while the
original language and certificates remain over `Symbol`.
The alphabet must contain at least two distinct symbols so that a certificate can carry
information through its symbols as well as its length.

The verifier receives `(Alphabet.wordPair Symbol).encode (input, certificate)`. Its polynomial
runtime is measured in that encoded word's length, which is the two word lengths plus one.
-/
def NP [_symbols : Nontrivial Symbol] : Set (Language Symbol) :=
  {L | ∃ (A : Language (Alphabet.Extended Symbol 1)) (q : Polynomial ℕ), A ∈ P ∧
    ∀ input, input ∈ L ↔ ∃ certificate : List Symbol,
      certificate.length ≤ q.eval input.length ∧
        (Alphabet.wordPair Symbol).encode (input, certificate) ∈ A}

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
  exact Nat.add_le_add_left (mono (by lia)) _

/--
This value constructs a Turing machine program that runs `machine` on the ordinary word before
the first separator and discards the remaining input. It first erases the separator and suffix,
then runs the alphabet-lifted original program. A missing separator retains the whole word.
The bound includes preparation and uses the monotonicity proof to bound the original
computation by the encoded input length.
-/
@[simps! tm program timeBound]
def TimeComputable.onFirstWord {f : List Symbol → List Symbol} (machine : TimeComputable f)
    (mono : Monotone machine.timeBound) :
    TimeComputable (fun input : List (Alphabet.Extended Symbol 1) =>
      (f (Alphabet.firstWord input)).map Sum.inl) :=
  letI := machine.symbolDecidableEq
  letI := machine.stateDecidableEq
  {
    tm := machine.tm.extendAlphabet (markers := 1)
    program := do [TMQuery (machine.tm.extendAlphabet (markers := 1))]
      SingleTapeTuringMachines.firstWord (machine.tm.extendAlphabet (markers := 1))
      machine.program.reduceProg (alphabetReduction (markers := 1))
    timeBound n := 2 * n + 4 + machine.timeBound n
    computesWithin := by
      apply TMQuery.ComputesWithin.of_outputsWithinTime
      intro input
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

variable [Nontrivial Symbol]

/--
For a language in `P`, this theorem supplies a polynomial-time verifier language over the
extended alphabet. Its Turing machine program keeps the word before the first separator and
runs the original decider on that word. The verifier is defined on all extended-alphabet words,
including malformed pair encodings.
-/
theorem P.onFirstWord {L : Language Symbol} (h : L ∈ P) :
    Alphabet.firstWord ⁻¹' L ∈ P (Symbol := Alphabet.Extended Symbol 1) := by
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
theorem NP.ofP {L : Language Symbol} (h : L ∈ P) : L ∈ NP := by
  exact ⟨_, 0, P.onFirstWord h, by simp⟩

/-- Every language in `P` belongs to `NP`. -/
theorem P_subset_NP : (P : Set (Language Symbol)) ⊆ NP := fun _ h => NP.ofP h

/-- Every language in NP has a polynomial-time Karp reduction to a language in this set. -/
def NPHard : Set (Language Symbol) :=
  {target | ∀ source : Language Symbol, source ∈ NP → KarpReducible source target}

/-- These are the NP-hard languages that belong to NP. -/
def NPComplete : Set (Language Symbol) := NP ∩ NPHard

/-- NP-hardness means that every language in NP reduces to the given language. -/
@[simp, grind =] theorem mem_NPHard {target : Language Symbol} :
    target ∈ NPHard ↔
      ∀ source : Language Symbol, source ∈ NP → KarpReducible source target := Iff.rfl

/-- NP-completeness consists of membership in NP and NP-hardness. -/
@[simp, grind =] theorem mem_NPComplete {target : Language Symbol} :
    target ∈ NPComplete ↔ target ∈ NP ∧ target ∈ NPHard := Iff.rfl


end Algolean.Algorithms
