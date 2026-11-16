/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Reduction.Logarithmic
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Serialization

/-!
# Single-tape alphabet reductions

An `AlphabetReduction` stores a block code and a fixed polynomial-time single-tape program
that writes it. The conversion tape uses tagged source and target symbols with one separator:
`Extended (Γ ⊕ Δ) 1`. The completed output uses only target symbols and that separator.
Source symbols are needed only while reading the original input.

`ofBlockCode` reuses the verified serializer, and `logarithmic` supplies the least payload
width when the target has at least two symbols. The program receives its input on the tape;
the code table and finite control are fixed independently of the input and its length.

This is an input representation change. It does not simulate an arbitrary source-alphabet
machine on a smaller tape alphabet. Unlike a Karp reduction it needs no decision problems or
membership equivalence: decoding recovers the original word itself.
-/

@[expose] public section

namespace Algolean.Algorithms

open Alphabet

namespace AlphabetReduction

/-- The conversion tape has tagged source and target symbols and one shared separator. -/
abbrev Tape (Γ Δ : Type) := Extended (Γ ⊕ Δ) 1

/-- The original input is placed on the conversion tape without changing its length. -/
def inputSymbol (Γ Δ : Type) : Γ ↪ Tape Γ Δ where
  toFun symbol := .inl (.inl symbol)
  inj' := by intro _ _ h; cases h; rfl

/-- The target payload and separator are included in the conversion tape. -/
def outputSymbol (Γ Δ : Type) : Extended Δ 1 ↪ Tape Γ Δ where
  toFun := Sum.map Sum.inr id
  inj' := by
    intro first second h
    cases first <;> cases second <;> simp_all

end AlphabetReduction

/-- A recoverable alphabet encoding computed by one fixed polynomial-time single-tape program. -/
structure AlphabetReduction (Γ Δ : Type) [Fintype Γ] [Fintype Δ] where
  /-- The number of target payload characters used for each source symbol. -/
  width : ℕ
  /-- Distinct source symbols receive distinct payloads. -/
  code : BlockCode Γ Δ width
  /-- The conversion is specified on every word over the shared tape alphabet. -/
  transform : List (AlphabetReduction.Tape Γ Δ) → List (AlphabetReduction.Tape Γ Δ)
  /-- One fixed single-tape program computes that conversion with a polynomial bound. -/
  computer : TMQuery.PolyTimeComputable transform
  /-- On source inputs the program produces precisely the separated target encoding. -/
  correct : ∀ input, transform (input.map (AlphabetReduction.inputSymbol Γ Δ)) =
    (code.encoding.encode input).map (AlphabetReduction.outputSymbol Γ Δ)

namespace AlphabetReduction

variable {Γ Δ : Type} [Fintype Γ] [Fintype Δ]

/-- Replace source symbols by target blocks and retain symbols already on the target tape. -/
def replacement {width : ℕ} (code : BlockCode Γ Δ width) :
    Tape Γ Δ → List (Tape Γ Δ)
  | .inl (.inl symbol) => (code.encodeSymbol symbol).map (outputSymbol Γ Δ)
  | symbol => [symbol]

omit [Fintype Γ] [Fintype Δ] in
/-- Every replacement is nonempty, as required by the serializer. -/
theorem replacement_ne_nil {width : ℕ} (code : BlockCode Γ Δ width)
    (symbol : Tape Γ Δ) : replacement code symbol ≠ [] := by
  cases symbol with
  | inl symbol =>
    cases symbol <;> simp [replacement, code.encodeSymbol_ne_nil]
  | inr marker => simp [replacement]

/-- The verified serializer computes the block replacement on every shared tape word. -/
noncomputable def blockComputer {width : ℕ} (code : BlockCode Γ Δ width) :
    TMQuery.PolyTimeComputable (fun input => input.flatMap (replacement code)) := by
  classical
  let computer := SingleTapeTuringMachines.serializerComputer (replacement code)
    (replacement_ne_nil code) [] [] []
  exact {
    tm := computer.tm
    symbolDecidableEq := computer.symbolDecidableEq
    stateDecidableEq := computer.stateDecidableEq
    program := computer.program
    timeBound := computer.timeBound
    poly := computer.poly
    bounds := computer.bounds
    computesWithin := by
      simpa [SingleTapeTuringMachines.PolynomialWriter.fieldsWord] using computer.computesWithin }

/-- The constructed program has a quadratic move bound, with a constant fixed by its code. -/
theorem blockComputer_poly {width : ℕ} (code : BlockCode Γ Δ width) :
    (blockComputer code).poly =
      Polynomial.C (SingleTapeTuringMachines.serializerTimeFactor
        (replacement code) [] [] []) * (Polynomial.X + 1) ^ 2 := by
  classical
  simp [blockComputer, SingleTapeTuringMachines.serializerComputer_poly,
    SingleTapeTuringMachines.PolynomialWriter.fieldsWork]

/-- Every fixed block code has a single-tape implementation using the verified serializer. -/
noncomputable def ofBlockCode {width : ℕ} (code : BlockCode Γ Δ width) :
    AlphabetReduction Γ Δ where
  width := width
  code := code
  transform input := input.flatMap (replacement code)
  computer := blockComputer code
  correct input := by
    induction input with
    | nil => simp [BlockCode.encode_eq_flatMap]
    | cons symbol input ih =>
      simpa [inputSymbol, replacement, BlockCode.encode_eq_flatMap] using
        congrArg ((code.encodeSymbol symbol).map (outputSymbol Γ Δ) ++ ·) ih

/-- Encode any finite source alphabet over a target alphabet with at least two symbols. -/
noncomputable def logarithmic (Γ Δ : Type) [Fintype Γ] [Fintype Δ] [Nontrivial Δ] :
    AlphabetReduction Γ Δ :=
  ofBlockCode (logarithmicCode Γ Δ)

/-- The constructed reduction uses the ceiling logarithm as its payload width. -/
@[simp] theorem width_logarithmic [Nontrivial Δ] :
    (logarithmic Γ Δ).width = payloadWidth Γ Δ := rfl

/-- Every alphabet reduction needs at least the ceiling-logarithm payload width. -/
theorem payloadWidth_le [Nontrivial Δ] (reduction : AlphabetReduction Γ Δ) :
    payloadWidth Γ Δ ≤ reduction.width :=
  (payloadWidth_le_iff Γ Δ _).mpr ⟨reduction.code⟩

/-- The output uses only the target alphabet and its one separator, with the exact block length. -/
theorem output_length (reduction : AlphabetReduction Γ Δ) (input : List Γ) :
    (reduction.transform (input.map (inputSymbol Γ Δ))).length =
      input.length * (reduction.width + 1) := by
  rw [reduction.correct, List.length_map, BlockCode.length_encode]

/-- The fixed program computes the target representation within its stored polynomial. -/
theorem outputsWithinTime (reduction : AlphabetReduction Γ Δ) (input : List Γ) :
    let := reduction.computer.symbolDecidableEq
    let := reduction.computer.stateDecidableEq
    TMQuery.OutputsWithinTime reduction.computer.program (input.map (inputSymbol Γ Δ))
      ((reduction.code.encoding.encode input).map (outputSymbol Γ Δ))
      (reduction.computer.poly.eval input.length) := by
  let := reduction.computer.symbolDecidableEq
  let := reduction.computer.stateDecidableEq
  simpa only [reduction.correct, List.length_map] using
    (reduction.computer.outputsFunInTime (input.map (inputSymbol Γ Δ))).mono
      (reduction.computer.bounds _)

end AlphabetReduction

end Algolean.Algorithms
