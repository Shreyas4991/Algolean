/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Reduction
public import Algolean.Problems.SingleTapeTM.Encodings.Basic

/-!
# Checking alphabet reductions

These examples cover the direction and rounding of the logarithm, optimality, degenerate
alphabets, concrete separated output, rejection of malformed words, and the fixed-program
execution guarantee. The language example reuses the existing encoded-language interface.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMAlphabetReduction

open Algolean.Algorithms Algolean.Algorithms.Alphabet

/-- Three distinct two-bit payloads, leaving the fourth payload unused. -/
def ternaryCode : BlockCode (Fin 3) Bool 2 where
  digits := ⟨fun symbol position => decide (symbol.val = position.val + 1), by decide⟩

example : payloadWidth (Fin 3) Bool = 2 := by decide
example : payloadWidth (Fin 4) Bool = 2 := by decide
example : payloadWidth (Fin 5) Bool = 3 := by decide
example : payloadWidth (Fin 9) (Fin 3) = 2 := by decide
example : payloadWidth Empty Bool = 0 := by decide
example : payloadWidth Unit Bool = 0 := by decide

-- Four source symbols cannot fit in one bit, but do fit in two bits.
example : ¬ Nonempty (BlockCode (Fin 4) Bool 1) := by
  rw [nonempty_blockCode_iff]
  decide

example : Nonempty (BlockCode (Fin 4) Bool 2) := by
  rw [nonempty_blockCode_iff]
  decide

-- A fixed-width unary payload cannot distinguish two source symbols at any width.
example (width : ℕ) : ¬ Nonempty (BlockCode Bool Unit width) := by
  simp [nonempty_blockCode_iff]

-- Separators are additional symbols, distinct from tape blank.
example : Fintype.card (Extended Bool 1) = 3 := by decide
example : (none : Option (Extended Bool 1)) ≠ some (BlockCode.separator Bool) := by simp

example : ternaryCode.encoding.encode [0, 2, 1] =
    [.inl false, .inl false, .inr 0,
     .inl false, .inl true, .inr 0,
     .inl true, .inl false, .inr 0] := by
  rw [BlockCode.encode_eq_flatMap]
  decide

example : ternaryCode.encoding.decode (ternaryCode.encoding.encode [2, 0, 1]) =
    some [2, 0, 1] := by simp

-- A truncated block cannot be a complete encoding.
example : ternaryCode.encoding.decode [.inl false, .inl true] = none := by
  cases h : ternaryCode.encoding.decode [.inl false, .inl true] with
  | none => rfl
  | some decoded =>
    have heq := ternaryCode.decode_eq_some_iff.mp h
    have := congrArg List.length heq
    simp at this
    omega

-- A separator in a payload position is rejected, even if the total length is correct.
example : ternaryCode.encoding.decode [.inr 0, .inl true, .inr 0] = none := by
  cases h : ternaryCode.encoding.decode [.inr 0, .inl true, .inr 0] with
  | none => rfl
  | some decoded =>
    have heq := ternaryCode.decode_eq_some_iff.mp h
    cases decoded with
    | nil => simp [BlockCode.encode_eq_flatMap] at heq
    | cons symbol rest =>
      simp [BlockCode.encode_eq_flatMap, BlockCode.encodeSymbol, ternaryCode,
        List.ofFn_succ] at heq

-- The unused payload is rejected as well.
example : ternaryCode.symbolEncoding.decode [.inl true, .inl true, .inr 0] = none := by
  cases h : ternaryCode.symbolEncoding.decode [.inl true, .inl true, .inr 0] with
  | none => rfl
  | some symbol =>
    have heq := ternaryCode.decode_symbolEncoding_eq_some_iff.mp h
    have hs : symbol = 0 ∨ symbol = 1 ∨ symbol = 2 := by omega
    rcases hs with rfl | rfl | rfl <;>
      simp [BlockCode.encodeSymbol, ternaryCode, List.ofFn_succ] at heq

-- A singleton source needs only its separator, so word lengths remain distinguishable.
example (word : List Unit) :
    ((logarithmicCode Unit Bool).encoding.encode word).length = word.length := by
  rw [BlockCode.length_encode]
  simp [payloadWidth]

example : (logarithmicCode Unit Bool).encoding.encode [(), ()] = [.inr 0, .inr 0] := by
  simp [BlockCode.encode_eq_flatMap, BlockCode.encodeSymbol, BlockCode.separator,
    logarithmicCode, payloadWidth]

example : ((logarithmicCode Empty Bool).encoding.encode []).length = 0 := by simp

-- Language membership is preserved by the same recoverable word encoding.
example (language : Algolean.Problems.Language (Fin 3)) (input : List (Fin 3)) :
    ternaryCode.encoding.encode input ∈
      Algolean.Problems.encodedLanguage language ternaryCode.encoding ↔ input ∈ language := by
  simp

-- The logarithmic constructor supplies an actual single-tape execution witness.
example (input : List (Fin 5)) :
    let reduction := AlphabetReduction.logarithmic (Fin 5) Bool
    let := reduction.computer.symbolDecidableEq
    let := reduction.computer.stateDecidableEq
    TMQuery.OutputsWithinTime reduction.computer.program
      (input.map (AlphabetReduction.inputSymbol (Fin 5) Bool))
      ((reduction.code.encoding.encode input).map
        (AlphabetReduction.outputSymbol (Fin 5) Bool))
      (reduction.computer.poly.eval input.length) :=
  (AlphabetReduction.logarithmic (Fin 5) Bool).outputsWithinTime input

example (input : List (Fin 5)) :
    ((AlphabetReduction.logarithmic (Fin 5) Bool).transform
      (input.map (AlphabetReduction.inputSymbol (Fin 5) Bool))).length = input.length * 4 := by
  rw [AlphabetReduction.output_length]
  rfl

end AlgoleanTests.SingleTapeTMAlphabetReduction
