/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Data.List.Basic

/-!
# Encoding two Boolean words without extending the alphabet

The encoding writes the first word's length as that many true bits followed by a false bit.
It then writes both words in order. The length tells the decoder where to split the words,
so either word may be empty and both may contain arbitrary Boolean values.

`pair` and `unpair` describe the encoded words and their decoding. The proofs show that decoding
recovers both words, that encoding is injective, and how appending to the second word changes
the encoding and its length.
-/

@[expose] public section

namespace Algolean.Problems.BooleanTapeEncoding

/--
`pair first second` is a pure Lean function that encodes two Boolean words as a unary header of
`first.length` true bits, a false delimiter, and the concatenation `first ++ second`. The header
records the boundary between the words without requiring a symbol outside the Boolean alphabet.
-/
def pair (first second : List Bool) : List Bool :=
  List.replicate first.length true ++ false :: (first ++ second)

/--
`readLength word` is a pure Lean function that counts the initial true bits until it reaches a false
delimiter. It returns that count and the untouched suffix after the delimiter, or `none` if the word
ends before any delimiter appears.
-/
def readLength : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
    let (n, payload) ← readLength rest
    pure (n + 1, payload)

/--
`unpair encoded` is a pure Lean function that reads the unary length header and splits the remaining
payload at that length to recover two words. It returns `none` if the delimiter is missing or if the
payload is shorter than the claimed first word.
-/
def unpair (encoded : List Bool) : Option (List Bool × List Bool) := do
  let (n, payload) ← readLength encoded
  if n ≤ payload.length then some (payload.take n, payload.drop n) else none

@[simp] theorem readLength_header (n : ℕ) (payload : List Bool) :
    readLength (List.replicate n true ++ false :: payload) = some (n, payload) := by
  induction n <;> simp_all [readLength, List.replicate_succ]

@[simp] theorem unpair_pair (first second : List Bool) :
    unpair (pair first second) = some (first, second) := by
  simp [unpair, pair]

/--
The Boolean pair encoding gives different encoded words to different pairs of input words. Decoding
a valid encoding therefore recovers both original words unambiguously.
-/
theorem pair_injective : Function.Injective (fun p : List Bool × List Bool => pair p.1 p.2) := by
  intro a b h
  have := congrArg unpair h
  rw [unpair_pair, unpair_pair] at this
  exact Option.some.inj this

/-- Two encoded pairs are equal exactly when both of their words are equal. -/
@[simp] theorem pair_eq_pair {first second first' second' : List Bool} :
    pair first second = pair first' second' ↔ first = first' ∧ second = second' := by
  constructor
  · intro h
    exact Prod.mk.inj (pair_injective h)
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem length_pair (first second : List Bool) :
    (pair first second).length = 2 * first.length + second.length + 1 := by
  simp [pair, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]

/-- Appending to the second word appends the same symbols to the end of the encoded pair. -/
theorem pair_append_right (first second suffix : List Bool) :
    pair first (second ++ suffix) = pair first second ++ suffix := by
  simp [pair, List.append_assoc]

end Algolean.Problems.BooleanTapeEncoding
