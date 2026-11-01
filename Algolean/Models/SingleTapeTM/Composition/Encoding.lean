/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component

/-!
# Boolean encodings for composition

A pair is encoded as a unary length header for the first word, a zero delimiter, then the two
words. Both empty words and all Boolean payloads are supported. These are specification
functions: a component must separately supply a query program implementing an encoding change.
-/

@[expose] public section

namespace Algolean.Algorithms.BooleanTapeEncoding

/-- Encode two words using only Boolean tape symbols, with no extra delimiter symbol. -/
def pair (first second : List Bool) : List Bool :=
  List.replicate first.length true ++ false :: (first ++ second)

/-- Parse a unary length header, returning the untouched payload. -/
def readLength : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
    let (n, payload) ← readLength rest
    pure (n + 1, payload)

/-- Decode a Boolean pair, rejecting missing delimiters and truncated first words. -/
def unpair (encoded : List Bool) : Option (List Bool × List Bool) := do
  let (n, payload) ← readLength encoded
  if n ≤ payload.length then some (payload.take n, payload.drop n) else none

@[simp] theorem readLength_header (n : ℕ) (payload : List Bool) :
    readLength (List.replicate n true ++ false :: payload) = some (n, payload) := by
  induction n <;> simp_all [readLength, List.replicate_succ]

@[simp] theorem unpair_pair (first second : List Bool) :
    unpair (pair first second) = some (first, second) := by
  simp [unpair, pair]

/-- The pair encoding is injective, so specifications cannot identify different logical inputs. -/
theorem pair_injective : Function.Injective (fun p : List Bool × List Bool => pair p.1 p.2) := by
  intro a b h
  have := congrArg unpair h
  simpa using this

@[simp] theorem length_pair (first second : List Bool) :
    (pair first second).length = 2 * first.length + second.length + 1 := by
  simp [pair]
  lia

@[simp] theorem pair_append_right (first second suffix : List Bool) :
    pair first (second ++ suffix) = pair first second ++ suffix := by
  simp [pair, List.append_assoc]

end Algolean.Algorithms.BooleanTapeEncoding
