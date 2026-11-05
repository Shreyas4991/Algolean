/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Sequential

/-!
# Encoding two Boolean words and composing their programs

This file encodes a pair of Boolean words without adding a new tape symbol. The encoding contains
one `true` for every bit of the first word, then a `false` delimiter, then the first and second
words in order. The unary header tells the decoder where the first word ends, so either word may be
empty and either may contain arbitrary Boolean values. These pure Lean encoding and decoding
functions describe tape contents; executable programs must still perform the writes and head
movements that produce them.

A `PairComputer` transforms such an encoded pair on one physical tape. `PairComputer.product` runs a
program that transforms the left word and preserves the right, followed by one that transforms the
right word and preserves the left. Their head-move costs add, with the second cost evaluated on the
intermediate pair. `pairOutputs` first runs a supplied physical duplicator and then these two
transformations, so its bound also includes the cost of copying the input.
-/

@[expose] public section

namespace Algolean.Algorithms.BooleanTapeEncoding

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
  simpa using this

@[simp] theorem length_pair (first second : List Bool) :
    (pair first second).length = 2 * first.length + second.length + 1 := by
  simp [pair]
  lia

@[simp] theorem pair_append_right (first second suffix : List Bool) :
    pair first (second ++ suffix) = pair first second ++ suffix := by
  simp [pair, List.append_assoc]

end Algolean.Algorithms.BooleanTapeEncoding

namespace Algolean.Algorithms

open Cslib.Turing

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
A `PairComputer` value stores a Turing machine program that transforms two words encoded together on
one Boolean tape, together with its correctness proof and head-move bound. It preserves the control
state and returns the head to the first cell of the encoded output.
-/
abbrev PairComputer (f : List Bool × List Bool → List Bool × List Bool)
    (time : List Bool × List Bool → ℕ) :=
  EncodedComputer tm (fun p => BooleanTapeEncoding.pair p.1 p.2)
    (fun p => BooleanTapeEncoding.pair p.1 p.2) f time

namespace PairComputer

/--
`product left right` composes two verified Turing machine programs. It first runs `left` to replace
the first logical word with `f` of that word while preserving the second. It then runs `right` to
apply `g` to the second word while preserving the transformed first word. The two programs share the
same physical tape, run sequentially, and contribute the sum of their head-move bounds.
-/
@[simps! program]
def product {f g : List Bool → List Bool} {a b : List Bool × List Bool → ℕ}
    (left : PairComputer (tm := tm) (fun p => (f p.1, p.2)) a)
    (right : PairComputer (tm := tm) (fun p => (p.1, g p.2)) b) :
    PairComputer (tm := tm) (fun p => (f p.1, g p.2))
      (fun p => a p + b (f p.1, p.2)) := EncodedComputer.seq left right

end PairComputer

/--
A `Duplicator` value contains a Turing machine program that replaces a plain input word with the
Boolean pair encoding of two identical copies, together with a proof of this behavior. Its
specification states the head-move bound and final head coordinate, which may differ from the
input's starting coordinate.
-/
abbrev Duplicator (time : List Bool → ℕ)
    (headPosition : List Bool → ℤ → ℤ := fun _ origin => origin) :=
  EncodedComputer tm id (fun p => BooleanTapeEncoding.pair p.1 p.2)
    (fun input => (input, input)) time headPosition

/--
`pairOutputs copy left right` composes three verified Turing machine programs. It runs the physical
duplicator `copy` to obtain two copies of the input on one tape. It then runs `left` on the first
logical word and `right` on the second, producing the encoding of `(f input, g input)`. The bound
adds the copying cost and both transformation costs, and the head finishes at the coordinate
specified by the duplicator.
-/
@[simps! program]
def pairOutputs {f g : List Bool → List Bool} {copyTime : List Bool → ℕ}
    {leftTime rightTime : List Bool × List Bool → ℕ}
    {copyPosition : List Bool → ℤ → ℤ}
    (copy : Duplicator (tm := tm) copyTime copyPosition)
    (left : PairComputer (tm := tm) (fun p => (f p.1, p.2)) leftTime)
    (right : PairComputer (tm := tm) (fun p => (p.1, g p.2)) rightTime) :
    EncodedComputer tm id (fun p => BooleanTapeEncoding.pair p.1 p.2)
      (fun input => (f input, g input))
      (fun input => copyTime input + (leftTime (input, input) + rightTime (f input, input)))
      copyPosition :=
  EncodedComputer.seq copy (PairComputer.product left right)

end Algolean.Algorithms
