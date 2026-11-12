/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.SingleTapeTM.Encodings.Pairing
public import Algolean.Models.SingleTapeTM.Composition.Sequential

/-!
# Composing programs on two words stored together

`PairComputer` describes a program that transforms two Boolean words stored on one tape using
`Problems.BooleanTapeEncoding.pair`. `PairComputer.product` runs a program on the first word,
preserving the second, and then a program on the second word, preserving the transformed first.
Their head-move bounds add, with the second bound evaluated on the intermediate pair.

`Duplicator` describes a program that writes two copies of its input in this encoding.
`pairOutputs` composes a duplicator with the two transformations. Its bound includes all three
programs, and its final head coordinate is the one specified by the duplicator.
-/

@[expose] public section

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
  EncodedComputer tm (fun p => Problems.BooleanTapeEncoding.pair p.1 p.2)
    (fun p => Problems.BooleanTapeEncoding.pair p.1 p.2) f time

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
  EncodedComputer tm id (fun p => Problems.BooleanTapeEncoding.pair p.1 p.2)
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
    EncodedComputer tm id (fun p => Problems.BooleanTapeEncoding.pair p.1 p.2)
      (fun input => (f input, g input))
      (fun input => copyTime input + (leftTime (input, input) + rightTime (f input, input)))
      copyPosition :=
  EncodedComputer.seq copy (PairComputer.product left right)

end Algolean.Algorithms
