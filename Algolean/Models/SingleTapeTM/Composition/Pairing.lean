/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Parallel

/-!
# Pairing outputs from a shared input

Fan-out needs a physical duplication program as well as the two framed computations.
Supplying a pure Lean pairing function is insufficient: every component below contains a
fixed query program and a proof of its tape behavior and head-move bound.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- A verified physical duplicator producing the specified Boolean encoding of two copies. -/
abbrev Duplicator (time : List Bool → ℕ)
    (headPosition : List Bool → ℤ → ℤ := fun _ origin => origin) :=
  EncodedComputer tm id (fun p => BooleanTapeEncoding.pair p.1 p.2)
    (fun input => (input, input)) time headPosition

/-- Pair two outputs by actually duplicating the input and running the verified product.
The duplication and both framed computations contribute their full costs and share history. -/
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
