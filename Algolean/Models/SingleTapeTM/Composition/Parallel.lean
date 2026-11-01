/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Encoding
public import Algolean.Models.SingleTapeTM.Composition.Sequential

/-!
# Single-tape product composition

Independent logical computations share one physical Boolean tape. Each supplied component
must prove that it preserves the other encoded word. Its bound includes all decoding,
shuttling, and re-encoding it performs. The resulting product runs the two programs in order;
its time is their sum on the intermediate pair, not a parallel-time maximum.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib.Turing

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- A machine transforming an encoded pair on one physical tape. -/
abbrev PairComputer (f : List Bool × List Bool → List Bool × List Bool)
    (time : List Bool × List Bool → ℕ) :=
  EncodedComputer tm (fun p => BooleanTapeEncoding.pair p.1 p.2)
    (fun p => BooleanTapeEncoding.pair p.1 p.2) f time

namespace PairComputer

/-- Product composition requires actual verified programs preserving the other component.
No assumption of disjoint physical tapes or free access to a logical word is introduced. -/
@[simps! program]
def product {f g : List Bool → List Bool} {a b : List Bool × List Bool → ℕ}
    (left : PairComputer (tm := tm) (fun p => (f p.1, p.2)) a)
    (right : PairComputer (tm := tm) (fun p => (p.1, g p.2)) b) :
    PairComputer (tm := tm) (fun p => (f p.1, g p.2))
      (fun p => a p + b (f p.1, p.2)) := EncodedComputer.seq left right

end PairComputer

end Algolean.Algorithms
