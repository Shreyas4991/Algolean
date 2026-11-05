/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.TMComplexity
public import Algolean.Algorithms.SingleTapeTuringMachines.Copying

/-!
# Transforming one word while preserving the other

These verified Turing machine programs operate on a pair stored in the Boolean encoding from
`Pairing`. `pairIdentityComputer` preserves the whole encoded pair. `appendRightComputer bit`
appends a bit to the second logical word while preserving the unary header and first word. It does
this by appending to the complete encoded tape and then returning to the first encoded cell, so its
bound counts a scan across the whole encoding.

The Turing machine program `duplicateAppendRightComputer bit` first physically duplicates an input
word, then preserves one copy and appends the bit to the other. Its output encodes `(input, input ++
[bit])`. The head finishes on the first output cell, which lies to the left of the original input,
and its quadratic bound includes all copying and subsequent scanning.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/--
This value contains a verified Turing machine program that leaves both logical words and their
shared encoding unchanged. It runs the identity program, preserves the head coordinate and control
state, and uses zero head moves.
-/
@[simps program]
def pairIdentityComputer : PairComputer (tm := tm) id (fun _ => 0) where
  program := identity tm
  correct input s hs :=
    (identityComputer (tm := tm)).correct (BooleanTapeEncoding.pair input.1 input.2) s hs

/--
This value contains a verified Turing machine program that appends `bit` to the second word of an
encoded pair and preserves the first word and unary header. It scans the whole encoded block to
append the bit, then returns to the original head coordinate. Its bound is twice the encoded input
length plus two head moves.
-/
@[simps program]
def appendRightComputer (bit : Bool) :
    PairComputer (tm := tm) (fun input => (input.1, input.2 ++ [bit]))
      (fun input => 2 * (BooleanTapeEncoding.pair input.1 input.2).length + 2) where
  program := appendBit tm bit
  correct input s hs := by
    simpa [appendBitComputer] using
      (appendBitComputer (tm := tm) bit).correct (BooleanTapeEncoding.pair input.1 input.2) s hs

/--
This value contains a verified Turing machine program that physically duplicates the input and then
appends `bit` only to the second copy. It produces the Boolean encoding of `(input, input ++ [bit])`
and finishes on its first cell, at `origin - (input.length + 1)`. Its bound of `4 * input.length ^ 2
+ 17 * input.length + 9` head moves includes both copying and appending.
-/
def duplicateAppendRightComputer (bit : Bool) :
    EncodedComputer tm id (fun input => BooleanTapeEncoding.pair input.1 input.2)
      (fun input => (input, input ++ [bit]))
      (fun input => 4 * input.length ^ 2 + 17 * input.length + 9)
      (fun input origin => origin - (input.length + 1 : ℕ)) :=
  EncodedComputer.mono
    (pairOutputs (Copying.duplicateComputer (tm := tm)) (pairIdentityComputer (tm := tm))
      (appendRightComputer (tm := tm) bit)) (by
        intro input
        simp only [BooleanTapeEncoding.length_pair]
        lia)

/--
This value proves polynomial-time computability of encoding the input together with a copy extended
by `bit`. It uses the composed duplication-and-append program, including its quadratic head-move
bound and its final position at the first encoded output cell.
-/
noncomputable def duplicateAppendRightPolyTimeComputable (bit : Bool) :
    TMQuery.PolyTimeComputable (fun input => BooleanTapeEncoding.pair input (input ++ [bit])) :=
  EncodedComputer.polyTimeComputable (tm := tm)
    (outputEncoding := fun p : List Bool × List Bool => BooleanTapeEncoding.pair p.1 p.2)
    (f := fun input => (input, input ++ [bit]))
    (position := fun input origin => origin - (input.length + 1 : ℕ))
    (poly := 4 * X ^ 2 + 17 * X + 9)
    (EncodedComputer.mono (duplicateAppendRightComputer (tm := tm) bit) (by intro input; simp))

end Algolean.Algorithms.SingleTapeTuringMachines
