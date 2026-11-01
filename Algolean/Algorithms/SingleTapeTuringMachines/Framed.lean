/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Complexity
public import Algolean.Algorithms.SingleTapeTuringMachines.Copying

/-!
# Verified operations on encoded pairs

Each component runs on one physical tape and proves that the other logical word is preserved.
Their bounds include the whole encoded tape. `duplicateAppendRightComputer` is an executable
fan-out example built entirely by composing verified components, including the physical copier.
-/

@[expose] public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing TMQuery Polynomial

variable {tm : SingleTapeTM Bool} [DecidableEq tm.State]

/-- Identity preserves both logical words of an encoded pair without moving the head. -/
@[simps program]
def pairIdentityComputer : PairComputer (tm := tm) id (fun _ => 0) where
  program := identity tm
  correct input s hs :=
    (identityComputer (tm := tm)).correct (BooleanTapeEncoding.pair input.1 input.2) s hs

/-- Append to the right word while preserving the encoded left word and the head origin. -/
@[simps program]
def appendRightComputer (bit : Bool) :
    PairComputer (tm := tm) (fun input => (input.1, input.2 ++ [bit]))
      (fun input => 2 * (BooleanTapeEncoding.pair input.1 input.2).length + 2) where
  program := appendBit tm bit
  correct input s hs := by
    simpa [appendBitComputer] using
      (appendBitComputer (tm := tm) bit).correct (BooleanTapeEncoding.pair input.1 input.2) s hs

/-- Fan-out into the original word and a copy with a fixed bit appended, charging all tape work. -/
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

/-- The assembled fan-out machine has a polynomial-time witness in the query complexity model. -/
noncomputable def duplicateAppendRightPolyTimeComputable (bit : Bool) :
    TMQuery.PolyTimeComputable (fun input => BooleanTapeEncoding.pair input (input ++ [bit])) :=
  EncodedComputer.polyTimeComputable (tm := tm)
    (outputEncoding := fun p : List Bool × List Bool => BooleanTapeEncoding.pair p.1 p.2)
    (f := fun input => (input, input ++ [bit]))
    (position := fun input origin => origin - (input.length + 1 : ℕ))
    (poly := 4 * X ^ 2 + 17 * X + 9)
    (by simpa using duplicateAppendRightComputer (tm := tm) bit)

end Algolean.Algorithms.SingleTapeTuringMachines
