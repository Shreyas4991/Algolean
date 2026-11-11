/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Variables
public import Algolean.Problems.Encodings.Pairing
public import Algolean.Problems.Encodings.SAT

/-!
# Binary names for the variables describing a computation

* `Variable.name` gives each variable a binary name. A certificate name begins with `false`,
  a tape name begins with `true, false`, and a head name begins with `true, true`.
* The remaining bits describe the position, time, symbol, or state separately. The existing
  Boolean word encoding records each field's length, so their boundaries can be recovered.
* Different variables have different names. The length theorems count the bits of each name.

The fields use binary numbers. Joining them only adds length headers and copies their bits;
it does not combine the numbers by arithmetic pairing.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Variable

open Computability Problems Problems.TMSAT

variable {Γ : Type} [Encodable Γ] {problem : Instance Γ}

/--
This names a variable by its kind and its separately encoded indices. Each length header
records the number of bits in the following field, as in `BooleanTapeEncoding.pair`.
-/
@[expose] def name : Variable problem → SAT.Variable
  | .certificate position symbol =>
    false :: BooleanTapeEncoding.pair (encodingNatBool.encode position.val)
      (encodingNatBool.encode (Encodable.encode symbol))
  | .tape time position symbol =>
    true :: false :: BooleanTapeEncoding.pair (encodingNatBool.encode time.val)
      (BooleanTapeEncoding.pair (encodingNatBool.encode position.val)
        (encodingNatBool.encode (Encodable.encode symbol)))
  | .head time (position, state) =>
    true :: true :: BooleanTapeEncoding.pair (encodingNatBool.encode time.val)
      (BooleanTapeEncoding.pair (encodingNatBool.encode position.val)
        (encodingNatBool.encode (Encodable.encode state)))

/-- Distinct certificate, tape, and head variables have distinct binary names. -/
theorem name_injective : Function.Injective (name (problem := problem)) := by
  intro first second h
  cases first <;> cases second <;>
    simp only [name, List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false,
      BooleanTapeEncoding.pair_eq_pair,
      encodingNatBool.encode_injective.eq_iff] at h <;>
    grind [Encodable.encode_injective, Fin.ext_iff]

/-- A certificate name contains its kind, position, symbol, and one length header. -/
@[simp] theorem length_name_certificate (position : Fin problem.certificateLength) (symbol : Γ) :
    (name (.certificate position symbol)).length =
      2 * position.val.size + (Encodable.encode symbol).size + 2 := by
  simp [name, BooleanTapeEncoding.length_pair]

/-- A tape name contains its kind, time, position, symbol, and two length headers. -/
@[simp] theorem length_name_tape (time : Fin (problem.time + 1))
    (position : Fin (width problem)) (symbol : Option (TapeSymbol Γ)) :
    (name (.tape time position symbol)).length =
      2 * time.val.size + 2 * position.val.size + (Encodable.encode symbol).size + 4 := by
  simp [name, BooleanTapeEncoding.length_pair]
  lia

/-- A head name contains its kind, time, position, state, and two length headers. -/
@[simp] theorem length_name_head (time : Fin (problem.time + 1))
    (position : Fin (width problem)) (state : Option (Fin (problem.verifier.states + 1))) :
    (name (.head time (position, state))).length =
      2 * time.val.size + 2 * position.val.size + (Encodable.encode state).size + 4 := by
  simp [name, BooleanTapeEncoding.length_pair]
  lia

end Algolean.Algorithms.TMSATToSAT.Variable
