/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Variables
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

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Computation.Variable

open Computability Problems

variable {Γ : Type} [Encodable Γ] {problem : BoundedVerification Γ}

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

end Algolean.Algorithms.NPToSAT.Computation.Variable

namespace Algolean.Algorithms.NPToSAT.Computation

open Computability Problems

variable {Γ : Type}

/-- The state list uses zero for halt, followed by the running states in increasing order. -/
@[simp] theorem stateChoices_codes (problem : BoundedVerification Γ) :
    (stateChoices problem).map Encodable.encode = List.range (problem.verifier.states + 2) := by
  let count := problem.verifier.states + 1
  have hindices : (List.finRange count).map Fin.val = List.range count := by
    ext i; simp
  calc
    _ = 0 :: (List.finRange count).map (fun state => state.val + 1) := by
      simp only [stateChoices, List.map_cons, List.map_map, Function.comp_def,
        Encodable.encode_none, Encodable.encode_some]
      rfl
    _ = 0 :: (List.range count).map Nat.succ := by
      simpa only [List.map_map, Function.comp_def, Nat.succ_eq_add_one] using
        congrArg (fun values => 0 :: values.map Nat.succ) hindices
    _ = _ := by simpa [count, Nat.add_assoc] using (@List.range_succ_eq_map count).symm

/-- The ordered controls enumerate every position and every state code, with position first. -/
theorem controlChoices_codes (problem : BoundedVerification Γ) :
    (controlChoices problem).map (fun control => (control.1.val, Encodable.encode control.2)) =
      (List.range (width problem)).flatMap fun position =>
        (List.range (problem.verifier.states + 2)).map (fun state => (position, state)) := by
  have hindices : (List.finRange (width problem)).map Fin.val = List.range (width problem) := by
    ext i; simp
  rw [← hindices]
  simp only [controlChoices, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]
  congr 1
  funext position
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map (fun state => (position.val, state))) (stateChoices_codes problem)

/-- The position and state codes distinguish all controls of the bounded computation. -/
theorem controlCode_injective (problem : BoundedVerification Γ) :
    Function.Injective
      (fun control : Fin (width problem) × Option (Fin (problem.verifier.states + 1)) =>
      (control.1.val, Encodable.encode control.2)) := by
  rintro ⟨first, firstState⟩ ⟨second, secondState⟩ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Encodable.encode_injective h.2)

end Algolean.Algorithms.NPToSAT.Computation

namespace Algolean.Algorithms.NPToSAT.Computation.Naming

open Problems

/-- These are the three kinds of variables used to describe a bounded computation. -/
inductive Kind where
  /-- This chooses one certificate symbol. -/
  | certificate
  /-- This describes one tape cell at one time. -/
  | tape
  /-- This describes the head position and state at one time. -/
  | head

/-- This gives the binary name obtained from the three words, ignoring time for certificates. -/
@[expose] def bits (kind : Kind) (time position value : List Bool) : List Bool :=
  match kind with
  | .certificate => false :: BooleanTapeEncoding.pair position value
  | .tape => true :: false ::
    BooleanTapeEncoding.pair time (BooleanTapeEncoding.pair position value)
  | .head => true :: true ::
    BooleanTapeEncoding.pair time (BooleanTapeEncoding.pair position value)

end Algolean.Algorithms.NPToSAT.Computation.Naming
