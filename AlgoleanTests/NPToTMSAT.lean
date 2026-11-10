/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Instances
public meta import Algolean.Algorithms.SingleTapeTuringMachines.CertificatePadding

/-!
# Checking verifier normalization

These examples run the word-comparison and certificate-decoding programs. They check empty
certificates, certificate symbols equal to the ending symbol, missing endings, and incorrectly
placed separators. The comparison examples check that matching only a prefix does not accept.
-/

@[expose] public section

namespace AlgoleanTests.NPToTMSAT

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines

/-- This records every stored tape cell using lists with decidable equality. -/
def tapeView {Symbol : Type} [Encodable Symbol] (contents : BiTape Symbol) :
    Option Nat × List (Option Nat) × List (Option Nat) :=
  (contents.head.map Encodable.encode, contents.left.toList.map (Option.map Encodable.encode),
    contents.right.toList.map (Option.map Encodable.encode))

/-- This machine supplies one state for the certificate preprocessing program. -/
abbrev control : SingleTapeTM (Alphabet.Extended Bool 1) where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This runs the fixed decoder and reports its output tape, head coordinate, and move count. -/
def decodeRun (input : List (Alphabet.Extended Bool 1)) :
    Option ((Option Nat × List (Option Nat) × List (Option Nat)) × Int × Nat) :=
  (execute 2000 (CertificatePadding.unpad control [false, true] false true)
    (TMState.init control input)).map fun (result, final) =>
      (tapeView final.machine.config.BiTape, final.machine.headPos, result.tell.steps)

/--
These cases check ordinary and empty certificates, a data symbol equal to the ending symbol,
missing endings, incomplete entries, extra separators, and inputs with no separator.
-/
def checkDecoder : IO Unit := do
  let cases : List (List (Alphabet.Extended Bool 1) × List (Alphabet.Extended Bool 1) × Nat) := [
    ([.inl true, .inr 0, .inl false, .inl false, .inl true], [.inl true, .inr 0, .inl false], 16),
    ([.inr 0, .inl true], [.inr 0], 6),
    ([.inr 0, .inl false, .inl true, .inl true], [.inr 0, .inl true], 14),
    ([.inr 0, .inl false, .inl false], [], 12),
    ([.inr 0, .inl false], [], 6),
    ([.inr 0, .inl false, .inr 0], [], 8),
    ([.inl false, .inl true], [], 8),
    ([], [], 4)]
  for (input, expected, moves) in cases do
    unless decodeRun input = some (tapeView (BiTape.mk₁ expected), 0, moves) do
      throw (IO.userError "Certificate decoding gave the wrong tape, head position, or cost.")

/--
This checks every raw word of length at most six over the verifier's three-symbol tape alphabet.
Each run must agree with the specified decoder, return the head to zero, and meet the quadratic
move bound. The inputs include incorrectly written certificates and arbitrary extra separators.
-/
def checkAllDecoderWords : IO Unit := do
  let symbols : List (Alphabet.Extended Bool 1) := [.inl false, .inl true, .inr 0]
  let mut words : List (List (Alphabet.Extended Bool 1)) := [[]]
  for _ in [:7] do
    for word in words do
      match decodeRun word with
      | none => throw (IO.userError "Certificate decoder ran out of fuel.")
      | some (contents, position, moves) =>
        let expected := CertificatePadding.result false true word
        unless contents = tapeView (BiTape.mk₁ expected) ∧ position = 0 ∧
            moves ≤ 8 * (word.length + 2) ^ 2 do
          throw (IO.userError "Certificate decoder failed an exhaustive short-word check.")
    words := words.flatMap (fun word => symbols.map (fun symbol => symbol :: word))

run_cmd Lean.Elab.Command.liftIO do
  checkDecoder
  checkAllDecoderWords

/-- This compares with a fixed word and reports the answer tape and move count. -/
def compareRun (expected input : List Bool) :
    Option ((Option Nat × List (Option Nat) × List (Option Nat)) × Nat) :=
  let tm := comparisonControl Bool
  (execute 100 (compareWord tm true false expected) (TMState.init tm input)).map
    fun (result, final) => (tapeView final.machine.config.BiTape, result.tell.steps)

-- Equal words accept, while either kind of proper prefix rejects.
example : compareRun [true] [true] = some (tapeView (BiTape.mk₁ [true]), 1) := by
  decide +kernel
example : compareRun [true] [true, false] = some (tapeView (BiTape.mk₁ [false]), 2) := by
  decide +kernel
example : compareRun [true, false] [true] = some (tapeView (BiTape.mk₁ [false]), 1) := by
  decide +kernel
example : compareRun [] [] = some (tapeView (BiTape.mk₁ [true]), 0) := by
  decide +kernel

-- Decoding an exact-length word cannot give an oversized certificate.
example (word certificate : List Bool) (bound : Nat)
    (hdecode : Problems.CertificatePadding.decode false true word = some certificate)
    (hlen : word.length = 2 * bound + 1) : certificate.length ≤ bound :=
  Problems.CertificatePadding.length_le_bound_of_decode false true hdecode hlen

end AlgoleanTests.NPToTMSAT
