/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.CertificateChoices
public import AlgoleanTests.NPToTMSAT
public meta import Algolean.Complexity.Reductions.NPToTMSAT.CertificateChoices

/-!
# Running the certificate-choice clause writer

The tests compare the output with SAT's existing encoder applied to the existing exactly-one
clauses. They cover zero positions, empty choices, repeated choices, reversed counter digits,
and counter growth. Unary counts are tested with both one-cell and three-cell units.
The checks use both the SAT symbol alphabet and a Boolean tape with eight cells per SAT symbol.
Every run checks the whole tape, preserved input, control state, and restored head position.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace AlgoleanTests.NPToSATCertificateChoices

open Algolean.Algorithms Algolean.Problems Algolean.Problems.SAT
open Algolean.Algorithms.NPToTMSAT
open AlgoleanTests.NPToTMSAT (tapeView)
open Cslib Cslib.Turing TMQuery

/-- This fixed machine has two control states; its Query program chooses every action. -/
private abbrev control (Γ : Type) [Inhabited Γ] [Fintype Γ] : SingleTapeTM Γ where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

private abbrev sample (Γ : Type) (count : Nat) : BoundedVerification Γ where
  verifier := { states := 0, initial := 0, transition _ symbol := (symbol, none, none) }
  input := []
  certificateLength := count
  time := 0

private def code (symbol : CodeSymbol) : List Bool :=
  List.ofFn fun position : Fin 8 => position.val == match symbol with
    | .inl false => 0
    | .inl true => 1
    | .inr marker => marker.val + 2

private def checkRun {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
    (zero one tick : Γ) (unitTail : List Γ) (code : CodeSymbol → List Γ)
    (symbols : List Γ) (count : Nat) (input output : List Γ) : Bool :=
  let original := CertificateChoices.layoutAcross tick unitTail count [input] output
  let initial : TMState (control Γ) := { config := ⟨some true, original⟩, headPos := -23 }
  let formula := (List.finRange count).flatMap fun position =>
    CNF.exactlyOne (symbols.map fun symbol =>
      Variable.name (problem := sample Γ count) (.certificate position symbol))
  let expected := CertificateChoices.layoutAcross tick unitTail count [input]
    (output ++ (encoding.encode formula).dropLast.flatMap code)
  match execute 5000000
      (CertificateChoices.writeChoicesAcross (control Γ) zero one tick unitTail code
        symbols 1) initial with
  | none => false
  | some (_, final) =>
    decide (tapeView final.machine.config.BiTape = tapeView expected ∧
      final.machine.config.state = some true ∧ final.machine.headPos = -23)

/--
This runs fixed clause-writing programs on several unary bounds and compares their output
with SAT's encoder using `Variable.name` directly. The main cases use the SAT symbol alphabet
so larger counters can be checked quickly. A Boolean-tape case checks the eight-cell encoding.
The whole-tape comparison also checks that the position counter is erased.
-/
def checkCertificateChoices : Bool :=
  let zero : CodeSymbol := .inl false
  let one : CodeSymbol := .inl true
  let raw := ([(0, []), (0, [zero, one]), (1, []), (1, [zero]), (1, [zero, one]),
    (3, [zero, one]), (5, [zero, one]), (2, [zero, zero, one])] :
      List (Nat × List CodeSymbol)).all fun (count, symbols) =>
    [[], [one, zero]].all fun unitTail =>
      checkRun zero one one unitTail List.singleton symbols count
        [one, zero, one, zero] [zero, one]
  raw && checkRun false true false [true, false] code [false, true] 1
    [true, false, true, false] [false, true]

run_cmd do
  unless checkCertificateChoices do
    throwError "The certificate-choice writer changed the wrong cells or wrote incorrect clauses."

end AlgoleanTests.NPToSATCertificateChoices
