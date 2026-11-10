/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import AlgoleanTests.NPToTMSAT
public import Algolean.Complexity.Reductions.NPToTMSAT.Reduction
public meta import Algolean.Algorithms.SingleTapeTuringMachines.PolynomialWriter
public meta import Algolean.Algorithms.SingleTapeTuringMachines.SymbolEncoding

/-!
# Checking the machines used by the TMSAT serializer

The counting tests run each fixed program on all short Boolean inputs, including the empty
word and inputs too short to contribute any copies. The encoding tests use both a Boolean
alphabet with different code lengths and a three-symbol alphabet. They check the complete tape
and head position, including preservation of the suffix written before encoding the input.
-/

@[expose] public section

namespace AlgoleanTests.Serialization

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery
open Algolean.Algorithms.SingleTapeTuringMachines NPToTMSAT

/-- This machine has one control state. The query programs define its instructions. -/
abbrev control (Symbol : Type) [Inhabited Symbol] [Fintype Symbol] : SingleTapeTM Symbol where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This checks that shifting a word and changing its left neighbor preserve the other tape contents.
The words on both sides include internal blanks, so an accidental erasure is visible. Each
fixed program is tested on every Boolean word of length at most four, including the empty word.
-/
def checkTapePreservation : IO Unit := do
  let tm := control Bool
  let shift := shiftRight tm [false, true]
  let changeLeft := setLeftCell tm (some false)
  let left := StackTape.cons (some false) (StackTape.cons none (StackTape.mapSome [true]))
  let tail := StackTape.cons (some true) (StackTape.cons none (StackTape.mapSome [false]))
  let mut words := [[]]
  for _ in [:5] do
    for word in words do
      let contents := BiTape.segment (StackTape.cons none left) word tail
      let initial : TMState tm := { config := ⟨some (), contents⟩, headPos := -7 }
      let expected := BiTape.segment (StackTape.cons none left) [] (StackTape.prepend word tail)
      match execute 10000 shift initial with
      | none => throw (IO.userError "Shifting a word ran out of fuel.")
      | some (result, final) =>
        unless tapeView final.machine.config.BiTape = tapeView expected ∧
            final.machine.headPos = -7 ∧ result.tell.steps = 4 * word.length + 2 do
          throw (IO.userError "Shifting damaged another word or gave the wrong position or cost.")
      let original := BiTape.segment (StackTape.cons (some true) left) word tail
      let before : TMState tm := { config := ⟨some (), original⟩, headPos := 5 }
      let after := BiTape.segment (StackTape.cons (some false) left) word tail
      match execute 100 changeLeft before with
      | none => throw (IO.userError "Changing a neighboring cell ran out of fuel.")
      | some (result, final) =>
        unless tapeView final.machine.config.BiTape = tapeView after ∧
            final.machine.headPos = 5 ∧ result.tell.steps = 2 do
          throw (IO.userError "Changing a neighboring cell damaged another part of the tape.")
    words := words.flatMap (fun word => [false :: word, true :: word])

/--
This runs each fixed counting program on every Boolean word of length at most five. It checks
that the input is restored and exactly one copy is written for each selected set of positions.
Both empty and nonempty previous outputs are tested. Empty copied words are also checked,
as are zero selected positions and more selected positions than the input contains. Each run
also checks the proved quadratic bound on head moves.
-/
def checkCounting : IO Unit := do
  for count in [:5] do
    for block in [[], [true, false]] do
      let program := PolynomialWriter.writeChoose (control Bool) [false, true] block count
      for oldOutput in [[], [false, true]] do
        let mut words := [[]]
        for _ in [:6] do
          for input in words do
            let initial := { TMState.init (control Bool) input with
              config.BiTape := BiTape.segment StackTape.nil input (StackTape.mapSome oldOutput) }
            let copies := input.length.choose count
            let output := oldOutput ++ (List.replicate copies block).flatten
            let expected := BiTape.segment (StackTape.mapSome input.reverse) []
              (StackTape.mapSome output)
            let size := input.length + output.length + block.length + copies + 3
            let bound := (2 * count + 4) * 2 ^ count * size ^ 2
            match execute 200000 program initial with
            | none => throw (IO.userError "The counting program ran out of fuel.")
            | some (result, final) =>
              unless tapeView final.machine.config.BiTape = tapeView expected ∧
                  final.machine.headPos = (input.length : Int) ∧ result.tell.steps ≤ bound do
                throw (IO.userError "The counter gave an incorrect tape, position, or cost.")
          words := words.flatMap (fun word => [false :: word, true :: word])

/--
This checks one fixed symbol encoder against all short words over its alphabet. The encoder
starts at the input's last symbol and must preserve the word to its right while retaining the
original input order in the encoded word.
-/
def checkEncoding {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
    [Encodable Symbol] (symbols : List Symbol) (code : Symbol → List Symbol)
    (suffix : List Symbol) : IO Unit := do
  let program := encodeLeft (control Symbol) symbols code
  let mut words := [[]]
  for _ in [:5] do
    for input in words do
      let initial := { TMState.init (control Symbol) input with
        config.BiTape := (BiTape.segment (StackTape.cons none (StackTape.mapSome suffix))
          input.reverse StackTape.nil).mirror }
      let expected := (BiTape.segment (StackTape.cons none
        (StackTape.mapSome (input.flatMap code ++ suffix))) [] StackTape.nil).mirror
      match execute 200000 program initial with
      | none => throw (IO.userError "The symbol encoder ran out of fuel.")
      | some (_, final) =>
        unless tapeView final.machine.config.BiTape = tapeView expected ∧
            final.machine.headPos = -(input.length : Int) do
          throw (IO.userError "The symbol encoder gave the wrong tape or head position.")
    words := words.flatMap (fun word => symbols.map (fun symbol => symbol :: word))

run_cmd Lean.Elab.Command.liftIO do
  checkTapePreservation
  checkCounting
  checkEncoding [false, true] (fun bit => if bit then [true, false, true] else [false]) []
  checkEncoding ([0, 1, 2] : List (Fin 3)) (fun symbol => [symbol, 2, symbol]) [2, 0]

-- The complete serializer works over both alphabets without requiring an extra numeric encoding.
example (verifier : SingleTapeTM.Description (Problems.TMSAT.TapeSymbol Bool))
    (m t : Polynomial Nat) :
    Nonempty (PolyTimeComputable (fun input => Problems.TMSAT.encodingOver.encode
      (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
        Problems.TMSAT.Instance Bool))) :=
  ⟨tmsatSerializer verifier m t⟩

example {L : Algorithms.Language (Fin 3)} (h : L ∈ NP) :
    Nonempty (KarpReduction L (Problems.TMSAT.languageOver (1 : Fin 3))) :=
  NP.karpReducible_tmsat h 1

-- Quadratic bounds give a time polynomial of degree at most four.
example (verifier : SingleTapeTM.Description (Problems.TMSAT.TapeSymbol Bool)) :
    (tmsatSerializer verifier (Polynomial.X ^ 2) (Polynomial.X ^ 2)).poly.natDegree ≤ 4 := by
  have h := tmsatSerializer_natDegree_le verifier (Polynomial.X ^ 2) (Polynomial.X ^ 2)
  rw [Polynomial.natDegree_X_pow] at h
  simpa using h

-- Constant bounds still require reading and encoding inputs of arbitrary length.
example (verifier : SingleTapeTM.Description (Problems.TMSAT.TapeSymbol Bool)) :
    (tmsatSerializer verifier 0 0).poly.natDegree ≤ 2 := by
  simpa using tmsatSerializer_natDegree_le verifier 0 0

end AlgoleanTests.Serialization
