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
This runs each fixed counting program on every Boolean word of length at most five. It checks
that the input is restored and exactly one copy is written for each selected set of positions.
The old output includes both an empty word and an occupied word. Empty copied words are also
checked, as are zero selected positions and more selected positions than the input contains.
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
            let expected := BiTape.segment (StackTape.mapSome input.reverse) []
              (StackTape.mapSome (oldOutput ++
                (List.replicate (input.length.choose count) block).flatten))
            match execute 200000 program initial with
            | none => throw (IO.userError "The counting program ran out of fuel.")
            | some (_, final) =>
              unless tapeView final.machine.config.BiTape = tapeView expected ∧
                  final.machine.headPos = (input.length : Int) do
                throw (IO.userError "The counting program gave the wrong tape or head position.")
          words := words.flatMap (fun word => [false :: word, true :: word])

/--
This checks one fixed symbol encoder against all short words over its alphabet. The encoder
starts at the input's last symbol and must preserve an existing suffix while retaining the
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

end AlgoleanTests.Serialization
