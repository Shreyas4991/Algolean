/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Naming
public import AlgoleanTests.TMSATWriting
public meta import Algolean.Complexity.Reductions.TMSATToSAT.Naming

/-!
# Running the computation variable name writer

These checks execute the same programs on all short binary fields and all three variable kinds.
They include empty fields, zero digits, and existing output. Each run checks the whole tape,
the control state, the restored head position, and the exact number of moves. Names are tested
both as ordinary bits and with the eight-cell representation used for SAT symbols.
-/

public section

namespace AlgoleanTests.TMSATNaming

open Algolean.Algorithms Algolean.Algorithms.TMSATToSAT
open AlgoleanTests.TMSATWriting (control)
open AlgoleanTests.NPToTMSAT (tapeView)
open Cslib Cslib.Turing TMQuery

private def words : List (List Bool) :=
  [[], [false], [true], [false, false], [false, true], [true, false], [true, true]]

private def earlier : StackTape Bool :=
  StackTape.cons (some true) (StackTape.cons none (StackTape.mapSome [false, true]))

private def satBit (bit : Bool) : List Bool :=
  List.ofFn fun position : Fin 8 => position.val == if bit then 1 else 0

/--
This checks the complete tape and exact cost for every kind and every combination of fields
of at most two bits. It also changes the initial control state and checks the fixed-width
representations used inside encoded SAT formulas.
-/
def checkNames : Bool :=
  [Naming.Kind.certificate, .tape, .head].all fun kind =>
    words.all fun time => words.all fun position => words.all fun value =>
      [[], [true, false]].all fun output =>
        [none, some false, some true].all fun label =>
          [false, true].all fun encoded =>
            let code := if encoded then satBit else List.singleton
            let width := if encoded then 8 else 1
            let original := Naming.layout false true earlier time position value output
            let initial : TMState (control Bool) := { config := ⟨label, original⟩, headPos := -7 }
            let expected := Naming.layout false true earlier time position value
              (output ++ (Naming.bits kind time position value).flatMap code)
            match execute 20000 (Naming.writeName (control Bool) false true code kind) initial with
            | none => false
            | some (result, final) =>
              decide (tapeView final.machine.config.BiTape = tapeView expected ∧
                final.machine.config.state = label ∧ final.machine.headPos = -7 ∧
                result.tell.steps =
                  Naming.moves kind width time.length position.length value.length output.length)

run_cmd do
  unless checkNames do
    throwError "The name writer changed the wrong cells, head position, control state, or cost."

end AlgoleanTests.TMSATNaming
