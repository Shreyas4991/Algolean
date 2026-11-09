/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.TMComplexity

/-!
# Executing the append and complement programs

These examples check appending and complementing Boolean words, including empty inputs and a
composition of both programs. The observations retain the complete tape, the control label, the
absolute head coordinate, and the head-move and allocation counts. A run with a shifted starting
coordinate and existing allocation history checks that the programs preserve that context.

The generic examples exercise the reusable correctness proofs and their conversion to
polynomial-time witnesses. The witnesses retain the actual executable programs.
-/

@[expose] public section

namespace AlgoleanTests.SingleTapeTuringMachines

open Algolean Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open Cslib.Turing TMQuery

open scoped TMQuery Computer

/--
This machine supplies two control labels for executing Boolean query programs. Its transition
table preserves the current symbol and halts; the query programs specify the tested operations.
-/
abbrev machine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr _ symbol := (⟨symbol, none⟩, none)

/--
This observation retains the head symbol, both complete tape stacks, the control label, the head
coordinate, and the execution's resource counts. Internal blanks and cells left of the head remain
visible, so stray symbols cannot be hidden by extracting only the nonblank output symbols.
-/
structure Observation where
  head : Option Bool
  left : List (Option Bool)
  right : List (Option Bool)
  label : Option Bool
  headPos : ℤ
  moves : ℕ
  newCells : ℕ
  totalCells : ℕ
deriving DecidableEq

/--
This function runs a Boolean Turing machine program from the supplied state with 100 units of
interpreter fuel and records its complete final tape, control label, position, and resource counts.
It returns `none` if execution exhausts the fuel.
-/
def observe (p : Prog (TMQuery machine) Unit) (initial : TMState machine) : Option Observation :=
  (execute 100 p initial).map fun (result, final) =>
    ⟨final.machine.config.BiTape.head, final.machine.config.BiTape.left.toList,
      final.machine.config.BiTape.right.toList, final.machine.config.state,
      final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
      final.machine.cellsAllocated.card⟩

example : observe (appendBit machine true) (TMState.init machine []) =
    some ⟨some true, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (appendBit machine false) (TMState.init machine []) =
    some ⟨some false, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (appendBit machine false) (TMState.init machine [true, false]) =
    some ⟨some true, [], [some false, some false], some false, 0, 6, 2, 4⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine []) =
    some ⟨none, [], [], some false, 0, 2, 1, 2⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine [false]) =
    some ⟨some true, [], [], some false, 0, 4, 2, 3⟩ := by decide +kernel

example : observe (complementBlock machine) (TMState.init machine [true, false, true]) =
    some ⟨some false, [], [some true, some false], some false, 0, 8, 2, 5⟩ := by decide +kernel

/--
This verified Turing machine program appends `true` and then negates every bit of the resulting
word. The second program runs on the tape and allocation history left by the first.
-/
def pipeline :=
  appendBitComputer (tm := machine) true ≫ₜ complementBlockComputer (tm := machine)

example : observe pipeline.program (TMState.init machine [true, false]) =
    some ⟨some false, [], [some true, some false], some false, 0, 14, 3, 5⟩ := by decide +kernel

example :
    let initial : TMState machine :=
      {TMState.init machine [true, false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 37 40
        cellsVisited := {37, 38}}
    observe (appendBit machine true) initial =
      some ⟨some true, [], [some false, some true], some true, 37, 6, 1, 5⟩ := by decide +kernel

-- The bundled proof applies to arbitrary words, starting labels, coordinates, and tape histories.
example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes pipeline.program s cost final ∧
      final.config = {s.config with BiTape := BiTape.mk₁ ((input ++ [true]).map Bool.not)} ∧
      final.headPos = s.headPos ∧
      cost.steps ≤ (2 * input.length + 2) + (2 * (input ++ [true]).length + 2) :=
  pipeline.correct input s hs

example (input : List Bool) (s : TMState machine) (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes (appendBit machine true) s cost final ∧
      cost.steps ≤ 2 * input.length + 2 ∧ cost.cellsAllocated ≤ 2 * input.length + 2 ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + (2 * input.length + 2) :=
  (appendBit_computes (tm := machine) true).space input s hs

-- Converting to a polynomial-time witness preserves the executable program definitionally.
example : (appendBitPolyTimeComputable (tm := machine) true).program =
    appendBit machine true := rfl

example : (complementBlockPolyTimeComputable (tm := machine)).program =
    complementBlock machine := rfl

end AlgoleanTests.SingleTapeTuringMachines
