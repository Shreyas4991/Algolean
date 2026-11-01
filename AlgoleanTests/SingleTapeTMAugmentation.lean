/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.NP
public import Algolean.Algorithms.SingleTapeTuringMachines.Complexity

/-! # Generic alphabet lifting and polynomial verification of encoded pairs -/

@[expose] public section

namespace AlgoleanTests.SingleTapeTMAugmentation

open Algolean Algolean.Algorithms Cslib Cslib.Turing TMQuery SingleTapeTuringMachines
open scoped TMQuery

/-- Original finite control, also used by the lifted machine. -/
abbrev machine : SingleTapeTM Bool where
  State := Fin 2
  q₀ := 0
  tr q symbol := (⟨symbol, some .right⟩, some q)

example (cfg : machine.Cfg) :
    machine.augment.step ⟨cfg.state, cfg.BiTape.augment⟩ =
      (machine.step cfg).map (fun t => ⟨t.state, t.BiTape.augment⟩) :=
  SingleTapeTM.step_augment machine cfg

-- A separator is an ordinary symbol, distinct from the tape's blank.
example : (some (Augmented.separator : Augmented Bool) : Option (Augmented Bool)) ≠ none := by
  simp

example : Augmented.encodePair [false] [true] ≠ Augmented.encodePair [false, true] [] := by
  decide

-- The same API works over a singleton alphabet; two Boolean marker values are not required.
example (input certificate : List Unit) :
    Augmented.firstWord (Augmented.encodePair input certificate) = input := by simp

/-- Observe output and costs after running the fixed first-word preparation program. -/
def observeFirstWord (input : List (Augmented Bool)) :
    Option (List (Augmented Bool) × ℤ × ℕ × ℕ) :=
  (execute 1000 (firstWord machine.augment) (TMState.init machine.augment input)).map
    fun (result, final) =>
      (final.machine.config.BiTape.head.toList ++
        final.machine.config.BiTape.right.toList.filterMap id,
        final.machine.headPos, result.tell.steps, final.machine.spaceUsed)

example : observeFirstWord (Augmented.encodePair [true, false] [false]) =
    some ([.symbol true, .symbol false], 0, 10, 6) := by decide

example : observeFirstWord [] = some ([], 0, 4, 3) := by decide

example : observeFirstWord (Augmented.encodePair [] []) = some ([], 0, 4, 3) := by decide

example : observeFirstWord [.symbol true, .symbol false] =
    some ([.symbol true, .symbol false], 0, 8, 5) := by decide

example : observeFirstWord [.symbol true, .separator, .separator, .symbol false] =
    some ([.symbol true], 0, 10, 6) := by decide

/-- Lift a verified component without rewriting its program or correctness proof. -/
def liftedAppend := (appendBitComputer (tm := machine) true).augment

example :
    (execute 100 liftedAppend.program
      (TMState.init machine.augment [.symbol false])).map
      (fun (result, final) =>
        (final.machine.config.BiTape.head.toList ++
          final.machine.config.BiTape.right.toList.filterMap id,
          result.tell.steps, final.machine.spaceUsed)) =
      some ([.symbol false, .symbol true], 4, 3) := by decide +kernel

example {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    (L : Algorithms.Language Symbol) (h : P L) : NP L := NP.ofP h

-- A verifier for a P language is built through the actual generic machine adapter.
example (yes : List Bool) :
    P (fun word : List (Augmented Bool) => Augmented.firstWord word = yes) := by
  apply P.onFirstWord (L := fun input : List Bool => input = yes)
  exact ⟨id, yes, ⟨TMQuery.PolyTimeComputable.id⟩, by simp⟩

end AlgoleanTests.SingleTapeTMAugmentation
