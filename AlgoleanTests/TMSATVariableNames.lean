/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.VariableNames

/-!
# Checking the boundaries in computation variable names

These examples check that a name distinguishes its kind, time, position, symbol, and state.
They include two certificate variables whose fields would have identical concatenations
without the length header. Decoding the encoded pair recovers the separate fields.
-/

public section

namespace AlgoleanTests.TMSATVariableNames

open Algolean.Problems Algolean.Problems.TMSAT Algolean.Algorithms.TMSATToSAT Computability

/-- This instance has four certificate symbols, two times, and a verifier with two states. -/
private abbrev exampleInstance : Instance (Fin 4) where
  verifier := {
    states := 1
    initial := 0
    transition _ symbol := (symbol, none, none) }
  input := []
  certificateLength := 4
  time := 1

/-- The words for one followed by three and three followed by one have the same bare bits. -/
theorem swapped_fields_same_bits : encodingNatBool.encode 1 ++ encodingNatBool.encode 3 =
    encodingNatBool.encode 3 ++ encodingNatBool.encode 1 := by
  decide +kernel

/-- The length header distinguishes those same numbers when they form a variable name. -/
example : Variable.name (problem := exampleInstance) (.certificate 1 3) ≠
    Variable.name (problem := exampleInstance) (.certificate 3 1) := by
  decide +kernel

/-- Removing the kind bit and decoding the pair recovers the position and alphabet symbol. -/
example : ((BooleanTapeEncoding.unpair
    (Variable.name (problem := exampleInstance) (.certificate 1 3)).tail).map
      fun fields => (decodeNat fields.1, decodeNat fields.2)) = some (1, 3) := by
  decide +kernel

/-- Exchanging the time and position changes a tape variable's name. -/
example : Variable.name (problem := exampleInstance) (.tape 0 ⟨1, by decide⟩ none) ≠
    Variable.name (problem := exampleInstance) (.tape 1 ⟨0, by decide⟩ none) := by
  decide +kernel

/-- A blank cell and an ordinary symbol receive different names at the same time and position. -/
example : Variable.name (problem := exampleInstance) (.tape 0 ⟨0, by decide⟩ none) ≠
    Variable.name (problem := exampleInstance) (.tape 0 ⟨0, by decide⟩ (some (.inl 0))) := by
  decide +kernel

/-- The halted state and active state zero receive different names. -/
example : Variable.name (problem := exampleInstance) (.head 0 (⟨0, by decide⟩, none)) ≠
    Variable.name (problem := exampleInstance) (.head 0 (⟨0, by decide⟩, some 0)) := by
  decide +kernel

/-- The two active states receive different names at the same time and position. -/
example : Variable.name (problem := exampleInstance) (.head 0 (⟨0, by decide⟩, some 0)) ≠
    Variable.name (problem := exampleInstance) (.head 0 (⟨0, by decide⟩, some 1)) := by
  decide +kernel

/-- Certificate, tape, and head variables remain distinct when their numeric fields are zero. -/
example :
    let certificate := Variable.name (problem := exampleInstance) (.certificate 0 0)
    let tape := Variable.name (problem := exampleInstance) (.tape 0 ⟨0, by decide⟩ none)
    let head := Variable.name (problem := exampleInstance) (.head 0 (⟨0, by decide⟩, none))
    certificate ≠ tape ∧ certificate ≠ head ∧ tape ≠ head := by
  decide +kernel

end AlgoleanTests.TMSATVariableNames
