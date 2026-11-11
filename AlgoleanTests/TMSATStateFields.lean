/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.StateFields

/-!
# State-field boundary cases

These proofs use the public checker specification from another module. They distinguish
halting from an initial state that needs a table row, and check the smallest valid largest
state number. Each case also checks the preserved input, final head position, and time bound.
-/

public section

namespace AlgoleanTests.TMSATStateFields

open Cslib Cslib.Turing Algolean.Algorithms
open Algolean.Algorithms.SingleTapeTuringMachines Algolean.Algorithms.TMSATToSAT
open Algolean.Algorithms.Alphabet Algolean.Problems.TMSAT
open scoped TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable (label : Option (Parsing.State Bool)) (origin : ℤ) (elapsed : Nat)

/-- A next-state code of zero means halting and needs no transition-table row. -/
theorem haltWithoutRows :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode [CodeSymbol.entryEnd])⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      StateFields.check false true .next
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl .header),
          BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode [CodeSymbol.entryEnd])⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 16384 ⦄ := by
  vcgen [StateFields.check_spec false true (by decide) .next [] [] [] (by simp)
    StackTape.nil label origin elapsed]
  all_goals simp_all [StateFields.FieldInput, StateFields.CheckResult, StateFields.fieldTape,
    StateFields.Field.ending, StateFields.Field.Valid, Computability.decodeNat,
    Computability.decodeNum]

/-- An initial-state number of zero is invalid when the transition table has no rows. -/
theorem initialWithoutRows :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode [CodeSymbol.initialEnd])⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      StateFields.check false true .initial
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl .reject),
          BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode [CodeSymbol.initialEnd])⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 16384 ⦄ := by
  vcgen [StateFields.check_spec false true (by decide) .initial [] [] [] (by simp)
    StackTape.nil label origin elapsed]
  all_goals simp_all [StateFields.FieldInput, StateFields.CheckResult, StateFields.fieldTape,
    StateFields.Field.ending, StateFields.Field.Valid, Computability.decodeNat,
    Computability.decodeNum]

/-- A largest-state number of zero is accepted when the table has one row. -/
theorem largestWithOneRow :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode
          [CodeSymbol.headerEnd, CodeSymbol.rowSeparator])⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      StateFields.check false true .largest
    ⦃ fun _ cost final => final.config =
        ⟨some (.inl .header),
          BiTape.mk₁ ((finiteWordsOver CodeSymbol Bool).encode
          [CodeSymbol.headerEnd, CodeSymbol.rowSeparator])⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 36864 ⦄ := by
  vcgen [StateFields.check_spec false true (by decide) .largest [] [CodeSymbol.rowSeparator] []
    (by decide) StackTape.nil label origin elapsed]
  all_goals simp_all [StateFields.FieldInput, StateFields.CheckResult, StateFields.fieldTape,
    StateFields.Field.ending, StateFields.Field.Valid, Computability.decodeNat,
    Computability.decodeNum]

end AlgoleanTests.TMSATStateFields
