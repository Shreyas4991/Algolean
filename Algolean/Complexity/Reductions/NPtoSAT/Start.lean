/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Choices
public import Algolean.Complexity.Reductions.NPtoSAT.Size

import Mathlib.Logic.Equiv.List

/-!
# Preparing the input and writing the choice clauses

* `program` computes the fixed polynomial bounds, preserves the input, and writes the
  certificate, head, and tape choice clauses.
* `program_spec` states the exact resulting tape and a polynomial bound on the head moves.

The verifier, polynomials, alphabet representation, and control states are fixed when the
program is constructed. The tape initially contains only the input word.
-/


attribute [local instance 100] Fintype.toEncodable


open Cslib.Turing.SingleTapeTM Cslib.Turing.SingleTapeTM.BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.Start

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open Polynomial Alphabet Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- Each formula symbol is written using the fixed SAT representation over the tape alphabet. -/
@[expose] noncomputable def code : CodeSymbol → List Γ :=
  fun symbol => (finiteWordsOver CodeSymbol Γ).encode [symbol]

private noncomputable def bounds (states : Nat)
    (certificate time : Polynomial Nat) : List (Polynomial Nat) :=
  let width := X + certificate + 2 * time + 1
  [time + 1, width, C (states + 2), width, C (states + 2)]

open Classical in
/-- This is the encoded certificate, head, and tape choice prefix for the fixed verifier. -/
@[expose] noncomputable def choiceWord
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (input : List Γ)
    (symbols : CodeSymbol → List Γ) : List Γ :=
  Choices.word symbols
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩

omit [Inhabited Γ] [Nontrivial Γ] in
private theorem choiceWord_length_le
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ)
    (symbols : CodeSymbol → List Γ) :
    (choiceWord verifier certificate time input symbols).length ≤
      ((encoding.encode (formula verifier certificate time yes input)).flatMap symbols).length := by
  classical
  simp only [encoding_encode_eq_formulaPrefix, List.flatMap_append]
  simp only [choiceWord, Choices.word, formula, indexedFormula, CNF.rename, formulaPrefix,
    List.map_append, List.flatMap_append, List.length_append]
  lia

open Classical in
/-- This polynomial bounds preparation and all three choice writers together. -/
noncomputable def timeBound
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (tick separator : Γ) (width : Nat) : Polynomial Nat :=
  Preparation.timeBound tick separator certificate (bounds verifier.states certificate time) +
    (Choices.timeBound (Γ := Γ) width).comp (sizeBound verifier certificate time)

open Classical in
/-- This program prepares the input and writes the choices for one fixed verifier. -/
noncomputable def program (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one tick separator : Γ)
    (different equal extra : tm.State) (symbols : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  Preparation.prepare tm (Finset.univ : Finset Γ).toList tick separator certificate
    (bounds verifier.states certificate time)
  Choices.writeChoices tm zero one tick symbols different equal extra

open Classical in
/--
The program preserves the input and writes exactly the choice prefix. It finishes on the first
unary time cell, after removing the certificate count, within the stated polynomial bound.
-/
@[spec] theorem program_spec
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (hne : zero ≠ one)
    (tick separator : Γ) (hsep : tick ≠ separator)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra) (yes : Γ)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (hsmall : width ≤ 8)
    (input : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let problem : BoundedVerification Γ :=
      ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      program tm verifier certificate time zero one tick separator different equal extra code
    ⦃ fun _ cost final => final.config = ⟨some different,
        NPToSAT.Computation.ChoiceIteration.layout tick (problem.time + 1)
          (NPToSAT.Computation.width problem) (verifier.states + 2) (tick :: input)
          (tick :: choiceWord verifier certificate time input code)⟩ ∧
        final.headPos = origin + input.length + 1 + problem.certificateLength + 1 ∧
        cost.steps ≤ elapsed + (timeBound verifier certificate time tick separator width).eval
          input.length ⦄ := by
  classical
  let problem : BoundedVerification Γ :=
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
  let clock := elapsed +
    (Preparation.timeBound tick separator certificate
      (bounds verifier.states certificate time)).eval input.length
  have hsize := source_size_le_code verifier certificate time yes input code width hwidth hsmall
  have hprefix := choiceWord_length_le verifier certificate time yes input code
  have hcap : problem.certificateLength + problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
      ([] ++ Choices.word code problem).length + 64 ≤
        (sizeBound verifier certificate time).eval input.length := by
    simpa only [List.nil_append, choiceWord, problem] using (by lia :
      problem.certificateLength + problem.time + 2 * NPToSAT.Computation.width problem +
        2 * (problem.verifier.states + 2) + input.length +
        (choiceWord verifier certificate time input code).length + 64 ≤
          (sizeBound verifier certificate time).eval input.length)
  have hp := Preparation.prepare_spec (tm := tm) (Finset.univ : Finset Γ).toList
    (by simp) tick separator hsep certificate (bounds verifier.states certificate time)
    input label origin elapsed
  have hc := Choices.writeChoices_spec (tm := tm) zero one hne tick code width hwidth
    different equal extra hfirst hlast hother problem input []
    ((sizeBound verifier certificate time).eval input.length) hcap label
    (origin + input.length + 1) clock
  dsimp only
  vcgen [program, hp, hc]
  all_goals
    simp_all [bounds, problem, choiceWord, clock, timeBound, NPToSAT.Computation.width,
      Polynomial.eval_comp, Nat.add_assoc]

end Algolean.Algorithms.NPToSAT.Start
