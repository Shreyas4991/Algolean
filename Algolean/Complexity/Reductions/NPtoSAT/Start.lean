/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Choices
public import Algolean.Complexity.Reductions.NPtoSAT.Size

/-!
# Preparing the input and writing the choice clauses

* `program` computes the fixed polynomial bounds, preserves the input, and writes the
  certificate, head, and tape choice clauses.
* `program_spec` states the exact resulting tape and a polynomial bound on the head moves.

The verifier, polynomials, alphabet representation, and control states are fixed when the
program is constructed. The tape initially contains only the input word.
-/

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

/-- This is the encoded certificate, head, and tape choice prefix for the fixed verifier. -/
@[expose] noncomputable def choiceWord
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (input : List Γ) : List Γ := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact Choices.word code
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩

omit [Inhabited Γ] in
private theorem choiceWord_length_le
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (input : List Γ) :
    (choiceWord verifier certificate time input).length ≤
      (encode verifier certificate time yes input).length := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  simp only [encode, encodingOver_encode_eq_formulaPrefix]
  simp only [choiceWord, Choices.word, formula, indexedFormula, CNF.rename, formulaPrefix,
    List.map_append, List.flatMap_append, List.length_append]
  unfold code
  lia

/-- This polynomial bounds preparation and all three choice writers together. -/
noncomputable def timeBound
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (tick separator : Γ) : Polynomial Nat := by
  classical
  letI : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact Preparation.timeBound tick separator certificate (bounds verifier.states certificate time) +
    (Choices.timeBound (Γ := Γ) 8).comp (sizeBound verifier certificate time)

/-- This program prepares the input and writes the choices for one fixed verifier. -/
noncomputable def program (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one tick separator : Γ)
    (different equal extra : tm.State) : Prog (TMQuery tm) Unit := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact do [TMQuery tm]
    Preparation.prepare tm (Finset.univ : Finset Γ).toList tick separator certificate
      (bounds verifier.states certificate time)
    Choices.writeChoices tm zero one tick code different equal extra

open Classical in
/--
The program preserves the input and writes exactly the choice prefix. It finishes on the first
unary time cell, after removing the certificate count, within the stated polynomial bound.
-/
@[spec] theorem program_spec
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (hne : zero ≠ one)
    (tick separator : Γ) (hsep : tick ≠ separator)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra) (yes : Γ)
    (input : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let problem : TMSAT.Instance Γ :=
      ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      program tm verifier certificate time zero one tick separator different equal extra
    ⦃ fun _ cost final => final.config = ⟨some different,
        NPToTMSAT.ChoiceIteration.layout tick (problem.time + 1)
          (NPToTMSAT.width problem) (verifier.states + 2) (tick :: input)
          (tick :: choiceWord verifier certificate time input)⟩ ∧
        final.headPos = origin + input.length + 1 + problem.certificateLength + 1 ∧
        cost.steps ≤ elapsed + (timeBound verifier certificate time tick separator).eval
          input.length ⦄ := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let problem : TMSAT.Instance Γ :=
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
  let clock := elapsed +
    (Preparation.timeBound tick separator certificate
      (bounds verifier.states certificate time)).eval input.length
  have hsize := source_size_le verifier certificate time yes input
  have hprefix := choiceWord_length_le verifier certificate time yes input
  have hcap : problem.certificateLength + problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length +
      ([] ++ Choices.word code problem).length + 64 ≤
        (sizeBound verifier certificate time).eval input.length := by
    simpa only [List.nil_append, choiceWord, problem] using (by lia :
      problem.certificateLength + problem.time + 2 * NPToTMSAT.width problem +
        2 * (problem.verifier.states + 2) + input.length +
        (choiceWord verifier certificate time input).length + 64 ≤
          (sizeBound verifier certificate time).eval input.length)
  have hwidth : ∀ symbol : CodeSymbol, (code (Γ := Γ) symbol).length = 8 := by
    intro symbol
    simp [code, CodeSymbol, Extended]
  have hp := Preparation.prepare_spec (tm := tm) (Finset.univ : Finset Γ).toList
    (by simp) tick separator hsep certificate (bounds verifier.states certificate time)
    input label origin elapsed
  have hc := Choices.writeChoices_spec (tm := tm) zero one hne tick code 8 hwidth
    different equal extra hfirst hlast hother problem input []
    ((sizeBound verifier certificate time).eval input.length) hcap label
    (origin + input.length + 1) clock
  dsimp only
  vcgen [program, hp, hc]
  all_goals
    simp_all [bounds, problem, choiceWord, clock, timeBound, NPToTMSAT.width,
      Polynomial.eval_comp, Nat.add_assoc]

end Algolean.Algorithms.NPToSAT.Start
