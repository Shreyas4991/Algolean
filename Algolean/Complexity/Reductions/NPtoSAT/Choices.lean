/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Preparation
public import Algolean.Complexity.Reductions.NPToTMSAT.CertificateChoices
public import Algolean.Complexity.Reductions.NPToTMSAT.HeadChoices
public import Algolean.Complexity.Reductions.NPToTMSAT.TapeChoices

/-!
# Writing the certificate, head, and tape choices

The program writes the clauses choosing one symbol at each certificate position, one head
position and state at each time, and one symbol in every recorded tape cell. It reads all
bounds from the prepared unary words and preserves the original input and earlier output.
It removes the certificate bound after writing its clauses and returns to the first time cell.

This is a machine template. The containing machine fixes its alphabet representations and
control states once. The instance describing the clauses occurs only in its specification.
-/

public section

namespace Algolean.Algorithms.NPToSAT.Choices

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open NPToTMSAT Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This encodes the existing certificate, head, and tape choices without ending the formula. -/
@[expose] noncomputable def word (code : CodeSymbol → List Γ) (problem : TMSAT.Instance Γ) :
    List Γ := (formulaPrefix ((choiceClauses problem).rename Variable.name)).flatMap code

omit [Inhabited Γ] in
private theorem word_eq_parts (code : CodeSymbol → List Γ) (problem : TMSAT.Instance Γ) :
    word code problem =
      (formulaPrefix ((certificateClauses problem).rename Variable.name)).flatMap code ++
      (formulaPrefix ((headClauses problem).rename Variable.name)).flatMap code ++
      (formulaPrefix ((tapeClauses problem).rename Variable.name)).flatMap code := by
  simp [word, choiceClauses, CNF.rename, formulaPrefix, List.flatMap_append, List.map_append,
    List.append_assoc]

private def eraseCertificate (tm : SingleTapeTM Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  eraseRight tm
  moveₜ .Right

omit [Encodable Γ] in
private theorem eraseCertificate_spec (tick : Γ) (certificate times positions states : Nat)
    (input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        Preparation.layout tick certificate [times, positions, states, positions, states]
          input output⟩ ∧ current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      eraseCertificate tm
    ⦃ fun _ cost final => final.config = ⟨label,
        ChoiceIteration.layout tick times positions states (tick :: input) (tick :: output)⟩ ∧
        final.headPos = origin + certificate + 1 ∧ cost.steps ≤ elapsed + certificate + 1 ⦄ := by
  apply Std.WP.Triple.intro
  rintro initial current ⟨hcfg, hpos, hcost⟩
  vcgen [eraseCertificate, eraseRight_spec (tm := tm) (List.replicate certificate tick)
    (StackTape.separateWords [List.replicate times tick, List.replicate positions tick,
      List.replicate states tick, List.replicate positions tick, List.replicate states tick,
      tick :: input] (StackTape.mapSome (tick :: output))) label origin initial.steps]
  all_goals
    simp_all [Preparation.layout, ChoiceIteration.layout, TMState.move, TMState.moveCost]

/-- This polynomial includes all three choice writers and removal of the certificate bound. -/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  CertificateChoices.timeBound width 1 (Finset.univ : Finset Γ).toList +
    HeadChoices.timeBound width +
    TapeChoices.timeBound width (Finset.univ : Finset (Option (TMSAT.TapeSymbol Γ))).toList + X + 1

/--
This fixed template writes all choice clauses and removes the certificate bound. It preserves
both copies of the position and state bounds, the time bound, and the original input.
-/
noncomputable def writeChoices (tm : SingleTapeTM Γ) [DecidableEq tm.State] (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (different equal extra : tm.State) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  CertificateChoices.writeCertificateChoicesAcross tm zero one tick [] code 6
  eraseCertificate tm
  HeadChoices.writeHeadChoices tm zero one tick code different equal extra
  TapeChoices.writeTapeChoices tm zero one tick code 4

/--
The program appends exactly the existing choice clauses. It preserves all remaining source
words and finishes at the first time cell, within the stated polynomial bound on head moves.
-/
@[spec] theorem writeChoices_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (problem : TMSAT.Instance Γ) (input output : List Γ) (size : Nat)
    (hsize : problem.certificateLength + problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (output ++ word code problem).length + 64 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        Preparation.layout tick problem.certificateLength
          [problem.time + 1, NPToTMSAT.width problem, problem.verifier.states + 2,
            NPToTMSAT.width problem, problem.verifier.states + 2] input output⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeChoices tm zero one tick code different equal extra
    ⦃ fun _ cost final => final.config = ⟨some different,
        ChoiceIteration.layout tick (problem.time + 1) (NPToTMSAT.width problem)
          (problem.verifier.states + 2) (tick :: input) (tick :: (output ++ word code problem))⟩ ∧
        final.headPos = origin + problem.certificateLength + 1 ∧
        cost.steps ≤ elapsed + (timeBound (Γ := Γ) width).eval size ⦄ := by
  let times := problem.time + 1
  let positions := NPToTMSAT.width problem
  let states := problem.verifier.states + 2
  let cert := (formulaPrefix ((certificateClauses problem).rename Variable.name)).flatMap code
  let head := (formulaPrefix ((headClauses problem).rename Variable.name)).flatMap code
  let cells := (formulaPrefix ((tapeClauses problem).rename Variable.name)).flatMap code
  let preserved := [List.replicate times tick, List.replicate positions tick,
    List.replicate states tick, List.replicate positions tick, List.replicate states tick,
    tick :: input]
  let later := [List.replicate states tick, List.replicate positions tick,
    List.replicate states tick, tick :: input]
  let first := output ++ cert
  let second := tick :: (first ++ head)
  let origin' := origin + problem.certificateLength + 1
  let certificateTime :=
    (CertificateChoices.timeBound width 1 (Finset.univ : Finset Γ).toList).eval size
  let headTime := (HeadChoices.timeBound width).eval size
  let clock₁ := elapsed + certificateTime
  let clock₂ := clock₁ + problem.certificateLength + 1
  let clock₃ := clock₂ + headTime
  have hw : word code problem = cert ++ head ++ cells := word_eq_parts code problem
  have hcert : problem.certificateLength + regionSpan preserved +
      (tick :: output).length + 1 ≤ size := by
    simp only [preserved, regionSpan, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil, List.length_replicate, List.length_append] at *
    dsimp [times, positions, states] at *
    rw [hw, List.length_append, List.length_append] at hsize
    lia
  have hhead : times + 2 * positions + 2 * states + (tick :: input).length +
      ((tick :: first) ++ head).length + 32 ≤ size := by
    simp only [List.length_cons, List.length_append, first] at *
    dsimp [times, positions, states] at *
    rw [hw, List.length_append, List.length_append] at hsize
    lia
  have htape : times + positions + regionSpan later + (second ++ cells).length ≤ size := by
    simp only [later, second, first, regionSpan, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil, List.length_replicate,
      List.length_append] at *
    dsimp [times, positions, states] at *
    rw [hw, List.length_append, List.length_append] at hsize
    lia
  have hc := CertificateChoices.writeCertificateChoicesAcross_spec (tm := tm)
    zero one hne tick [] code width hwidth problem preserved (regionSpan preserved)
    (by lia) (tick :: output) label origin elapsed
  have hmono :=
    (CertificateChoices.timeBound width 1 (Finset.univ : Finset Γ).toList).eval_mono hcert
  have he := eraseCertificate_spec (tm := tm) tick problem.certificateLength times positions states
    input first label origin clock₁
  have hh := HeadChoices.writeHeadClauses_spec (tm := tm) zero one hne tick code width hwidth
    different equal extra hfirst hlast hother problem (tick :: input) (tick :: first)
    size label origin' clock₂ hhead
  have ht := TapeChoices.writeTapeChoices_spec (tm := tm) zero one hne tick code width hwidth
    problem later second size htape (some different) origin' clock₃
  dsimp only [preserved, later, times, positions, states] at hc ht
  simp only [List.length_cons, List.length_nil] at hc ht
  vcgen [writeChoices, hc, he, hh, ht]
  all_goals
    simp_all [Preparation.layout, CertificateChoices.layoutAcross, HeadChoices.AtInput,
      TapeChoices.AtInput, TapeChoices.layout, ChoiceIteration.layout, unaryWord,
      preserved, later, times, positions, states, first, second, cert, head, cells,
      clock₁, clock₂, clock₃, certificateTime,
      headTime, origin', timeBound, Nat.add_assoc, List.append_assoc]
    all_goals lia

end Algolean.Algorithms.NPToSAT.Choices
