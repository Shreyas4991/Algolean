/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Start
public import Algolean.Complexity.Reductions.NPtoSAT.InitialWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Writing
public import Algolean.Complexity.Reductions.NPtoSAT.Finishing
public import Algolean.Models.SingleTapeTM.Computability

import Mathlib.Logic.Equiv.List

/-!
# Computing the direct reduction to SAT

* `computer` writes the fixed verifier's formula in the encoding over the input alphabet.
* `formulaComputer` writes the same formula directly in SAT's original formula alphabet.
* The stored correctness statement identifies the exact encoded SAT output and gives a
  polynomial bound on head moves. The final tape contains only that word, with the head at
  its first symbol.

The verifier, certificate bound, and time bound are fixed when constructing the program.
Its finite transition cases are part of the program. It reads the original input and computes
its bounds on the tape.
-/


attribute [local instance 100] Fintype.toEncodable Encodable.decidableEqOfEncodable


open Cslib.Turing.SingleTapeTM Cslib.Turing.SingleTapeTM.BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT Polynomial
open NPToSAT.Computation Alphabet Computability
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

private def control : SingleTapeTM Γ where
  State := Option Γ ⊕ Fin 3
  q₀ := .inr 0
  tr _ symbol := (⟨symbol, none⟩, none)

private noncomputable def writeFormula (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (different equal extra : tm.State)
    (record : Option Γ → tm.State) (yes : Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  Start.program tm verifier certificate time zero one one zero different equal extra code
  InitialWriting.writeInitialClauses tm verifier zero one one code different equal record
  Writing.writeTransitions tm verifier zero one one code different equal extra
  Finishing.finish tm zero one one code yes

private noncomputable def timeBound (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (width : Nat) : Polynomial Nat :=
  Start.timeBound verifier certificate time one zero width +
    (InitialWriting.timeBound (Γ := Γ) width + Writing.transitionTimeBound verifier width +
      Finishing.timeBound width).comp (sizeBound verifier certificate time)

private theorem writeFormula_spec {tm : SingleTapeTM Γ} [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (hne : zero ≠ one)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width) (hsmall : width ≤ 8)
    (yes : Γ) (input : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeFormula tm verifier certificate time zero one different equal extra record yes code
    ⦃ fun _ cost final => final.config.BiTape =
        BiTape.mk₁ ((encoding.encode (formula verifier certificate time yes input)).flatMap code) ∧
        cost.steps ≤ elapsed +
          (timeBound verifier certificate time zero one width).eval input.length ⦄ := by
  let problem : BoundedVerification Γ :=
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
  let first := Start.choiceWord verifier certificate time input code
  let second := (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code
  let third := (formulaPrefix ((NPToSAT.stepClauses problem).rename Variable.name)).flatMap code
  let fourth :=
    (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap code
  let size := (sizeBound verifier certificate time).eval input.length
  let clock₁ :=
    elapsed + (Start.timeBound verifier certificate time one zero width).eval input.length
  let clock₂ := clock₁ + (InitialWriting.timeBound (Γ := Γ) width).eval size
  let clock₃ := clock₂ + (Writing.transitionTimeBound verifier width).eval size
  let place : ℤ := origin + input.length + 1 + problem.certificateLength + 1
  have hword : (encoding.encode (formula verifier certificate time yes input)).flatMap code =
      first ++ second ++ third ++ fourth ++ code (.inr 5) := by
    simp only [formula, indexedFormula, encoding_encode_eq_formulaPrefix,
      CNF.rename, List.map_append, formulaPrefix_append, List.flatMap_append,
      first, Start.choiceWord, Choices.word, second, third, fourth, problem,
      List.append_assoc, List.flatMap_singleton]
  have hsize := source_size_le_code verifier certificate time yes input code width hwidth hsmall
  rw [hword] at hsize
  simp only [List.length_append] at hsize
  have hi : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + (one :: input).length +
        ((one :: first) ++ second).length + 64 ≤ size := by
    simp only [List.length_cons, List.length_append]
    dsimp only [problem, size] at *
    lia
  have ht : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + (one :: input).length +
        (((one :: first) ++ second) ++ third).length + 32 ≤ size := by
    simp only [List.length_cons, List.length_append]
    dsimp only [problem, size] at *
    lia
  have hf : problem.time + 2 * NPToSAT.Computation.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (first ++ second ++ third ++ fourth).length + 64 ≤ size := by
    simp only [List.length_append]
    dsimp only [problem, size] at *
    lia
  have hs := Start.program_spec (tm := tm) verifier certificate time zero one hne one zero
    (Ne.symm hne) different equal extra hfirst hlast hother yes code width hwidth hsmall
    input label origin elapsed
  have hI := InitialWriting.writeInitialClauses_spec (tm := tm) verifier zero one hne one code
    width hwidth different equal hfirst record hrecord problem rfl (one :: first) size
    (by simpa only [problem, second] using hi) (some different) place clock₁
  have hT := Writing.writeTransitions_spec (tm := tm) verifier zero one hne one code width hwidth
    different equal extra hfirst hlast hother problem rfl (one :: input)
    ((one :: first) ++ second) size ht (some different) place clock₂
  have hF := Finishing.finish_spec (tm := tm) zero one hne one code width hwidth problem yes input
    (first ++ second ++ third) size (by simpa only [fourth, List.append_assoc] using hf)
    (some different) place clock₃
  simp only [HeadChoices.AtInput] at hT
  vcgen [writeFormula, hs, hI, hT, hF]
  all_goals
    simp_all [place, first, second, third, fourth, problem, clock₁, clock₂, clock₃,
      timeBound, size, Polynomial.eval_comp, List.append_assoc, Nat.add_assoc]

/--
This single-tape program writes the fixed verifier's SAT formula for every input length.
The stored specification proves the exact output and a polynomial bound on head moves.
-/
private noncomputable def codedComputer (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) (code : CodeSymbol → List Γ)
    (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width) (hsmall : width ≤ 8) :
    TMQuery.PolyTimeComputable (fun input =>
      (encoding.encode (formula verifier certificate time yes input)).flatMap code) :=
  let digits : {pair : Γ × Γ // pair.1 ≠ pair.2} := Classical.choice (by
    obtain ⟨zero, one, hne⟩ := exists_pair_ne Γ
    exact ⟨⟨(zero, one), hne⟩⟩)
  let zero := digits.val.1
  let one := digits.val.2
  let tm : SingleTapeTM Γ := control
  let different : tm.State := .inr 0
  let equal : tm.State := .inr 1
  let extra : tm.State := .inr 2
  let record : Option Γ → tm.State := Sum.inl
  {
    tm := tm
    program :=
      writeFormula tm verifier certificate time zero one different equal extra record yes code
    timeBound := (timeBound verifier certificate time zero one width).eval
    poly := timeBound verifier certificate time zero one width
    bounds := fun _ => le_rfl
    computesWithin := by
      have hne : zero ≠ one := digits.property
      have hfirst : different ≠ equal := by simp [different, equal, tm, control]
      have hlast : different ≠ extra := by simp [different, extra, tm, control]
      have hother : equal ≠ extra := by simp [equal, extra, tm, control]
      have hrecord : Function.Injective record := Sum.inl_injective
      apply TMQuery.ComputesWithin.of_outputsWithinTime
      intro input
      obtain ⟨cost, final, completed, output, bound⟩ :
          ∃ cost final,
            Completes
              (writeFormula tm verifier certificate time zero one different equal extra record
                yes code)
              (TMState.init tm input) cost final ∧
            final.config.BiTape =
              BiTape.mk₁
                ((encoding.encode (formula verifier certificate time yes input)).flatMap code) ∧
            cost.steps ≤
              (timeBound verifier certificate time zero one width).eval input.length := by
        apply Spec.completes
        vcgen [writeFormula_spec verifier certificate time zero one hne different equal extra
          hfirst hlast hother record hrecord code width hwidth hsmall yes input (some tm.q₀) 0 0]
        all_goals simp_all [TMState.init, SingleTapeTM.initCfg]
      exact completed.outputsWithinTime output bound }

omit [Inhabited Γ] in
private theorem encode_eq_flatMap (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) :
    encode verifier certificate time yes = fun input =>
      (encoding.encode (formula verifier certificate time yes input)).flatMap Start.code := by
  funext input
  have hcode : Start.code (Γ := Γ) =
      fun symbol : CodeSymbol => (finiteWordsOver CodeSymbol Γ).encode [symbol] := by
    funext symbol
    rfl
  rw [hcode]
  simpa only [encode, encodingOver, Encoding.over, Encoding.comp] using
    encode_finiteWordsOver (Γ := Γ) (encoding.encode (formula verifier certificate time yes input))

/-- This writes the verifier's formula using the SAT encoding over the input alphabet. -/
noncomputable def computer (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) :
    TMQuery.PolyTimeComputable (encode verifier certificate time yes) :=
  (encode_eq_flatMap verifier certificate time yes).symm ▸
    codedComputer verifier certificate time yes Start.code 8
      (by intro symbol; simp [Start.code, CodeSymbol, Extended]) (by decide)

/-- This writes the verifier's formula directly in SAT's original eight-symbol alphabet. -/
noncomputable def formulaComputer
    (verifier : SingleTapeTM.Description (TapeSymbol CodeSymbol))
    (certificate time : Polynomial Nat) (yes : CodeSymbol) :
    TMQuery.PolyTimeComputable (fun input =>
      encoding.encode (formula verifier certificate time yes input)) :=
  (funext fun input => List.flatMap_singleton'
    (encoding.encode (formula verifier certificate time yes input))) ▸
      codedComputer verifier certificate time yes (fun symbol => [symbol]) 1
        (by simp) (by decide)

end Algolean.Algorithms.NPToSAT
