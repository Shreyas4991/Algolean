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

/-!
# Computing the direct reduction to SAT

* `computer` is one fixed Query program that writes the computation formula for a fixed
  verifier. Its only input is the original input word.
* The stored correctness statement identifies the exact encoded SAT output and gives a
  polynomial bound on head moves. The final tape contains only that word, with the head at
  its first symbol.

The verifier, certificate bound, and time bound are fixed when constructing the program.
Its finite transition cases are part of the program. It reads the original input and computes
its bounds on the tape.
-/

public section

namespace Algolean.Algorithms.NPToSAT

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT Polynomial
open NPToTMSAT Alphabet
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

private noncomputable def writeFormula (tm : SingleTapeTM Γ) [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (different equal extra : tm.State)
    (record : Option Γ → tm.State) (yes : Γ) : Prog (TMQuery tm) Unit := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact do [TMQuery tm]
    Start.program tm verifier certificate time zero one one zero different equal extra
    InitialWriting.writeInitialClauses tm verifier zero one one Start.code different equal record
    Writing.writeTransitions tm verifier zero one one Start.code different equal extra
    Finishing.finish tm zero one one Start.code yes

private noncomputable def timeBound (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) : Polynomial Nat := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  exact Start.timeBound verifier certificate time one zero +
    (InitialWriting.timeBound (Γ := Γ) 8 + Writing.transitionTimeBound verifier 8 +
      Finishing.timeBound 8).comp (sizeBound verifier certificate time)

open Classical in
private theorem writeFormula_spec {tm : SingleTapeTM Γ} [DecidableEq tm.State]
    (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (zero one : Γ) (hne : zero ≠ one)
    (different equal extra : tm.State) (hfirst : different ≠ equal)
    (hlast : different ≠ extra) (hother : equal ≠ extra)
    (record : Option Γ → tm.State) (hrecord : Function.Injective record)
    (yes : Γ) (input : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      writeFormula tm verifier certificate time zero one different equal extra record yes
    ⦃ fun _ cost final => final.config.BiTape =
        BiTape.mk₁ (encode verifier certificate time yes input) ∧
        cost.steps ≤ elapsed +
          (timeBound verifier certificate time zero one).eval input.length ⦄ := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let code := Start.code (Γ := Γ)
  have hwidth : ∀ symbol : CodeSymbol, (code symbol).length = 8 := by
    intro symbol
    simp [code, Start.code, CodeSymbol, Extended]
  let problem : TMSAT.Instance Γ :=
    ⟨verifier, input, certificate.eval input.length, time.eval input.length⟩
  let first := Start.choiceWord verifier certificate time input
  let second := (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code
  let third := (formulaPrefix ((NPToSAT.stepClauses problem).rename Variable.name)).flatMap code
  let fourth :=
    (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap code
  let size := (sizeBound verifier certificate time).eval input.length
  let clock₁ := elapsed + (Start.timeBound verifier certificate time one zero).eval input.length
  let clock₂ := clock₁ + (InitialWriting.timeBound (Γ := Γ) 8).eval size
  let clock₃ := clock₂ + (Writing.transitionTimeBound verifier 8).eval size
  let place : ℤ := origin + input.length + 1 + problem.certificateLength + 1
  have hword : encode verifier certificate time yes input =
      first ++ second ++ third ++ fourth ++ code (.inr 5) := by
    simp only [encode, formula, indexedFormula, encodingOver_encode_eq_formulaPrefix,
      CNF.rename, List.map_append, formulaPrefix_append, List.flatMap_append,
      first, Start.choiceWord, Choices.word, second, third, fourth, problem, code, Start.code,
      List.append_assoc]
    rfl
  have hsize := source_size_le verifier certificate time yes input
  rw [hword] at hsize
  simp only [List.length_append] at hsize
  have hi : problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + (one :: input).length +
        ((one :: first) ++ second).length + 64 ≤ size := by
    simp only [List.length_cons, List.length_append]
    dsimp only [problem, size] at *
    lia
  have ht : problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + (one :: input).length +
        (((one :: first) ++ second) ++ third).length + 32 ≤ size := by
    simp only [List.length_cons, List.length_append]
    dsimp only [problem, size] at *
    lia
  have hf : problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length +
        (first ++ second ++ third ++ fourth).length + 64 ≤ size := by
    simp only [List.length_append]
    dsimp only [problem, size] at *
    lia
  have hs := Start.program_spec (tm := tm) verifier certificate time zero one hne one zero
    (Ne.symm hne) different equal extra hfirst hlast hother yes input label origin elapsed
  have hI := InitialWriting.writeInitialClauses_spec (tm := tm) verifier zero one hne one code
    8 hwidth different equal hfirst record hrecord problem rfl (one :: first) size
    (by simpa only [problem, second] using hi) (some different) place clock₁
  have hT := Writing.writeTransitions_spec (tm := tm) verifier zero one hne one code 8 hwidth
    different equal extra hfirst hlast hother problem rfl (one :: input)
    ((one :: first) ++ second) size ht (some different) place clock₂
  have hF := Finishing.finish_spec (tm := tm) zero one hne one code 8 hwidth problem yes input
    (first ++ second ++ third) size (by simpa only [fourth, List.append_assoc] using hf)
    (some different) place clock₃
  simp only [HeadChoices.AtInput] at hT
  dsimp only [code, this] at hI hT hF
  vcgen [writeFormula, hs, hI, hT, hF]
  all_goals
    simp_all [place, first, second, third, fourth, problem, clock₁, clock₂, clock₃,
      timeBound, size, code, Polynomial.eval_comp, List.append_assoc, Nat.add_assoc]

/--
This single-tape program writes the fixed verifier's SAT formula for every input length.
The stored specification proves the exact output and a polynomial bound on head moves.
-/
noncomputable def computer (verifier : SingleTapeTM.Description (TMSAT.TapeSymbol Γ))
    (certificate time : Polynomial Nat) (yes : Γ) :
    TMQuery.PolyTimeComputable (encode verifier certificate time yes) := by
  classical
  let : Encodable Γ := Encodable.ofEquiv (Fin (Fintype.card Γ)) (Fintype.equivFin Γ)
  let digits : {pair : Γ × Γ // pair.1 ≠ pair.2} := Classical.choice (by
    obtain ⟨zero, one, hne⟩ := exists_pair_ne Γ
    exact ⟨⟨(zero, one), hne⟩⟩)
  let zero := digits.val.1
  let one := digits.val.2
  have hne : zero ≠ one := digits.property
  let tm : SingleTapeTM Γ := {
    State := Option Γ ⊕ Fin 3
    q₀ := .inr 0
    tr := fun _ symbol => (⟨symbol, none⟩, none) }
  let different : tm.State := .inr 0
  let equal : tm.State := .inr 1
  let extra : tm.State := .inr 2
  let record : Option Γ → tm.State := Sum.inl
  have hfirst : different ≠ equal := by simp [different, equal, tm]
  have hlast : different ≠ extra := by simp [different, extra, tm]
  have hother : equal ≠ extra := by simp [equal, extra, tm]
  have hrecord : Function.Injective record := by
    intro first second heq
    exact Sum.inl.inj heq
  refine {
    tm := tm
    program := writeFormula tm verifier certificate time zero one different equal extra record yes
    timeBound := (timeBound verifier certificate time zero one).eval
    poly := timeBound verifier certificate time zero one
    bounds := fun _ => le_rfl
    computesWithin := ?_ }
  apply TMQuery.ComputesWithin.of_outputsWithinTime
  intro input
  obtain ⟨cost, final, completed, output, bound⟩ :
      ∃ cost final,
        Completes
          (writeFormula tm verifier certificate time zero one different equal extra record yes)
          (TMState.init tm input) cost final ∧
        final.config.BiTape = BiTape.mk₁ (encode verifier certificate time yes input) ∧
        cost.steps ≤ (timeBound verifier certificate time zero one).eval input.length := by
    apply Spec.completes
    vcgen [writeFormula_spec verifier certificate time zero one hne different equal extra
      hfirst hlast hother record hrecord yes input (some tm.q₀) 0 0]
    all_goals simp_all [TMState.init, SingleTapeTM.initCfg]
  exact completed.outputsWithinTime output bound

end Algolean.Algorithms.NPToSAT
