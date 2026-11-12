/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.FinalWriting
public import Algolean.Complexity.Reductions.NPtoSAT.Output

/-!
# Completing the direct reduction's output

* `finish` writes the final acceptance clauses, ends the SAT formula, and erases the input
  and bounds. It leaves exactly the encoded formula, with its first symbol under the head.
* `finish_spec` identifies the appended clauses and bounds the number of head moves.

The accepting symbol and alphabet codes are fixed when constructing the containing machine.
The time and tape-width bounds are read from the tape.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.Finishing

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open NPToTMSAT Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This writes the acceptance clauses and leaves only the completed SAT word on the tape. -/
noncomputable def finish (tm : SingleTapeTM Γ)
    (zero one tick : Γ) (code : CodeSymbol → List Γ) (yes : Γ) : Prog (TMQuery tm) Unit :=
    do [TMQuery tm]
  FinalWriting.writeFinalClauses tm zero one tick code yes
  Output.finish tm code

/-- This polynomial bounds the final clause writer and the erasure of all source words. -/
noncomputable def timeBound (width : Nat) : Polynomial Nat :=
  FinalWriting.timeBound width + 5 * X + C (2 * width + 64)

/--
The program writes the acceptance clauses, ends the formula, and erases the input and bounds.
Its final tape is clean, and the head points to the first output symbol.
-/
@[spec] theorem finish_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (problem : BoundedVerification Γ) (yes : Γ) (input output : List Γ) (size : Nat)
    (hsize : problem.time + 2 * NPToTMSAT.width problem + 2 * (problem.verifier.states + 2) +
      input.length + (output ++
        (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap
          code).length + 64 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let word := (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap
      code
    let offset := problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length + 9
    ⦃ fun cost current => current.config = ⟨label,
        ChoiceIteration.layout tick (problem.time + 1) (NPToTMSAT.width problem)
          (problem.verifier.states + 2) (tick :: input) (tick :: output)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finish tm zero one tick code yes
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.mk₁ (output ++ word ++ code (.inr 5))⟩ ∧
        final.headPos = origin + offset ∧
        cost.steps ≤ elapsed + (timeBound width).eval size ⦄ := by
  dsimp only
  let word := (formulaPrefix ((Formula.finalClauses problem yes).rename Variable.name)).flatMap
    code
  have hfinal : problem.time + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + (tick :: input).length +
        ((tick :: output) ++ word).length + 32 ≤ size := by
    simp only [List.length_cons, List.length_append] at hsize ⊢
    dsimp only [word]
    lia
  have hf := FinalWriting.writeFinalClauses_spec (tm := tm) zero one hne tick code width hwidth
    problem yes (tick :: input) (tick :: output) size hfinal label origin elapsed
  have he := Output.finish_spec (tm := tm) tick code (problem.time + 1)
    (NPToTMSAT.width problem) (problem.verifier.states + 2) input (output ++ word) label origin
    (elapsed + (FinalWriting.timeBound width).eval size)
  have hcleanup : 3 * (problem.time + 1 + 2 * NPToTMSAT.width problem +
      2 * (problem.verifier.states + 2) + input.length + 7) +
      2 * (output ++ word).length + 2 * (code (.inr 5)).length + 17 ≤
        5 * size + (2 * width + 64) := by
    rw [hwidth]
    dsimp only [word]
    lia
  vcgen [finish, hf, he]
  all_goals
    simp_all only [List.cons_append, Nat.cast_add, Nat.cast_ofNat,
      timeBound, eval_add, eval_mul, eval_ofNat, eval_X, eval_C, word]
    all_goals lia

end Algolean.Algorithms.NPToSAT.Finishing
