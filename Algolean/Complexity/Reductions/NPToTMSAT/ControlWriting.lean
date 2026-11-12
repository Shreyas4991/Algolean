/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.LiteralWriting
public import Algolean.Complexity.Reductions.NPToTMSAT.TransitionClauses

/-!
# Writing requirements on the next head position and state

* `writeForbiddenControlClause` excludes one combination of a current head, scanned symbol,
  and next head. It writes the existing SAT clause with those three negative literals.
* Its specification proves the exact output, preserves every selected index and the starting
  head position, and bounds the number of head moves.

The containing machine fixes the scanned symbol and output alphabet. The selected time,
positions, and states are read from the tape when it runs.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToTMSAT.ControlWriting

open Computability Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Problems Problems.SAT
open HeadChoices LiteralWriting
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [Encodable Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- This is the existing clause excluding the three selected head and cell values together. -/
@[expose] def forbiddenWord (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbol : Option (TapeSymbol Γ)) : List Γ :=
  (formulaPrefix [Clause.forbid [headNameAtTime choice false false,
    tapeName choice false false symbol, headNameAtTime choice true true]]).flatMap code

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem forbiddenWord_eq (code : CodeSymbol → List Γ) (choice : ActiveChoices)
    (symbol : Option (TapeSymbol Γ)) :
    forbiddenWord code choice symbol = headLiteralWord code choice false false false ++
      tapeLiteralWord code choice false false false symbol ++
        headLiteralWord code choice false true true ++ code (.inr 3) ++ code (.inr 4) := by
  simp [forbiddenWord, formulaPrefix, Clause.forbid, certificateEncoding_encode_neg,
    certificateEncoding_encode_nil, headLiteralWord, tapeLiteralWord,
    List.flatMap_append, List.flatMap_map, List.append_assoc]

/--
This writes the clause excluding the selected current head, scanned symbol, and next head
from holding together. The containing machine fixes the symbol and output representations;
the time, positions, and states are read from their selected unary words.
-/
def writeForbiddenControlClause (tm : SingleTapeTM Γ) (zero one tick : Γ)
    (code : CodeSymbol → List Γ) (symbol : Option (TapeSymbol Γ)) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeHeadLiteralAtTime tm zero one tick code false false false
  writeTapeLiteral tm zero one tick code false false false symbol
  writeHeadLiteralAtTime tm zero one tick code false true true
  appendAcross tm (code (.inr 3) ++ code (.inr 4)) 2

/-- This bounds the three literals and the symbols that finish their clause. -/
@[expose] def forbiddenTime (width size : Nat) : Nat := 15 * markedNumberBudget width size

/-- The writer appends exactly the existing SAT clause and preserves every selected word. -/
@[spec] theorem writeForbiddenControlClause_spec (zero one : Γ) (hne : zero ≠ one) (tick : Γ)
    (code : CodeSymbol → List Γ) (width : Nat) (hwidth : ∀ symbol, (code symbol).length = width)
    (choice : ActiveChoices) (symbol : Option (TapeSymbol Γ))
    (input output : List Γ) (size : Nat)
    (hsize : choice.size + input.length +
      (output ++ forbiddenWord code choice symbol).length + 32 ≤ size)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtPair tick choice input output label origin current ∧
        cost.steps ≤ elapsed ⦄
      writeForbiddenControlClause tm zero one tick code symbol
    ⦃ fun _ cost final => AtPair tick choice input
        (output ++ forbiddenWord code choice symbol) label origin final ∧
        cost.steps ≤ elapsed + forbiddenTime width size ⦄ := by
  let first := output ++ headLiteralWord code choice false false false
  let second := first ++ tapeLiteralWord code choice false false false symbol
  let third := second ++ headLiteralWord code choice false true true
  let ending := code (.inr 3) ++ code (.inr 4)
  have hdata : choice.size + input.length + (third ++ ending).length + 32 ≤ size := by
    simpa only [forbiddenWord_eq, third, second, first, ending, List.length_append,
      Nat.add_assoc] using hsize
  have hfirst : choice.size + input.length + first.length + 32 ≤ size := by
    simp only [third, second, List.length_append] at hdata
    lia
  have hsecond : choice.size + input.length + second.length + 32 ≤ size := by
    simp only [third, List.length_append] at hdata
    lia
  have hthird : choice.size + input.length + third.length + 32 ≤ size := by
    simp only [List.length_append] at hdata
    lia
  have hf := writeHeadLiteralAtTime_spec (tm := tm) zero one hne tick code width hwidth choice
    false false false input output size hfirst label origin elapsed
  have hs := writeTapeLiteral_spec (tm := tm) zero one hne tick code width hwidth choice
    false false false symbol input first size hsecond label origin
    (elapsed + 5 * markedNumberBudget width size)
  have ht := writeHeadLiteralAtTime_spec (tm := tm) zero one hne tick code width hwidth choice
    false true true input second size hthird label origin
    (elapsed + 9 * markedNumberBudget width size)
  have he := appendPart_spec (tm := tm) ending tick choice input third width size hdata label
    origin (elapsed + 14 * markedNumberBudget width size)
  dsimp only [ending] at he
  vcgen [writeForbiddenControlClause, hf, hs, ht, he]
  all_goals simp_all [forbiddenWord_eq, first, second, third, ending, forbiddenTime,
    tapeLiteralTime, List.append_assoc]
  all_goals lia

end Algolean.Algorithms.NPToTMSAT.ControlWriting
