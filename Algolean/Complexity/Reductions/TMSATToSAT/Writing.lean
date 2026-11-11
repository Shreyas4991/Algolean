/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Writing
public import Algolean.Problems.Encodings.SAT

/-!
# Writing SAT literals from names stored on the tape

A literal is a Boolean variable, such as `x`, or its negation, `¬x`. The tape initially holds
a sign followed by the variable's name in binary. For example, the name `101` and a negative
sign describe the negation of the variable named `101`. A blank separates the sign and name
from the output already written to their right. The cell just before the sign is also blank.
These are two parts of the same tape.

The program reads the sign and name and adds that literal to the end of the output in SAT's
format. It leaves the original sign, name, and earlier output unchanged. It also leaves all
cells farther left unchanged and returns the head to the sign.

The containing machine chooses the two symbols for binary digits and the representation of
each SAT symbol once. The sign and name can change between runs because they are read from
the tape. The program copies a name already on the tape; it does not calculate the name's
number from the variable's indices.

`appendLiteralOver` uses SAT's existing representation over `Γ`. `endClause` adds the symbols
that finish a clause, and `endFormula` adds the symbol that finishes the whole formula.
The correctness theorems describe what each program writes, where the head stops, and exactly
how many head moves it makes.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Writing

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet
open Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

private def copyCell (tm : SingleTapeTM Γ) (restore : Γ) (word : List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  tape ←ₜ none
  moveₜ .Right
  nextRegion tm
  appendWord tm none word
  previousRegion tm
  moveₜ .Left
  tape ←ₜ some restore
  moveₜ .Right

private theorem copyCell_spec (restore : Γ) (word : List Γ) (left : StackTape Γ)
    (rest output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment left (restore :: rest) (StackTape.mapSome output)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyCell tm restore word
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons (some restore) left) rest
          (StackTape.mapSome (output ++ word))⟩ ∧
        final.headPos = origin + 1 ∧
        cost.steps = elapsed + 2 * (rest.length + output.length + word.length) + 13 ⦄ := by
  vcgen [copyCell,
    nextRegion_spec (tm := tm) (StackTape.cons none left) rest output StackTape.nil
      label (origin + 1) (elapsed + 1),
    appendWord_spec (tm := tm) none (StackTape.prepend rest.reverse (StackTape.cons none left))
      output word label (origin + (rest.length + 2 : Nat)) (elapsed + rest.length + 2),
    previousRegion_spec (tm := tm) left rest (output ++ word) StackTape.nil
      label (origin + (rest.length + 2 : Nat))
      (elapsed + rest.length + 2 + 2 * (output.length + word.length) + 6)]
  all_goals cases rest
  all_goals simp_all [TMState.move, TMState.write, TMState.moveCost,
    BiTape.segment, BiTape.write, BiTape.moveRight, BiTape.moveLeft]
  all_goals lia

private def copyName (tm : SingleTapeTM Γ) (zero one : Γ)
    (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some one then
      copyCell tm one (code (.inl true))
    else
      copyCell tm zero (code (.inl false))

private theorem copyName_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (bits : List Bool) (left : StackTape Γ) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment left
        (bits.map (fun bit => if bit then one else zero)) (StackTape.mapSome output)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      copyName tm zero one code
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment
          (StackTape.prepend (bits.map (fun bit => if bit then one else zero)).reverse left) []
          (StackTape.mapSome (output ++ bits.flatMap (fun bit => code (.inl bit))))⟩ ∧
        final.headPos = origin + bits.length ∧ cost.steps = elapsed +
          (width + 1) * bits.length ^ 2 + 2 * bits.length * output.length +
            (width + 12) * bits.length ⦄ := by
  induction bits generalizing left output origin elapsed with
  | nil =>
    unfold copyName
    vcgen [Spec.while_false_spec]
    simp_all
  | cons bit bits ih =>
    unfold copyName
    vcgen [Spec.while_step_spec (loop := copyName tm zero one code) (hloop := rfl),
      copyCell_spec one (code (.inl true)) left
        (bits.map (fun bit => if bit then one else zero)) output label origin elapsed,
      copyCell_spec zero (code (.inl false)) left
        (bits.map (fun bit => if bit then one else zero)) output label origin elapsed,
      ih (StackTape.cons (some (if bit then one else zero)) left) (output ++ code (.inl bit))
        (origin + 1) (elapsed + 2 * (bits.length + output.length + width) + 13)]
    all_goals cases bit
    all_goals simp_all [List.reverse_cons, StackTape.prepend_append, List.append_assoc]
    all_goals ring_nf at *
    all_goals simp_all

private def returnSource (tm : SingleTapeTM Γ) (ending : List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  appendWord tm none ending
  previousRegion tm

private theorem returnSource_spec (ending : List Γ) (left : StackTape Γ)
    (input output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend input.reverse (StackTape.cons none left)) []
        (StackTape.mapSome output)⟩ ∧ current.headPos = origin ∧ cost.steps = elapsed ⦄
      returnSource tm ending
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left) input (StackTape.mapSome (output ++ ending))⟩ ∧
        final.headPos = origin - input.length ∧
        cost.steps = elapsed + 2 * (output.length + ending.length) + input.length + 10 ⦄ := by
  vcgen [returnSource,
    appendWord_spec (tm := tm) none (StackTape.prepend input.reverse (StackTape.cons none left))
      output ending label (origin + 1) (elapsed + 1),
    previousRegion_spec (tm := tm) left input (output ++ ending) StackTape.nil
      label (origin + 1) (elapsed + 1 + 2 * (output.length + ending.length) + 6)]
  all_goals simp_all [TMState.move, TMState.moveCost]
  all_goals lia

/--
This reads a sign and variable name from the tape and adds one literal after the existing
output. Initially, the head is on the sign: `zero` means the variable itself, and `one` means
its negation. The following cells contain the name, with `zero` and `one` representing its
binary digits. The cell just before the sign must be blank. One blank separates the name from
the output, and every cell beyond the output must be blank.

The program leaves the original sign, name, existing output, and all cells farther left
unchanged. It finishes with the head back on the sign.

This is a machine template. The containing machine chooses `zero`, `one`, and `code` once.
The function `code` specifies which tape word represents each SAT symbol. The same program
then handles every sign and name by reading them from the tape.
-/
def appendLiteral (tm : SingleTapeTM Γ) (zero one : Γ) (code : CodeSymbol → List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  ifₜ tape =ₜ some one then
    copyCell tm one (code (.inr 1))
  else
    copyCell tm zero (code (.inr 0))
  copyName tm zero one code
  returnSource tm (code (.inr 2))

/-- Appending a literal preserves its source and restores the head with the exact move count. -/
@[spec] theorem appendLiteral_spec (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (negative : Bool) (name : List Bool) (left : StackTape Γ) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome output)⟩ ∧ current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendLiteral tm zero one code
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome (output ++ code (.inr (if negative then 1 else 0)) ++
          name.flatMap (fun bit => code (.inl bit)) ++ code (.inr 2)))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          (width + 1) * name.length ^ 2 + 2 * name.length * output.length +
            (5 * width + 15) * name.length + 4 * output.length + 6 * width + 24 ⦄ := by
  let digit := if negative then one else zero
  let sign : CodeSymbol := .inr (if negative then 1 else 0)
  let source := digit :: name.map (fun bit => if bit then one else zero)
  have hlength : (name.flatMap (fun bit => code (.inl bit))).length = name.length * width := by
    simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  vcgen [appendLiteral,
    copyCell_spec one (code (.inr 1)) (StackTape.cons none left)
      (name.map (fun bit => if bit then one else zero)) output label origin elapsed,
    copyCell_spec zero (code (.inr 0)) (StackTape.cons none left)
      (name.map (fun bit => if bit then one else zero)) output label origin elapsed,
    copyName_spec zero one hne code width hwidth name
      (StackTape.cons (some digit) (StackTape.cons none left)) (output ++ code sign)
      label (origin + 1) (elapsed + 2 * (name.length + output.length + width) + 13),
    returnSource_spec (code (.inr 2)) left source
      (output ++ code sign ++ name.flatMap (fun bit => code (.inl bit)))
      label (origin + (name.length + 1 : Nat))
      (elapsed + 2 * (name.length + output.length + width) + 13 +
        (width + 1) * name.length ^ 2 + 2 * name.length * (output ++ code sign).length +
          (width + 12) * name.length)]
  all_goals cases negative
  all_goals simp_all [digit, sign, source, List.reverse_cons,
    StackTape.prepend_append, List.append_assoc]
  all_goals ring_nf at *

/--
This proves that `appendLiteral` adds the correct sign, name, and symbol marking the end of
the name. The original sign and name, the previous output, all cells farther left, and the
machine's state remain unchanged. The head returns to the sign. When each SAT symbol is
represented by `width` tape cells, the theorem gives the exact number of head moves.
-/
theorem appendLiteral_correct (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (negative : Bool) (name : List Bool) (left : StackTape Γ) (output : List Γ)
    (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.cons none left)
      ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
      (StackTape.mapSome output)) :
    Runs (appendLiteral tm zero one code) s
      (BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome (output ++ code (.inr (if negative then 1 else 0)) ++
          name.flatMap (fun bit => code (.inl bit)) ++ code (.inr 2))))
      s.headPos ((width + 1) * name.length ^ 2 + 2 * name.length * output.length +
        (5 * width + 15) * name.length + 4 * output.length + 6 * width + 24) := by
  apply Spec.runs
  vcgen [appendLiteral_spec zero one hne code width hwidth negative name left output
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

variable [Nontrivial Γ]

/--
This uses `appendLiteral` to write a literal in SAT's existing representation over `Γ`.
Each SAT symbol is written as eight tape cells. The containing machine chooses the two
symbols for reading binary digits once. The program reads the sign and name from the tape
and leaves them there so that later instructions can read them again.
-/
noncomputable def appendLiteralOver (tm : SingleTapeTM Γ) (zero one : Γ) :
    Prog (TMQuery tm) Unit :=
  appendLiteral tm zero one (fun symbol => (finiteWordsOver CodeSymbol Γ).encode [symbol])

/-- Writing a literal over `Γ` preserves its source and uses the stated quadratic move count. -/
@[spec] theorem appendLiteralOver_spec (zero one : Γ) (hne : zero ≠ one)
    (negative : Bool) (name : List Bool) (left : StackTape Γ) (output : List Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome output)⟩ ∧ current.headPos = origin ∧ cost.steps = elapsed ⦄
      appendLiteralOver tm zero one
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome (output ++ (finiteWordsOver CodeSymbol Γ).encode
          (certificateEncoding.encode
            [if negative then Literal.neg name else Literal.pos name]).dropLast))⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed + 9 * name.length ^ 2 +
          2 * name.length * output.length + 55 * name.length + 4 * output.length + 72 ⦄ := by
  have hwidth (symbol : CodeSymbol) :
      ((finiteWordsOver CodeSymbol Γ).encode [symbol]).length = 8 := by
    simp [CodeSymbol, Extended]
  have hword : (finiteWordsOver CodeSymbol Γ).encode
      ((.inr (if negative then 1 else 0)) :: name.map Sum.inl ++ [.inr 2]) =
      (finiteWordsOver CodeSymbol Γ).encode [.inr (if negative then 1 else 0)] ++
        name.flatMap (fun bit => (finiteWordsOver CodeSymbol Γ).encode [.inl bit]) ++
        (finiteWordsOver CodeSymbol Γ).encode [.inr 2] := by
    rw [encode_finiteWordsOver]
    simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_map,
      List.flatMap_nil, List.append_nil]
  have hliteral : (certificateEncoding.encode
      [if negative then Literal.neg name else Literal.pos name]).dropLast =
      (.inr (if negative then 1 else 0)) :: name.map Sum.inl ++ [.inr 2] := by
    cases negative <;>
      simp [certificateEncoding_encode_pos, certificateEncoding_encode_neg,
        certificateEncoding_encode_nil, List.dropLast_cons_of_ne_nil]
  vcgen [appendLiteralOver, appendLiteral_spec zero one hne
    (fun symbol => (finiteWordsOver CodeSymbol Γ).encode [symbol]) 8 hwidth
    negative name left output label origin elapsed]
  all_goals simp_all [List.append_assoc, add_assoc]

/--
This proves that the program adds the literal in SAT's existing representation over `Γ`.
The original sign and name, previous output, cells farther left, and machine state remain
unchanged. The head returns to the sign. If the name has `m` digits and the previous output
occupies `p` cells, the head makes exactly `9*m^2 + 2*m*p + 55*m + 4*p + 72` moves.

The statement uses `certificateEncoding` because it writes literals in the same way as a
clause. Its last symbol is removed because that symbol ends a whole clause; this program
writes only one literal.
-/
theorem appendLiteralOver_correct (zero one : Γ) (hne : zero ≠ one)
    (negative : Bool) (name : List Bool) (left : StackTape Γ) (output : List Γ)
    (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.cons none left)
      ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
      (StackTape.mapSome output)) :
    Runs (appendLiteralOver tm zero one) s
      (BiTape.segment (StackTape.cons none left)
        ((if negative then one else zero) :: name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome (output ++ (finiteWordsOver CodeSymbol Γ).encode
          (certificateEncoding.encode
            [if negative then Literal.neg name else Literal.pos name]).dropLast)))
      s.headPos (9 * name.length ^ 2 + 2 * name.length * output.length +
        55 * name.length + 4 * output.length + 72) := by
  apply Spec.runs
  vcgen [appendLiteralOver_spec zero one hne negative name left output
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

omit [Nontrivial Γ] in
/--
This adds two SAT symbols after the existing output. They mark the end of the current clause
and separate it from the next clause. The head starts and finishes at the first output cell.
The cell immediately before the output must be blank, as must all cells beyond its end.
The containing machine chooses once how `code` represents each SAT symbol on the tape.
-/
def endClause (tm : SingleTapeTM Γ) (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit :=
  appendWord tm none (code (.inr 3) ++ code (.inr 4))

omit [Nontrivial Γ] in
/-- Ending a clause preserves the old output and restores the head with the exact move count. -/
@[spec] theorem endClause_spec (code : CodeSymbol → List Γ) (left : StackTape Γ)
    (output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (StackTape.cons none left) output StackTape.nil⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      endClause tm code
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment (StackTape.cons none left)
        (output ++ code (.inr 3) ++ code (.inr 4)) StackTape.nil⟩ ∧
        final.headPos = origin ∧ cost.steps = elapsed +
          2 * (output.length + (code (.inr 3)).length + (code (.inr 4)).length) + 6 ⦄ := by
  vcgen [endClause, appendWord_spec (tm := tm) none left output
    (code (.inr 3) ++ code (.inr 4)) label origin elapsed]
  all_goals simp_all [List.append_assoc, add_assoc]

omit [Nontrivial Γ] in
/--
This proves that the program adds the clause endings, returns the head to the first output
cell, and leaves the machine state and cells farther left unchanged. It gives the exact move count.
-/
theorem endClause_correct (code : CodeSymbol → List Γ) (left : StackTape Γ)
    (output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.cons none left) output StackTape.nil) :
    Runs (endClause tm code) s
      (BiTape.segment (StackTape.cons none left)
        (output ++ code (.inr 3) ++ code (.inr 4)) StackTape.nil)
      s.headPos (2 * (output.length + (code (.inr 3)).length + (code (.inr 4)).length) + 6) := by
  apply Spec.runs
  vcgen [endClause_spec code left output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

omit [Nontrivial Γ] in
/--
This adds the SAT symbol that marks the end of the whole formula. The head starts and
finishes at the first output cell. The cell immediately before the output must be blank,
as must all cells beyond its end. The containing machine chooses once how `code` represents
each SAT symbol on the tape.
-/
def endFormula (tm : SingleTapeTM Γ) (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit :=
  appendWord tm none (code (.inr 5))

omit [Nontrivial Γ] in
/-- Ending the formula preserves the old output and restores the head with the exact move count. -/
@[spec] theorem endFormula_spec (code : CodeSymbol → List Γ) (left : StackTape Γ)
    (output : List Γ) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, BiTape.segment (StackTape.cons none left) output StackTape.nil⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      endFormula tm code
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.segment (StackTape.cons none left)
        (output ++ code (.inr 5)) StackTape.nil⟩ ∧ final.headPos = origin ∧
        cost.steps = elapsed + 2 * (output.length + (code (.inr 5)).length) + 6 ⦄ := by
  vcgen [endFormula, appendWord_spec (tm := tm) none left output
    (code (.inr 5)) label origin elapsed]

omit [Nontrivial Γ] in
/--
This proves that the program adds the formula ending, returns the head to the first output
cell, and leaves the machine state and cells farther left unchanged. It gives the exact move count.
-/
theorem endFormula_correct (code : CodeSymbol → List Γ) (left : StackTape Γ)
    (output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.cons none left) output StackTape.nil) :
    Runs (endFormula tm code) s
      (BiTape.segment (StackTape.cons none left) (output ++ code (.inr 5)) StackTape.nil)
      s.headPos (2 * (output.length + (code (.inr 5)).length) + 6) := by
  apply Spec.runs
  vcgen [endFormula_spec code left output s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config
    simp_all

end Algolean.Algorithms.TMSATToSAT.Writing
