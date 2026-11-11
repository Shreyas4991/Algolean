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
open scoped TMQuery

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

private theorem copyCell_correct (restore : Γ) (word : List Γ) (left : StackTape Γ)
    (rest output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left (restore :: rest)
      (StackTape.mapSome output)) :
    Runs (copyCell tm restore word) s
      (BiTape.segment (StackTape.cons (some restore) left) rest
        (StackTape.mapSome (output ++ word)))
      (s.headPos + 1) (2 * (rest.length + output.length + word.length) + 13) := by
  have he : Runs (do FreeM.lift (.write none); FreeM.lift (.move .Right)) s
      (BiTape.segment (StackTape.cons none left) rest (StackTape.mapSome output))
      (s.headPos + 1) 1 := by
    cases rest <;> simpa [htape, BiTape.segment, BiTape.write, BiTape.moveRight] using
      (write_correct s none).append_move .Right
  have hn := he.seq (q := nextRegion tm)
    (second := BiTape.segment
      (StackTape.cons none (StackTape.prepend rest.reverse (StackTape.cons none left)))
      output StackTape.nil)
    (pos₂ := s.headPos + (rest.length + 2 : Nat)) (time₂ := rest.length + 1) (by
      intro middle hm hp
      simpa [hp, StackTape.prepend_nil, add_assoc, add_comm, add_left_comm] using
        nextRegion_correct (StackTape.cons none left) rest output StackTape.nil middle
          (by simpa [StackTape.prepend_nil] using congrArg SingleTapeTM.Cfg.BiTape hm))
  have hw := hn.seq (q := appendWord tm none word)
    (second := BiTape.segment
      (StackTape.cons none (StackTape.prepend rest.reverse (StackTape.cons none left)))
      (output ++ word) StackTape.nil)
    (pos₂ := s.headPos + (rest.length + 2 : Nat))
    (time₂ := 2 * (output.length + word.length) + 6) (by
      intro middle hm hp
      simpa [hp] using appendWord_correct none
        (StackTape.prepend rest.reverse (StackTape.cons none left)) output word middle
        (congrArg SingleTapeTM.Cfg.BiTape hm))
  have hb := hw.seq (q := previousRegion tm)
    (second := BiTape.segment (StackTape.cons none left) rest
      (StackTape.mapSome (output ++ word)))
    (pos₂ := s.headPos + 1) (time₂ := rest.length + 3) (by
      intro middle hm hp
      simpa [hp, StackTape.prepend_nil, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        previousRegion_correct left rest (output ++ word) StackTape.nil middle
          (congrArg SingleTapeTM.Cfg.BiTape hm))
  have hf := ((hb.append_move .Left).append_write (some restore)).append_move .Right
  convert hf using 1
  · simp [copyCell, bind_assoc]
  · cases rest <;>
      simp [BiTape.segment, BiTape.moveLeft, BiTape.moveRight, BiTape.write]
  · simp
  · ring

private def copyName (tm : SingleTapeTM Γ) (zero one : Γ)
    (code : CodeSymbol → List Γ) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  whileₜ (notₜ tape =ₜ none) do
    ifₜ tape =ₜ some one then
      copyCell tm one (code (.inl true))
    else
      copyCell tm zero (code (.inl false))

private theorem copyName_correct (zero one : Γ) (hne : zero ≠ one)
    (code : CodeSymbol → List Γ) (width : Nat)
    (hwidth : ∀ symbol, (code symbol).length = width)
    (bits : List Bool) (left : StackTape Γ) (output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment left
      (bits.map (fun bit => if bit then one else zero)) (StackTape.mapSome output)) :
    Runs (copyName tm zero one code) s
      (BiTape.segment
        (StackTape.prepend (bits.map (fun bit => if bit then one else zero)).reverse left) []
        (StackTape.mapSome (output ++ bits.flatMap (fun bit => code (.inl bit)))))
      (s.headPos + bits.length)
      ((width + 1) * bits.length ^ 2 + 2 * bits.length * output.length +
        (width + 12) * bits.length) := by
  induction bits generalizing left output s with
  | nil => simp [copyName, htape]
  | cons bit bits ih =>
    let digit := if bit then one else zero
    have hfirst := copyCell_correct digit (code (.inl bit)) left
      (bits.map (fun value : Bool => if value then one else zero)) output s
      (by simpa [digit] using htape)
    have hbody : Runs
        (branch (.tapeIs (some one)) (copyCell tm one (code (.inl true)))
          (copyCell tm zero (code (.inl false)))) s
        (BiTape.segment (StackTape.cons (some digit) left)
          (bits.map (fun bit => if bit then one else zero))
          (StackTape.mapSome (output ++ code (.inl bit))))
        (s.headPos + 1) (2 * (bits.length + output.length + width) + 13) := by
      apply Runs.branch
      cases bit <;> simpa [htape, digit, hne, hwidth] using hfirst
    have hr := hbody.seq (q := copyName tm zero one code)
      (second := BiTape.segment
        (StackTape.prepend
          ((bit :: bits).map (fun bit => if bit then one else zero)).reverse left) []
        (StackTape.mapSome (output ++ (bit :: bits).flatMap (fun bit => code (.inl bit)))))
      (pos₂ := s.headPos + (bit :: bits).length)
      (time₂ := (width + 1) * bits.length ^ 2 +
        2 * bits.length * (output ++ code (.inl bit)).length + (width + 12) * bits.length) (by
        intro middle hm hp
        simpa [hp, digit, List.reverse_cons, StackTape.prepend_append, List.append_assoc,
          add_assoc, add_comm, add_left_comm] using
          ih (StackTape.cons (some digit) left) (output ++ code (.inl bit))
          middle (congrArg SingleTapeTM.Cfg.BiTape hm))
    unfold copyName
    apply runs_while_step (by cases bit <;> simp [htape])
    convert hr using 1
    · simp [copyName]
    · simp only [List.length_cons, List.length_append, hwidth]
      ring

private def returnSource (tm : SingleTapeTM Γ) (ending : List Γ) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  moveₜ .Right
  appendWord tm none ending
  previousRegion tm

private theorem returnSource_correct (ending : List Γ) (left : StackTape Γ)
    (input output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment
      (StackTape.prepend input.reverse (StackTape.cons none left)) []
      (StackTape.mapSome output)) :
    Runs (returnSource tm ending) s
      (BiTape.segment (StackTape.cons none left) input (StackTape.mapSome (output ++ ending)))
      (s.headPos - input.length) (2 * (output.length + ending.length) + input.length + 10) := by
  have hm : Runs (FreeM.lift (.move .Right)) s
      (BiTape.segment
        (StackTape.cons none (StackTape.prepend input.reverse (StackTape.cons none left)))
        output StackTape.nil) (s.headPos + 1) 1 := by
    cases output <;> simpa [htape, BiTape.segment, BiTape.moveRight] using move_correct s .Right
  have hw := hm.seq (q := appendWord tm none ending)
    (second := BiTape.segment
      (StackTape.cons none (StackTape.prepend input.reverse (StackTape.cons none left)))
      (output ++ ending) StackTape.nil)
    (pos₂ := s.headPos + 1) (time₂ := 2 * (output.length + ending.length) + 6) (by
      intro middle hh hp
      simpa [hp] using appendWord_correct none
        (StackTape.prepend input.reverse (StackTape.cons none left)) output ending middle
        (congrArg SingleTapeTM.Cfg.BiTape hh))
  have hr := hw.seq (q := previousRegion tm)
    (second := BiTape.segment (StackTape.cons none left) input
      (StackTape.mapSome (output ++ ending)))
    (pos₂ := s.headPos - input.length) (time₂ := input.length + 3) (by
      intro middle hh hp
      simpa [hp, StackTape.prepend_nil, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        previousRegion_correct left input (output ++ ending) StackTape.nil middle
          (congrArg SingleTapeTM.Cfg.BiTape hh))
  convert hr using 1
  · simp [returnSource]
  · lia

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
  let digit := if negative then one else zero
  let sign : CodeSymbol := .inr (if negative then 1 else 0)
  let source := digit :: name.map (fun bit => if bit then one else zero)
  have hfirst := copyCell_correct digit (code sign) (StackTape.cons none left)
    (name.map (fun bit : Bool => if bit then one else zero)) output s htape
  have hsign : Runs
      (branch (.tapeIs (some one)) (copyCell tm one (code (.inr 1)))
        (copyCell tm zero (code (.inr 0)))) s
      (BiTape.segment (StackTape.cons (some digit) (StackTape.cons none left))
        (name.map (fun bit => if bit then one else zero))
        (StackTape.mapSome (output ++ code sign)))
      (s.headPos + 1) (2 * (name.length + output.length + width) + 13) := by
    apply Runs.branch
    cases negative <;> simpa [htape, digit, sign, hne, hwidth] using hfirst
  have hn := hsign.seq (q := copyName tm zero one code)
    (second := BiTape.segment (StackTape.prepend source.reverse (StackTape.cons none left)) []
      (StackTape.mapSome (output ++ code sign ++ name.flatMap (fun bit => code (.inl bit)))))
    (pos₂ := s.headPos + (name.length + 1 : Nat))
    (time₂ := (width + 1) * name.length ^ 2 +
      2 * name.length * (output ++ code sign).length + (width + 12) * name.length) (by
      intro middle hm hp
      simpa [source, List.reverse_cons, StackTape.prepend_append, List.append_assoc,
        hp, add_assoc, add_comm, add_left_comm] using
        copyName_correct zero one hne code width hwidth name
          (StackTape.cons (some digit) (StackTape.cons none left)) (output ++ code sign)
          middle (congrArg SingleTapeTM.Cfg.BiTape hm))
  have hf := hn.seq (q := returnSource tm (code (.inr 2)))
    (second := BiTape.segment (StackTape.cons none left) source
      (StackTape.mapSome (output ++ code sign ++ name.flatMap (fun bit => code (.inl bit)) ++
        code (.inr 2))))
    (pos₂ := s.headPos)
    (time₂ := 2 * ((output ++ code sign ++ name.flatMap (fun bit => code (.inl bit))).length +
      width) + source.length + 10) (by
      intro middle hm hp
      simpa [hp, source, hwidth, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
        returnSource_correct (code (.inr 2)) left source
          (output ++ code sign ++ name.flatMap (fun bit => code (.inl bit))) middle
          (congrArg SingleTapeTM.Cfg.BiTape hm))
  have hlength : (name.flatMap (fun bit => code (.inl bit))).length = name.length * width := by
    simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  convert hf using 1
  · simp [appendLiteral, bind_assoc]
  · simp only [List.length_append, hwidth, hlength, source, List.length_cons, List.length_map]
    ring

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
  rw [hliteral, hword]
  simpa [appendLiteralOver, List.append_assoc, Nat.add_assoc] using
    appendLiteral_correct zero one hne
      (fun symbol => (finiteWordsOver CodeSymbol Γ).encode [symbol]) 8 hwidth
      negative name left output s htape

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
  simpa [endClause, List.append_assoc, Nat.add_assoc] using
    appendWord_correct none left output (code (.inr 3) ++ code (.inr 4)) s htape

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
/--
This proves that the program adds the formula ending, returns the head to the first output
cell, and leaves the machine state and cells farther left unchanged. It gives the exact move count.
-/
theorem endFormula_correct (code : CodeSymbol → List Γ) (left : StackTape Γ)
    (output : List Γ) (s : TMState tm)
    (htape : s.config.BiTape = BiTape.segment (StackTape.cons none left) output StackTape.nil) :
    Runs (endFormula tm code) s
      (BiTape.segment (StackTape.cons none left) (output ++ code (.inr 5)) StackTape.nil)
      s.headPos (2 * (output.length + (code (.inr 5)).length) + 6) :=
  appendWord_correct none left output (code (.inr 5)) s htape

end Algolean.Algorithms.TMSATToSAT.Writing
