/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SymbolEncoding
public import Algolean.Algorithms.SingleTapeTuringMachines.PolynomialFields
public import Mathlib.Tactic.GCongr

/-!
# Serializing an input with fixed and polynomially sized fields

The machine first writes fields whose lengths are polynomials in the input length. It inserts
the fixed input ending before those fields, encodes the input from right to left, and writes
the fixed header.
The final tape contains exactly the serialized word, with the head at its first symbol.

All symbol codes, words, polynomials, and alphabet comparisons are fixed when constructing the
machine. One finite program handles every input length. The serializer uses only its original
finite tape alphabet and blank cells.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib Cslib.Turing TMQuery Copying Polynomial PolynomialWriter
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq tm.State]

private def finishEncoding (symbols : List Symbol) (code : Symbol → List Symbol)
    (header ending : List Symbol) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  seekRightBlank tm
  insertAfterBlank tm symbols ending
  moveₜ .Left
  encodeLeft tm symbols code
  moveₜ .Right
  writeLeft tm header.reverse
  moveₜ .Right

private noncomputable def encodingTime (W : Nat) (header ending : List Symbol) : Polynomial Nat :=
  X + C ending.length * (4 * X + 3) + C ending.length + 1 +
    X * (C W * (4 * (C W * X + C ending.length + X) + 3) + C W + 2) +
      1 + C header.length + 1

omit [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol] in
private theorem length_codes_le (code : Symbol → List Symbol) (W : Nat)
    (hW : ∀ symbol, (code symbol).length ≤ W) (input : List Symbol) :
    (input.flatMap code).length ≤ W * input.length := by
  induction input with
  | nil => simp
  | cons symbol input ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := hW symbol
    lia

private theorem finishEncoding_correct (symbols : List Symbol) (code : Symbol → List Symbol)
    (header ending : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (hne : ∀ symbol, code symbol ≠ []) (W : Nat) (hW : ∀ symbol, (code symbol).length ≤ W)
    (input suffix : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = segment StackTape.nil input (StackTape.mapSome suffix)) :
    ∃ moves, Runs (finishEncoding (tm := tm) symbols code header ending) s
      (BiTape.mk₁ (header ++ input.flatMap code ++ ending ++ suffix))
      (s.headPos + 1 - header.length) moves ∧
      moves ≤ (encodingTime W header ending).eval (input.length + suffix.length) := by
  have hr := seekRightBlank_segment StackTape.nil input (StackTape.mapSome suffix) s hs
  have hi := hr.seq (q := insertAfterBlank tm symbols ending)
    (second := segment (StackTape.mapSome input.reverse) [] (StackTape.mapSome (ending ++ suffix)))
    (pos₂ := s.headPos + input.length)
    (time₂ := ending.length * (4 * suffix.length + 3) + ending.length) (by
      intro middle ht hp
      simpa [hp] using insertAfterBlank_correct symbols ending hcover
        (StackTape.mapSome input.reverse) suffix middle
        (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht))
  have hm := hi.append_move .Left
  obtain ⟨cost, middle, hc, ht, hp, hmoves⟩ := hm
  have htape : middle.config.BiTape =
      (segment (StackTape.cons none (StackTape.mapSome (ending ++ suffix)))
        input.reverse StackTape.nil).mirror := by
    have h := congrArg SingleTapeTM.Cfg.BiTape ht
    cases hx : input.reverse <;>
      simpa [hx, Copying.segment, BiTape.segment, BiTape.mirror, BiTape.moveLeft] using h
  let output := input.flatMap code ++ ending ++ suffix
  obtain ⟨loopMoves, hl, hb⟩ := encodeLeft_correct symbols code hcover hne W hW
    input.reverse (ending ++ suffix) output.length middle htape
    (by simp [output, List.append_assoc])
  have hjoin := hl.prepend hc (by simp [ht])
  have hgap := hjoin.append_move .Right
  have hw := hgap.seq (q := writeLeft tm header.reverse)
    (second := segment StackTape.nil [] (StackTape.mapSome (header ++ output)))
    (pos₂ := s.headPos - header.length) (time₂ := header.length) (by
      intro next hcfg hpos
      have htape' : next.config.BiTape = segment StackTape.nil [] (StackTape.mapSome output) := by
        simpa [output, List.append_assoc, Copying.segment, BiTape.segment, BiTape.mirror,
          BiTape.moveRight] using congrArg SingleTapeTM.Cfg.BiTape hcfg
      convert writeLeft_correct header.reverse StackTape.nil (StackTape.mapSome output) next
        (by simpa using htape') using 1 <;>
        simp [hpos, hp, output, sub_eq_add_neg, add_assoc, add_comm, add_left_comm])
  have hf := hw.append_move .Right
  refine ⟨cost.steps + loopMoves + 1 + header.length + 1, ?_, ?_⟩
  · convert hf using 1
    · simp [finishEncoding, bind_assoc]
    · have heq : header ++ input.flatMap code ++ ending ++ suffix = header ++ output := by
        simp [output, List.append_assoc]
      rw [heq]
      generalize header ++ output = word
      cases word <;> rfl
    · simp [sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · have hn : input.length ≤ input.length + suffix.length := by lia
    have hsuf : suffix.length ≤ input.length + suffix.length := by lia
    have hout : output.length ≤ W * (input.length + suffix.length) + ending.length +
        (input.length + suffix.length) := by
      have hcodes := length_codes_le code W hW input
      have hmul := Nat.mul_le_mul_left W hn
      simp only [output, List.length_append]
      lia
    have hloop := hb.trans (show input.reverse.length *
        (W * (4 * output.length + 3) + W + 2) ≤
          (input.length + suffix.length) *
            (W * (4 * (W * (input.length + suffix.length) + ending.length +
              (input.length + suffix.length)) + 3) + W + 2) by
        simp only [List.length_reverse]
        gcongr)
    have hend : ending.length * (4 * suffix.length + 3) ≤
        ending.length * (4 * (input.length + suffix.length) + 3) := by gcongr
    simp only [encodingTime, eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
    lia

/--
This machine template serializes the input as a fixed header, the input symbol codes, a fixed
ending, and polynomially sized fields. The containing machine fixes all these parameters once.
Neither the input nor its length is a program parameter; one finite program reads every input
from the tape and computes the field lengths there.
-/
noncomputable def serialize (tm : SingleTapeTM Symbol) (symbols : List Symbol)
    (code : Symbol → List Symbol) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeFields tm symbols fields
  finishEncoding symbols code header ending

/--
The specified serialization is computable in polynomial time over the same finite alphabet.
All input symbols must have a nonempty code. The resulting machine is fixed for the chosen
format and works on every input, including the empty word.
-/
noncomputable def serializerComputer (code : Symbol → List Symbol)
    (hne : ∀ symbol, code symbol ≠ []) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) :
    PolyTimeComputable (fun input => header ++ input.flatMap code ++ ending ++
      fieldsWord fields input.length) := by
  classical
  let control : SingleTapeTM Symbol := {
    State := Unit
    q₀ := ()
    tr := fun _ symbol => (⟨symbol, none⟩, none) }
  let symbols := (Finset.univ : Finset Symbol).toList
  have hcover : ∀ symbol, symbol ∈ symbols := by simp [symbols]
  let W := ∑ symbol : Symbol, (code symbol).length
  have hW : ∀ symbol, (code symbol).length ≤ W := by
    intro symbol
    exact Finset.single_le_sum (fun s _ => Nat.zero_le ((code s).length))
      (Finset.mem_univ symbol)
  let time := fieldsTime fields + (encodingTime W header ending).comp (X + fieldsSize fields)
  refine {
    tm := control
    program := serialize control symbols code header ending fields
    timeBound := fun n => time.eval n
    poly := time
    bounds := fun _ => le_rfl
    outputsFunInTime := ?_ }
  intro input
  obtain ⟨firstMoves, hf, hb⟩ := writeFields_correct (tm := control) symbols hcover fields input []
    (TMState.init control input) (by rw [mapSome_nil]; exact (BiTape.segment_start input).symm)
  obtain ⟨cost, middle, hc, ht, hp, hm⟩ := hf
  obtain ⟨lastMoves, hl, hlast⟩ := finishEncoding_correct symbols code header ending hcover hne W hW
    input (fieldsWord fields input.length) middle
    (by simpa using congrArg SingleTapeTM.Cfg.BiTape ht)
  obtain ⟨total, final, hcomplete, htape, _, htime⟩ := hl.prepend hc (by simp [ht])
  apply hcomplete.outputsWithinTime (by simpa using congrArg SingleTapeTM.Cfg.BiTape htape)
  have hsum := Nat.add_le_add hb hlast
  rw [htime, hm]
  simpa [time, eval_comp] using hsum

end Algolean.Algorithms.SingleTapeTuringMachines
