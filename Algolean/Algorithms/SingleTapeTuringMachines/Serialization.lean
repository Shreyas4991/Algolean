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
# Writing an input together with fixed words and polynomial-length parts

The machine replaces each input symbol with a fixed nonempty word. It leaves a chosen word
before the replaced input, another chosen word after it, and then the extra output parts.
Each extra part repeats a fixed word a polynomial number of times in the original input length.

The machine writes the extra parts first, while the original input remains available for
counting. It then works through the input from right to left and writes the word that must
appear at the start. The head finishes at the first symbol of the completed output.

All words, polynomials, and symbol comparisons are fixed when constructing the machine. One
finite program handles every input length and uses only the original tape alphabet and blanks.
The stored time polynomial is a constant times the square of the input length plus `fieldsWork`
plus one. Each bound polynomial is evaluated at the original input length.
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
private theorem encodingTime_le (W : Nat) (header ending : List Symbol) (n : Nat) :
    (encodingTime W header ending).eval n ≤
      (encodingTime W header ending).eval 1 * (n + 1) ^ 2 := by
  let a := 4 * W * (W + 1)
  let b := 3 + 4 * ending.length + 4 * W * ending.length + 4 * W
  let c := 4 * ending.length + header.length + 3
  have heq (x : Nat) : (encodingTime W header ending).eval x = a * x ^ 2 + b * x + c := by
    simp only [encodingTime, eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
    dsimp only [a, b, c]
    ring
  rw [heq n, heq 1]
  simp only [one_pow, Nat.mul_one]
  have hsquare : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by lia) 2
  have hlinear : n ≤ (n + 1) ^ 2 := by
    have h := Nat.le_mul_of_pos_right (n + 1) (show 0 < n + 1 by lia)
    rw [pow_two]
    lia
  have hconstant := Nat.mul_le_mul_left c (show 1 ≤ (n + 1) ^ 2 from Nat.pow_pos (by lia))
  simp only [Nat.mul_one] at hconstant
  calc
    a * n ^ 2 + b * n + c ≤
        a * (n + 1) ^ 2 + b * (n + 1) ^ 2 + c * (n + 1) ^ 2 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hsquare)
        (Nat.mul_le_mul_left b hlinear)) hconstant
    _ = (a + b + c) * (n + 1) ^ 2 := by ring

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
This machine leaves `header`, the replaced input, `ending`, and the extra output parts in that
order. Every input symbol must have a nonempty replacement word, and `symbols` must contain
every alphabet symbol. The head finishes at the first output symbol.

The containing machine fixes all words, polynomials, and comparisons once. The machine reads
the input from its tape and counts its length there. It uses the same finite program on every
input length.
-/
noncomputable def serialize (tm : SingleTapeTM Symbol) (symbols : List Symbol)
    (code : Symbol → List Symbol) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) : Prog (TMQuery tm) Unit := do [TMQuery tm]
  writeFields tm symbols fields
  finishEncoding symbols code header ending

/-- This constant depends only on the fixed output words, polynomials, and symbol replacements. -/
noncomputable def serializerTimeFactor (code : Symbol → List Symbol)
    (header ending : List Symbol) (fields : List (List Symbol × Polynomial Nat)) : Nat :=
  fieldsTimeFactor fields + (encodingTime (∑ symbol : Symbol, (code symbol).length)
    header ending).eval 1

/--
This constructs a machine with a proved polynomial time bound for writing the specified output.
The function `code` assigns a fixed nonempty word to each alphabet symbol. The machine contains
one fixed case for each symbol; tape tests select the case during execution. It works on every
input, including the empty word. All words and polynomials are fixed when constructing it.
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
  let time := C (serializerTimeFactor code header ending fields) *
    (X + fieldsWork fields + 1) ^ 2
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
  have hencoding := encodingTime_le W header ending
    (input.length + (fieldsWord fields input.length).length)
  have hsize := fieldsSize_le_fieldsWork fields input.length
  have hlast' : lastMoves ≤ (encodingTime W header ending).eval 1 *
      (input.length + (fieldsWork fields).eval input.length + 1) ^ 2 := by
    apply (hlast.trans hencoding).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simpa using Nat.add_le_add_right (Nat.add_le_add_left hsize input.length) 1
  have hsum := Nat.add_le_add hb hlast'
  rw [htime, hm]
  simpa [time, serializerTimeFactor, W, Nat.add_mul] using hsum

private theorem serializerComputer_poly_impl (code : Symbol → List Symbol)
    (hne : ∀ symbol, code symbol ≠ []) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) :
    (serializerComputer code hne header ending fields).poly =
      C (serializerTimeFactor code header ending fields) * (X + fieldsWork fields + 1) ^ 2 := rfl


/--
The stored polynomial is quadratic in the input length plus the requested writing work.
The constant depends only on the chosen words, polynomials, and symbol replacements.
-/
theorem serializerComputer_poly (code : Symbol → List Symbol)
    (hne : ∀ symbol, code symbol ≠ []) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) :
    (serializerComputer code hne header ending fields).poly =
      C (serializerTimeFactor code header ending fields) * (X + fieldsWork fields + 1) ^ 2 :=
  serializerComputer_poly_impl code hne header ending fields

end Algolean.Algorithms.SingleTapeTuringMachines
