/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.SymbolEncoding
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.PolynomialFields
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
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

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

private theorem finishEncoding_spec (symbols : List Symbol) (code : Symbol → List Symbol)
    (header ending : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (hne : ∀ symbol, code symbol ≠ []) (W : Nat) (hW : ∀ symbol, (code symbol).length ≤ W)
    (input suffix : List Symbol) (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, segment StackTape.nil input (StackTape.mapSome suffix)⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finishEncoding (tm := tm) symbols code header ending
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.mk₁ (header ++ input.flatMap code ++ ending ++ suffix)⟩ ∧
        final.headPos = origin + 1 - header.length ∧
        cost.steps ≤ elapsed +
          (encodingTime W header ending).eval (input.length + suffix.length) ⦄ := by
  let output := input.flatMap code ++ ending ++ suffix
  have htime : input.length + ending.length * (4 * suffix.length + 3) + ending.length + 1 +
      input.length * (W * (4 * output.length + 3) + W + 2) + 1 + header.length + 1 ≤
        (encodingTime W header ending).eval (input.length + suffix.length) := by
    have hn : input.length ≤ input.length + suffix.length := by lia
    have hsuf : suffix.length ≤ input.length + suffix.length := by lia
    have hout : output.length ≤ W * (input.length + suffix.length) + ending.length +
        (input.length + suffix.length) := by
      have hcodes := length_codes_le code W hW input
      have hmul := Nat.mul_le_mul_left W hn
      simp only [output, List.length_append]
      lia
    have hloop : input.length * (W * (4 * output.length + 3) + W + 2) ≤
        (input.length + suffix.length) *
          (W * (4 * (W * (input.length + suffix.length) + ending.length +
            (input.length + suffix.length)) + 3) + W + 2) := by gcongr
    have hend : ending.length * (4 * suffix.length + 3) ≤
        ending.length * (4 * (input.length + suffix.length) + 3) := by gcongr
    simp only [encodingTime, eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
    lia
  unfold finishEncoding
  iterate 3 rw [← bind_assoc]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config = ⟨label,
    (segment (StackTape.cons none (StackTape.mapSome output)) [] StackTape.nil).mirror⟩ ∧
    current.headPos = origin - 1 ∧ cost.steps ≤ elapsed + input.length +
      ending.length * (4 * suffix.length + 3) + ending.length + 1 +
        input.length * (W * (4 * output.length + 3) + W + 2))
  · apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hsteps⟩
    vcgen [seekRightBlank_segment_spec StackTape.nil (StackTape.mapSome suffix) input
        label origin initial.steps,
      insertAfterBlank_spec symbols ending hcover (StackTape.mapSome input.reverse) suffix
        label (origin + input.length) (initial.steps + input.length),
      encodeLeft_spec symbols code hcover hne W hW input.reverse (ending ++ suffix) output.length
        (by simp [output, List.append_assoc]) label (origin + input.length - 1)
        (initial.steps + input.length +
          ending.length * (4 * suffix.length + 3) + ending.length + 1)]
    all_goals cases hx : input.reverse
    all_goals simp_all [output, TMState.move, TMState.moveCost,
      BiTape.segment, BiTape.mirror, BiTape.moveLeft, List.append_assoc]
    all_goals lia
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hsteps⟩
    vcgen [writeLeft_spec header.reverse StackTape.nil (StackTape.mapSome output)
      label origin (initial.steps + 1)]
    all_goals simp_all [TMState.move, TMState.moveCost, output, List.append_assoc,
      BiTape.segment, BiTape.mirror, BiTape.moveRight]
    all_goals cases hx : header ++ (input.flatMap code ++ (ending ++ suffix))
    all_goals simp_all [BiTape.mk₁]
    all_goals lia

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
Serialization writes the chosen output, preserves the control state, and finishes on the first
output cell. Its time bound uses the original input length and the total writing work.
-/
@[spec] theorem serialize_spec (symbols : List Symbol) (hcover : ∀ symbol, symbol ∈ symbols)
    (code : Symbol → List Symbol) (hne : ∀ symbol, code symbol ≠ []) (header ending : List Symbol)
    (fields : List (List Symbol × Polynomial Nat)) (input : List Symbol)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.mk₁ input⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      serialize tm symbols code header ending fields
    ⦃ fun _ cost final => final.config = ⟨label, BiTape.mk₁
        (header ++ input.flatMap code ++ ending ++ fieldsWord fields input.length)⟩ ∧
        final.headPos = origin + 1 - header.length ∧ cost.steps ≤ elapsed +
          serializerTimeFactor code header ending fields *
            (input.length + (fieldsWork fields).eval input.length + 1) ^ 2 ⦄ := by
  classical
  let W := ∑ symbol : Symbol, (code symbol).length
  have hW : ∀ symbol, (code symbol).length ≤ W := by
    intro symbol
    exact Finset.single_le_sum (fun s _ => Nat.zero_le ((code s).length))
      (Finset.mem_univ symbol)
  have hencoding := encodingTime_le W header ending
    (input.length + (fieldsWord fields input.length).length)
  have hsize := fieldsSize_le_fieldsWork fields input.length
  have hlast : (encodingTime W header ending).eval
      (input.length + (fieldsWord fields input.length).length) ≤
        (encodingTime W header ending).eval 1 *
          (input.length + (fieldsWork fields).eval input.length + 1) ^ 2 := by
    apply hencoding.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_fieldsWord]
    lia
  vcgen [serialize, writeFields_spec symbols hcover fields input [] label origin elapsed,
    finishEncoding_spec symbols code header ending hcover hne W hW input
      (fieldsWord fields input.length) label origin
      (elapsed + fieldsTimeFactor fields *
        (input.length + (fieldsWork fields).eval input.length + 1) ^ 2)]
  all_goals simp_all [serializerTimeFactor, W, Nat.add_mul]
  all_goals lia

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
  let time := C (serializerTimeFactor code header ending fields) *
    (X + fieldsWork fields + 1) ^ 2
  refine {
    tm := control
    program := serialize control symbols code header ending fields
    timeBound := fun n => time.eval n
    poly := time
    bounds := fun _ => le_rfl
    computesWithin := ?_ }
  apply TMQuery.ComputesWithin.of_outputsWithinTime
  intro input
  obtain ⟨cost, final, hc, hf, _, hb⟩ :
      ∃ cost final, Completes (serialize control symbols code header ending fields)
        (TMState.init control input) cost final ∧
        final.config = ⟨some (), BiTape.mk₁
          (header ++ input.flatMap code ++ ending ++ fieldsWord fields input.length)⟩ ∧
        final.headPos = 1 - (header.length : ℤ) ∧
        cost.steps ≤ serializerTimeFactor code header ending fields *
          (input.length + (fieldsWork fields).eval input.length + 1) ^ 2 := by
    apply Spec.completes
    vcgen [serialize_spec (tm := control) symbols hcover code hne header ending fields input
      (some ()) 0 0]
    all_goals simp_all [TMState.init]
  apply hc.outputsWithinTime (by simpa using congrArg SingleTapeTM.Cfg.BiTape hf)
  simpa [time] using hb

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
