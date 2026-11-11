/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.WordCopying
public import Algolean.Complexity.Reductions.TMSATToSAT.VariableNames

/-!
# Writing computation variable names from fields on the tape

* `writeName` reads three binary words: a time, a position, and a symbol or state number.
  A blank separates each word from the next. The output follows the third word.
* Certificate names use the position and symbol. Tape and head names also use the time.
  The program adds the kind bits and length headers required by `Variable.name`.
* Each output bit may be replaced by a fixed word. This allows writing either ordinary binary
  names or their representations within the SAT encoding over the chosen alphabet.
* The source words, earlier output, and cells farther left are preserved. The head returns
  to the beginning of the time word, including when that word is empty.

These are machine templates. The containing machine fixes the variable kind, digit symbols,
and output representations. The numbers themselves are read from the tape. When writing a
particular variable's name, its fields must contain the binary words chosen by the number
encoding; the program copies those words without changing their representation.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Naming

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Computability Problems
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable {tm : SingleTapeTM Γ} [DecidableEq tm.State]

/-- These are the three kinds of variables used to describe a bounded computation. -/
inductive Kind where
  /-- This chooses one certificate symbol. -/
  | certificate
  /-- This describes one tape cell at one time. -/
  | tape
  /-- This describes the head position and state at one time. -/
  | head
deriving DecidableEq

private def kindBits : Kind → List Bool
  | .certificate => [false]
  | .tape => [true, false]
  | .head => [true, true]

/-- This gives the binary name obtained from the three words, ignoring time for certificates. -/
@[expose] def bits (kind : Kind) (time position value : List Bool) : List Bool :=
  match kind with
  | .certificate => false :: BooleanTapeEncoding.pair position value
  | .tape => true :: false ::
    BooleanTapeEncoding.pair time (BooleanTapeEncoding.pair position value)
  | .head => true :: true ::
    BooleanTapeEncoding.pair time (BooleanTapeEncoding.pair position value)

/-- This describes the three source words, their separating blanks, and the existing output. -/
@[expose] def layout (zero one : Γ) (left : StackTape Γ)
    (time position value : List Bool) (output : List Γ) : BiTape Γ :=
  BiTape.segment (StackTape.cons none left) (time.map (fun bit => if bit then one else zero))
    (StackTape.separateWords
      [position.map (fun bit => if bit then one else zero),
        value.map (fun bit => if bit then one else zero)] (StackTape.mapSome output))

/-- This states the tape contents, control state, and head coordinate for a name writer. -/
@[expose] def AtFields (zero one : Γ) (left : StackTape Γ)
    (time position value : List Bool) (output : List Γ) (label : Option tm.State)
    (origin : ℤ) (current : TMState tm) : Prop :=
  current.config = ⟨label, layout zero one left time position value output⟩ ∧
    current.headPos = origin

private def pairMoves (width size distance output : Nat) : Nat :=
  lengthHeaderMoves width size distance output +
    copyBitsMoves width size distance (output + width * (size + 1))

private def writePairPart (zero one : Γ) (code : Bool → List Γ) (count : Nat) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendLengthHeader tm zero one code count
  copyBitsAcross tm zero one code count

private theorem writePairPart_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (input : List Bool) (parts : List (List Γ)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (input.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts (StackTape.mapSome output))⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writePairPart (tm := tm) zero one code parts.length
    ⦃ fun _ cost final => final.config = ⟨label,
        BiTape.segment (StackTape.cons none left)
          (input.map (fun bit => if bit then one else zero))
          (StackTape.separateWords parts
            (StackTape.mapSome (output ++ (BooleanTapeEncoding.pair input []).flatMap code)))⟩ ∧
        final.headPos = origin ∧
        cost.steps = elapsed + pairMoves width input.length (regionSpan parts) output.length ⦄ := by
  have hlength : ((List.replicate input.length true ++ [false]).flatMap code).length =
      width * (input.length + 1) := by
    simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm, Nat.mul_add]
  vcgen [writePairPart,
    appendLengthHeader_spec zero one hne code width hwidth input parts output left
      label origin elapsed,
    copyBitsAcross_spec zero one hne code width hwidth input parts
      (output ++ (List.replicate input.length true ++ [false]).flatMap code) left label origin
      (elapsed + lengthHeaderMoves width input.length (regionSpan parts) output.length)]
  all_goals
    simp_all [pairMoves, BooleanTapeEncoding.pair, List.append_assoc]
    all_goals ring_nf at *

private def fieldBits (first : List Bool) : List (List Bool) → List Bool
  | [] => first
  | next :: rest => BooleanTapeEncoding.pair first (fieldBits next rest)

private def fieldMoves (width first : Nat) : List Nat → Nat → Nat
  | [], output => copyBitsMoves width first 0 output
  | next :: rest, output =>
    pairMoves width first ((next :: rest).sum + (next :: rest).length) output +
      2 * first + 4 + fieldMoves width next rest (output + width * (2 * first + 1))

private def fieldsTape (zero one : Γ) (left : StackTape Γ) (first : List Bool)
    (rest : List (List Bool)) (output : List Γ) : BiTape Γ :=
  BiTape.segment (StackTape.cons none left) (first.map (fun bit => if bit then one else zero))
    (StackTape.separateWords (rest.map fun word => word.map (fun bit => if bit then one else zero))
      (StackTape.mapSome output))

private def writeFields (zero one : Γ) (code : Bool → List Γ) : Nat → Prog (TMQuery tm) Unit
  | 0 => copyBitsAcross tm zero one code 0
  | count + 1 => do [TMQuery tm]
    writePairPart zero one code (count + 1)
    nextRegion tm
    writeFields zero one code count
    previousRegion tm

private theorem writeFields_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (first : List Bool) (rest : List (List Bool)) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, fieldsTape zero one left first rest output⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      writeFields (tm := tm) zero one code rest.length
    ⦃ fun _ cost final => final.config = ⟨label,
        fieldsTape zero one left first rest (output ++ (fieldBits first rest).flatMap code)⟩ ∧
        final.headPos = origin ∧ cost.steps =
          elapsed + fieldMoves width first.length (rest.map List.length) output.length ⦄ := by
  induction rest generalizing first output left origin elapsed with
  | nil =>
    simp only [List.length_nil, writeFields]
    have hc := copyBitsAcross_spec (tm := tm) zero one hne code width hwidth first [] output
      left label origin elapsed
    simp only [List.length_nil] at hc
    vcgen [hc]
    all_goals simp_all [fieldsTape, fieldBits, fieldMoves, regionSpan]
  | cons next rest ih =>
    let digit : Bool → Γ := fun bit => if bit then one else zero
    let later := (next :: rest).map fun word => word.map digit
    let written := output ++ (BooleanTapeEncoding.pair first []).flatMap code
    let step := pairMoves width first.length (regionSpan later) output.length
    have hlength : ((BooleanTapeEncoding.pair first []).flatMap code).length =
        width * (2 * first.length + 1) := by
      simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
    have hpart := writePairPart_spec (tm := tm) zero one hne code width hwidth
      first later output left label origin elapsed
    simp only [later, List.map_cons, List.length_cons, List.length_map] at hpart
    simp only [List.length_cons, writeFields]
    vcgen [hpart,
      nextRegion_spec (StackTape.cons none left) (first.map digit) (next.map digit)
        (StackTape.separateWords (rest.map fun word => word.map digit) (StackTape.mapSome written))
        label origin (elapsed + step),
      ih next written (StackTape.prepend (first.map digit).reverse (StackTape.cons none left))
        (origin + (first.length + 1 : Nat)) (elapsed + step + first.length + 1),
      previousRegion_spec left (first.map digit) (next.map digit)
        (StackTape.separateWords (rest.map fun word => word.map digit)
          (StackTape.mapSome (written ++ (fieldBits next rest).flatMap code)))
        label (origin + (first.length + 1 : Nat))
        (elapsed + step + first.length + 1 +
          fieldMoves width next.length (rest.map List.length) written.length)]
    all_goals
      simp_all [fieldsTape, fieldBits, fieldMoves, BooleanTapeEncoding.pair,
        digit, later, written, step, regionSpan, List.append_assoc, List.map_map, Function.comp_def]
      all_goals ring_nf at *

private def bodyBits (kind : Kind) (time position value : List Bool) : List Bool :=
  match kind with
  | .certificate => BooleanTapeEncoding.pair position value
  | .tape | .head => BooleanTapeEncoding.pair time (BooleanTapeEncoding.pair position value)

private theorem bits_eq (kind : Kind) (time position value : List Bool) :
    bits kind time position value = kindBits kind ++ bodyBits kind time position value := by
  cases kind <;> rfl

private def writeBody (zero one : Γ) (code : Bool → List Γ) : Kind → Prog (TMQuery tm) Unit
  | .certificate => do [TMQuery tm]
    nextRegion tm
    writeFields zero one code 1
    previousRegion tm
  | .tape | .head => writeFields zero one code 2

private def bodyMoves (kind : Kind) (width time position value output : Nat) : Nat :=
  match kind with
  | .certificate => 2 * time + 4 + fieldMoves width position [value] output
  | .tape | .head => fieldMoves width time [position, value] output

private theorem writeBody_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (kind : Kind) (time position value : List Bool) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtFields zero one left time position value output label origin current ∧
        cost.steps = elapsed ⦄
      writeBody (tm := tm) zero one code kind
    ⦃ fun _ cost final =>
        AtFields zero one left time position value
          (output ++ (bodyBits kind time position value).flatMap code) label origin final ∧
        cost.steps = elapsed + bodyMoves kind width time.length position.length
          value.length output.length ⦄ := by
  let digit : Bool → Γ := fun bit => if bit then one else zero
  have htwo := writeFields_spec (tm := tm) zero one hne code width hwidth position [value] output
    (StackTape.prepend (time.map digit).reverse (StackTape.cons none left))
    label (origin + (time.length + 1 : Nat)) (elapsed + time.length + 1)
  have hthree := writeFields_spec (tm := tm) zero one hne code width hwidth
    time [position, value] output left label origin elapsed
  norm_num only [List.length_cons, List.length_nil] at htwo hthree
  cases kind <;> unfold writeBody <;>
    vcgen [htwo, hthree,
      nextRegion_spec (StackTape.cons none left) (time.map digit) (position.map digit)
        (StackTape.separateWords [value.map digit] (StackTape.mapSome output))
        label origin elapsed,
      previousRegion_spec left (time.map digit) (position.map digit)
        (StackTape.separateWords [value.map digit]
          (StackTape.mapSome (output ++ (fieldBits position [value]).flatMap code)))
        label (origin + (time.length + 1 : Nat))
        (elapsed + time.length + 1 +
          fieldMoves width position.length [value.length] output.length)]
  all_goals
    simp_all [AtFields, layout, fieldsTape, bodyBits, bodyMoves, digit, fieldBits]
    all_goals lia

/--
This machine template appends a variable name using the three words on the tape. It chooses
the certificate, tape, or head format once through `kind`. It reads every binary field from
the tape and restores all three fields and the starting head position.
-/
def writeName (tm : SingleTapeTM Γ) (zero one : Γ) (code : Bool → List Γ) (kind : Kind) :
    Prog (TMQuery tm) Unit := do [TMQuery tm]
  appendFromRegion tm ((kindBits kind).flatMap code) 2
  writeBody zero one code kind

/-- This counts every head move made while adding the kind bits, headers, and copied fields. -/
def moves (kind : Kind) (width time position value output : Nat) : Nat :=
  let kindLength := width * (kindBits kind).length
  2 * (time + position + value + 2 + output + kindLength) + 12 +
    bodyMoves kind width time position value (output + kindLength)

/--
The writer appends exactly the chosen representation of the variable name. It preserves the
three fields, previous output, control state, and head coordinate. The cost is the exact number
of moves given by `moves`; the specification also covers empty binary fields.
-/
@[spec] theorem writeName_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (kind : Kind) (time position value : List Bool) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => AtFields zero one left time position value output label origin current ∧
        cost.steps = elapsed ⦄
      writeName tm zero one code kind
    ⦃ fun _ cost final =>
        AtFields zero one left time position value
          (output ++ (bits kind time position value).flatMap code) label origin final ∧
        cost.steps = elapsed + moves kind width time.length position.length
          value.length output.length ⦄ := by
  let clock := elapsed + 2 * (time.length + position.length + value.length + 2 +
    output.length + width * (kindBits kind).length) + 12
  have hlength : ((kindBits kind).flatMap code).length = width * (kindBits kind).length := by
    simp [List.length_flatMap, hwidth, List.sum_replicate, Nat.mul_comm]
  have hstart := appendFromRegion_spec (tm := tm) ((kindBits kind).flatMap code)
    (time.map (fun bit => if bit then one else zero))
    [position.map (fun bit => if bit then one else zero),
      value.map (fun bit => if bit then one else zero)] output left label origin elapsed
  norm_num only [List.length_cons, List.length_nil] at hstart
  vcgen [writeName, hstart, writeBody_spec zero one hne code width hwidth kind
    time position value (output ++ (kindBits kind).flatMap code) left label origin clock]
  all_goals
    simp_all [AtFields, layout, bits_eq, moves, clock, regionSpan, List.append_assoc]
    all_goals lia

/-- The exact move count is quadratic in the source and previous output lengths. -/
theorem moves_le (kind : Kind) (width time position value output : Nat) :
    moves kind width time position value output ≤
      8 * (width + 1) * (time + position + value + output + 4) ^ 2 := by
  cases kind <;> simp only [moves, bodyMoves, kindBits, fieldMoves, pairMoves,
    lengthHeaderMoves, copyBitsMoves,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  all_goals
    ring_nf;
    lia

/-- The writer produces the stated name, preserves the source, and restores the head. -/
theorem writeName_correct (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (kind : Kind) (time position value : List Bool) (output : List Γ) (left : StackTape Γ)
    (s : TMState tm) (hs : s.config.BiTape = layout zero one left time position value output) :
    Runs (writeName tm zero one code kind) s
      (layout zero one left time position value
        (output ++ (bits kind time position value).flatMap code)) s.headPos
      (moves kind width time.length position.length value.length output.length) := by
  apply Spec.runs
  vcgen [writeName_spec zero one hne code width hwidth kind time position value output left
    s.config.state s.headPos 0]
  all_goals
    cases hcfg : s.config;
    simp_all [AtFields]

/--
The writer finishes within the stated quadratic bound and produces the same output as in
`writeName_correct`. The coefficient depends only on the fixed bit representation width.
-/
theorem writeName_time_bound (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (kind : Kind) (time position value : List Bool) (output : List Γ) (left : StackTape Γ)
    (s : TMState tm) (hs : s.config.BiTape = layout zero one left time position value output) :
    ∃ steps, Runs (writeName tm zero one code kind) s
      (layout zero one left time position value
        (output ++ (bits kind time position value).flatMap code)) s.headPos steps ∧
      steps ≤ 8 * (width + 1) *
        (time.length + position.length + value.length + output.length + 4) ^ 2 :=
  ⟨_, writeName_correct zero one hne code width hwidth kind time position value output left s hs,
    moves_le kind width time.length position.length value.length output.length⟩

/-- These are the three binary words read by the name writer and their fixed variable kind. -/
structure Fields where
  /-- This determines which kind bits and which fields the writer uses. -/
  kind : Kind
  /-- This is the encoded time, or the empty word for a certificate variable. -/
  time : List Bool
  /-- This is the encoded position in the certificate or recorded tape. -/
  position : List Bool
  /-- This is the encoded symbol or machine state. -/
  value : List Bool

variable {Δ : Type} [Encodable Δ] {problem : TMSAT.Instance Δ}

/-- This gives the separately encoded indices from which the machine writes a variable's name. -/
@[expose] def sourceFields : Variable problem → Fields
  | .certificate position symbol =>
    ⟨.certificate, [], encodingNatBool.encode position.val,
      encodingNatBool.encode (Encodable.encode symbol)⟩
  | .tape time position symbol =>
    ⟨.tape, encodingNatBool.encode time.val, encodingNatBool.encode position.val,
      encodingNatBool.encode (Encodable.encode symbol)⟩
  | .head time (position, controlState) =>
    ⟨.head, encodingNatBool.encode time.val, encodingNatBool.encode position.val,
      encodingNatBool.encode (Encodable.encode controlState)⟩

/-- The fields of a computation variable give exactly its existing binary name. -/
@[simp] theorem bits_sourceFields (entry : Variable problem) :
    let source := sourceFields entry
    bits source.kind source.time source.position source.value = Variable.name entry := by
  cases entry <;> rfl

/--
Reading a variable's separately encoded indices writes exactly `Variable.name`, with each bit
replaced by its chosen representation. The variable and its indices occur only in this
specification. The program reads those indices from the tape.
-/
theorem writeVariable_spec (zero one : Γ) (hne : zero ≠ one)
    (code : Bool → List Γ) (width : Nat) (hwidth : ∀ bit, (code bit).length = width)
    (entry : Variable problem) (output : List Γ) (left : StackTape Γ)
    (label : Option tm.State) (origin : ℤ) (elapsed : Nat) :
    let source := sourceFields entry
    ⦃ fun cost current =>
        AtFields zero one left source.time source.position source.value output
          label origin current ∧
        cost.steps = elapsed ⦄
      writeName tm zero one code source.kind
    ⦃ fun _ cost final =>
        AtFields zero one left source.time source.position source.value
          (output ++ (Variable.name entry).flatMap code) label origin final ∧
        cost.steps = elapsed + moves source.kind width source.time.length source.position.length
          source.value.length output.length ⦄ := by
  simpa only [bits_sourceFields] using
    writeName_spec (tm := tm) zero one hne code width hwidth (sourceFields entry).kind
      (sourceFields entry).time (sourceFields entry).position (sourceFields entry).value
      output left label origin elapsed

end Algolean.Algorithms.TMSATToSAT.Naming
