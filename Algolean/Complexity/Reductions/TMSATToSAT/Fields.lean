/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.TMSATToSAT.Parsing
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Regions

/-!
# Reading numbers from a TMSAT description

* `readNumber` reads a binary number from the description into the counter to its left.
  It preserves the description and stops at the symbol that ends the number.
* `readNumber_spec` proves that the counter represents the decoded number. It also bounds
  its length and the number of head moves.

The counter stores its most significant digit first. An empty counter represents zero.
Mathlib's number decoder also accepts binary words ending in `false`. It reads these as
having an extra highest `true` bit. The reader writes that bit too, so the two agree.

The alphabet, the two counter digits, and the field ending are fixed with the program. The
number itself is read from the tape and does not select a different program.
-/

public section

namespace Algolean.Algorithms.TMSATToSAT.Fields

open Cslib Cslib.Turing TMQuery SingleTapeTuringMachines Copying Alphabet Problems.TMSAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ]

private noncomputable def code (symbol : CodeSymbol) : List Γ :=
  (finiteWordsOver CodeSymbol Γ).encode [symbol]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] in
private theorem code_length (symbol : CodeSymbol) : (code (Γ := Γ) symbol).length = 12 := by
  simp [code, CodeSymbol, PayloadSymbol, SingleTapeTM.Description.CodeSymbol,
    SingleTapeTM.Description.BodySymbol, SingleTapeTM.Description.TableSymbol,
    SingleTapeTM.Description.RowSymbol, SingleTapeTM.Description.TransitionSymbol,
    SingleTapeTM.Description.MovementSymbol, Extended]

private def view (counter crossed remaining : List Γ) (tail : StackTape Γ) : BiTape Γ :=
  BiTape.segment
    (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome counter.reverse)))
    remaining tail

private def prependBit (bit : Γ) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
    do [TMQuery (Parsing.machine (Γ := Γ))]
  moveₜ .Left
  tape ←ₜ some bit

omit [Nontrivial Γ] in
private theorem prependBit_spec (bit : Γ) (counter : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil counter tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      prependBit bit
    ⦃ fun _ cost final => final.config =
        ⟨label, BiTape.segment StackTape.nil (bit :: counter) tail⟩ ∧
        final.headPos = origin - 1 ∧ cost.steps ≤ elapsed + 1 ⦄ := by
  vcgen [prependBit]
  cases counter <;> simp_all [TMState.move, TMState.write, TMState.moveCost,
    BiTape.segment, BiTape.moveLeft, BiTape.write, sub_eq_add_neg]

private def visitCounter (restore bit : Γ) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  visitPreviousRegion (Parsing.machine (Γ := Γ)) restore (prependBit bit)

omit [Nontrivial Γ] in
private theorem visitCounter_spec (restore bit : Γ) (counter crossed suffix : List Γ)
    (tail : StackTape Γ) (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, view counter crossed (restore :: suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      visitCounter restore bit
    ⦃ fun _ cost final => final.config =
        ⟨label, view (bit :: counter) crossed (restore :: suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 8 ⦄ := by
  have ha (right : StackTape Γ) (position : ℤ) (spent : Nat) :
      ⦃ fun cost current => current.config = ⟨label, BiTape.segment StackTape.nil counter right⟩ ∧
          current.headPos = position ∧ cost.steps ≤ spent ⦄
        prependBit bit
      ⦃ fun _ cost final => final.config =
          ⟨label, BiTape.segment StackTape.nil (bit :: counter) right⟩ ∧
          final.headPos = position + counter.length - (bit :: counter).length ∧
          cost.steps ≤ spent + 1 ⦄ := by
    vcgen [prependBit_spec bit counter right label position spent]
    all_goals simp_all
    all_goals lia
  vcgen [visitCounter, visitPreviousRegion_spec restore (prependBit bit)
    counter (bit :: counter) crossed suffix tail 1 label label origin elapsed ha]
  all_goals simp_all [view]
  all_goals lia

private noncomputable def copyDigit (zero one : Γ) (bit : Bool) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  visitCounter ((code (CodeSymbol.digit bit)).headD zero) (if bit then one else zero)
  moveCells (Parsing.machine (Γ := Γ)) .Right 12

private theorem copyDigit_spec (zero one : Γ) (bit : Bool)
    (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code (CodeSymbol.digit bit) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      copyDigit zero one bit
    ⦃ fun _ cost final => final.config = ⟨label, view ((if bit then one else zero) :: counter)
        (crossed ++ code (CodeSymbol.digit bit)) suffix tail⟩ ∧
        final.headPos = origin + 12 ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 20 ⦄ := by
  obtain ⟨restore, rest, hcode⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos
      (by simp [code_length] : 0 < (code (Γ := Γ) (CodeSymbol.digit bit)).length))
  have hmove : BiTape.moveRight^[12]
      (view ((if bit then one else zero) :: counter) crossed
        (code (CodeSymbol.digit bit) ++ suffix) tail) =
      view ((if bit then one else zero) :: counter)
        (crossed ++ code (CodeSymbol.digit bit)) suffix tail := by
    rw [← code_length (Γ := Γ) (CodeSymbol.digit bit)]
    simp [view, BiTape.segment_moveRight_iterate, List.reverse_append, StackTape.prepend_append]
  unfold copyDigit
  simp only [hcode, List.headD_cons]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨label, view ((if bit then one else zero) :: counter) crossed
      (code (CodeSymbol.digit bit) ++ suffix) tail⟩ ∧
    current.headPos = origin ∧
    cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 8)
  · vcgen [visitCounter_spec restore (if bit then one else zero) counter crossed
      (rest ++ suffix) tail label origin elapsed]
    all_goals simp_all
  · intro _
    apply Std.WP.Triple.intro
    rintro initial current ⟨hcfg, hpos, hsteps⟩
    vcgen [moveCells_spec (tm := Parsing.machine (Γ := Γ)) .Right 12
      (view ((if bit then one else zero) :: counter) crossed
        (code (CodeSymbol.digit bit) ++ suffix) tail) label origin initial.steps]
    all_goals simp_all

private def lastStage : Option Bool → Parsing.Stage Γ
  | none => .header
  | some bit => .inputDigits 0 0 bit

omit [Inhabited Γ] [Nontrivial Γ] [DecidableEq Γ] in
private theorem lastStage_injective : Function.Injective (lastStage (Γ := Γ)) := by
  intro first second h
  cases first <;> cases second <;> simp_all [lastStage]

private theorem testCode_spec (expected actual : CodeSymbol) (last : Option Bool)
    (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code actual ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      checkPrefix (Parsing.machine (Γ := Γ)) (.inr (lastStage last, expected))
        (.inl (lastStage last)) (code expected)
    ⦃ fun _ cost final => final.config =
        ⟨some (if expected = actual then .inr (lastStage last, expected)
          else .inl (lastStage last)),
          view counter crossed (code actual ++ suffix) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed + 24 ⦄ := by
  have hp : code (Γ := Γ) expected <+: code actual ++ suffix ↔ expected = actual :=
    finiteWordsOver_symbol_prefix_iff expected actual suffix
  vcgen [checkPrefix_spec (tm := Parsing.machine (Γ := Γ))
    (.inr (lastStage last, expected)) (.inl (lastStage last))
    (code expected) (code actual ++ suffix)
    (StackTape.prepend crossed.reverse (StackTape.cons none (StackTape.mapSome counter.reverse)))
    tail label origin elapsed]
  all_goals simp_all [view, code_length]

private noncomputable def recordDigit (zero one : Γ) (bit : Bool) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  copyDigit zero one bit
  state ←ₜ .inl (lastStage (some bit))

private theorem recordDigit_spec (zero one : Γ) (bit : Bool)
    (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code (CodeSymbol.digit bit) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      recordDigit zero one bit
    ⦃ fun _ cost final => final.config = ⟨some (.inl (lastStage (some bit))),
        view ((if bit then one else zero) :: counter)
          (crossed ++ code (CodeSymbol.digit bit)) suffix tail⟩ ∧
        final.headPos = origin + 12 ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 20 ⦄ := by
  vcgen [recordDigit, copyDigit_spec zero one bit counter crossed suffix tail label origin elapsed]
  all_goals simp_all

private def finishedCounter (one : Γ) (last : Option Bool) (counter : List Γ) : List Γ :=
  if last = some false then one :: counter else counter

private noncomputable def finishNumber (zero one : Γ) (ending : CodeSymbol)
    (last : Option Bool) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
    do [TMQuery (Parsing.machine (Γ := Γ))]
  if last = some false then
    visitCounter ((code ending).headD zero) one
  state ←ₜ .inl .initial

private theorem finishNumber_spec (zero one : Γ) (ending : CodeSymbol) (last : Option Bool)
    (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code ending ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      finishNumber zero one ending last
    ⦃ fun _ cost final => final.config = ⟨some (.inl .initial),
        view (finishedCounter one last counter) crossed (code ending ++ suffix) tail⟩ ∧
        final.headPos = origin ∧
        cost.steps ≤ elapsed + 2 * crossed.length + 2 * counter.length + 8 ⦄ := by
  obtain ⟨restore, rest, hcode⟩ := List.exists_cons_of_ne_nil
    (List.ne_nil_of_length_pos (by simp [code_length] : 0 < (code (Γ := Γ) ending).length))
  by_cases hlast : last = some false
  · simp only [finishNumber, hlast, ↓reduceIte, hcode, List.headD_cons]
    vcgen [visitCounter_spec restore one counter crossed (rest ++ suffix) tail label origin elapsed]
    all_goals simp_all [finishedCounter]
  · simp only [finishNumber, hlast, ↓reduceIte]
    vcgen
    simp_all [finishedCounter]
    lia

private noncomputable def readCandidates (zero one : Γ) (ending : CodeSymbol)
    (last : Option Bool) : List Bool → Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit
  | [] => finishNumber zero one ending last
  | bit :: rest => do [TMQuery (Parsing.machine (Γ := Γ))]
      checkPrefix (Parsing.machine (Γ := Γ)) (.inr (lastStage last, CodeSymbol.digit bit))
        (.inl (lastStage last)) (code (CodeSymbol.digit bit))
      ifₜ state =ₜ some (.inr (lastStage last, CodeSymbol.digit bit)) then
        recordDigit zero one bit
      else
        readCandidates zero one ending last rest

private noncomputable def readDigit (zero one : Γ) (ending : CodeSymbol)
    (last : Option Bool) : Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit :=
  readCandidates zero one ending last [false, true]

private theorem readCandidates_bit_spec (zero one : Γ) (ending : CodeSymbol)
    (last : Option Bool) (candidates : List Bool) (bit : Bool) (hmem : bit ∈ candidates)
    (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code (CodeSymbol.digit bit) ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      readCandidates zero one ending last candidates
    ⦃ fun _ cost final => final.config = ⟨some (.inl (lastStage (some bit))),
        view ((if bit then one else zero) :: counter)
          (crossed ++ code (CodeSymbol.digit bit)) suffix tail⟩ ∧
        final.headPos = origin + 12 ∧ cost.steps ≤
          elapsed + 2 * crossed.length + 2 * counter.length + 20 + 24 * candidates.length ⦄ := by
  induction candidates generalizing label origin elapsed with
  | nil => simp at hmem
  | cons candidate rest ih =>
    by_cases heq : candidate = bit
    · subst candidate
      vcgen [readCandidates, testCode_spec (CodeSymbol.digit bit) (CodeSymbol.digit bit) last
        counter crossed suffix tail label origin elapsed, Spec.branch_true_spec]
      case vc1 =>
        refine ⟨by simp_all, ?_⟩
        dsimp only [binderNameHint]
        vcgen [recordDigit_spec zero one bit counter crossed suffix tail
          (some (.inr (lastStage last, CodeSymbol.digit bit))) origin (elapsed + 24)]
        all_goals simp_all
        all_goals lia
    · have hrest : bit ∈ rest := by simpa [Ne.symm heq] using hmem
      vcgen [readCandidates, testCode_spec (CodeSymbol.digit candidate) (CodeSymbol.digit bit) last
        counter crossed suffix tail label origin elapsed, Spec.branch_false_spec]
      case vc1 =>
        refine ⟨by simp_all [CodeSymbol.digit, SingleTapeTM.Description.bitSymbol], ?_⟩
        dsimp only [binderNameHint]
        vcgen [ih hrest (some (.inl (lastStage last))) origin (elapsed + 24)]
        all_goals simp_all [CodeSymbol.digit, SingleTapeTM.Description.bitSymbol]
        all_goals lia

private theorem readCandidates_end_spec (zero one : Γ) (ending : CodeSymbol)
    (hending : ∀ bit, ending ≠ CodeSymbol.digit bit) (last : Option Bool)
    (candidates : List Bool) (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨label, view counter crossed (code ending ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      readCandidates zero one ending last candidates
    ⦃ fun _ cost final => final.config = ⟨some (.inl .initial),
        view (finishedCounter one last counter) crossed (code ending ++ suffix) tail⟩ ∧
        final.headPos = origin ∧ cost.steps ≤
          elapsed + 2 * crossed.length + 2 * counter.length + 8 +
            24 * candidates.length ⦄ := by
  induction candidates generalizing label origin elapsed with
  | nil =>
    vcgen [readCandidates, finishNumber_spec zero one ending last counter crossed suffix tail
      label origin elapsed]
    all_goals simp_all
  | cons candidate rest ih =>
    have hne := Ne.symm (hending candidate)
    vcgen [readCandidates, testCode_spec (CodeSymbol.digit candidate) ending last
      counter crossed suffix tail label origin elapsed, Spec.branch_false_spec]
    case vc1 =>
      refine ⟨by simp_all, ?_⟩
      dsimp only [binderNameHint]
      vcgen [ih (some (.inl (lastStage last))) origin (elapsed + 24)]
      all_goals simp_all
      all_goals lia

private noncomputable def readLoop (zero one : Γ) (ending : CodeSymbol) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  whileₜ (notₜ state =ₜ some (.inl .initial)) do
    select [none, some false, some true]
      (fun last => .stateIs (some (.inl (lastStage last)))) (readDigit zero one ending)

private def counterResult (zero one : Γ) : Option Bool → List Bool → List Γ → List Γ
  | last, [], counter => finishedCounter one last counter
  | _, bit :: rest, counter =>
      counterResult zero one (some bit) rest ((if bit then one else zero) :: counter)

omit [Inhabited Γ] [Fintype Γ] [Nontrivial Γ] [DecidableEq Γ] in
private theorem counterResult_eq (zero one : Γ) (last : Option Bool)
    (digits : List Bool) (counter : List Γ) :
    counterResult zero one last digits counter =
      finishedCounter one (digits.getLast?.or last)
        (digits.reverse.map (fun bit => if bit then one else zero) ++ counter) := by
  induction digits generalizing last counter with
  | nil => rfl
  | cons bit rest ih =>
    rw [counterResult, ih]
    cases rest with
    | nil => simp
    | cons next rest =>
      cases hlast : (next :: rest).getLast? with
      | none => simp at hlast
      | some last => simp [List.reverse_cons, List.map_append, List.append_assoc, hlast]

private def storedBits (digits : List Bool) : List Bool :=
  (if digits.getLast? = some false then [true] else []) ++ digits.reverse

private theorem storedBits_value (digits : List Bool) :
    Nat.ofDigits 2 ((storedBits digits).reverse.map Bool.toNat) =
      Computability.decodeNat digits := by
  rw [Computability.decodeNat_eq_ofDigits]
  by_cases hlast : digits.getLast? = some false <;>
    simp [storedBits, hlast, List.map_append, Nat.ofDigits_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil]

private theorem storedBits_length (digits : List Bool) :
    (storedBits digits).length ≤ digits.length + 1 := by
  unfold storedBits
  split_ifs <;> simp

private theorem selectDigit_spec (zero one : Γ) (ending : CodeSymbol) (last : Option Bool)
    {pre : TMCost → TMState (Parsing.machine (Γ := Γ)) → Prop}
    {post : Unit → TMCost → TMState (Parsing.machine (Γ := Γ)) → Prop}
    (hread : ⦃ pre ⦄ readDigit zero one ending last ⦃ post ⦄)
    (hstate : ∀ cost current, pre cost current →
      current.config.state = some (.inl (lastStage last))) :
    ⦃ pre ⦄ select [none, some false, some true]
      (fun last => TMCondition.stateIs (tm := Parsing.machine (Γ := Γ))
        (some (.inl (lastStage last)))) (readDigit zero one ending) ⦃ post ⦄ := by
  have hmem : last ∈ [none, some false, some true] := by
    cases last with
    | none => simp
    | some bit => cases bit <;> simp
  apply Std.WP.Triple.intro
  intro initial current hp
  vcgen [Spec.select_spec [none, some false, some true]
    (fun last => TMCondition.stateIs (tm := Parsing.machine (Γ := Γ))
      (some (.inl (lastStage last)))) (readDigit zero one ending) last hmem]
  refine ⟨?_, hread.le_wp initial current hp⟩
  intro candidate
  simp [hstate initial current hp, lastStage_injective.eq_iff, eq_comm]

private theorem readLoop_done_spec (zero one : Γ) (ending : CodeSymbol) (contents : BiTape Γ)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some (.inl .initial), contents⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      readLoop zero one ending
    ⦃ fun _ cost final => final.config = ⟨some (.inl .initial), contents⟩ ∧
        final.headPos = origin ∧ cost.steps ≤ elapsed ⦄ := by
  unfold readLoop
  vcgen [Spec.while_false_spec]
  simp_all

private theorem readLoop_spec (zero one : Γ) (ending : CodeSymbol)
    (hending : ∀ bit, ending ≠ CodeSymbol.digit bit) (last : Option Bool)
    (digits : List Bool) (counter crossed suffix : List Γ) (tail : StackTape Γ)
    (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨some (.inl (lastStage last)),
        view counter crossed ((digits.flatMap fun bit => code (CodeSymbol.digit bit)) ++
          code ending ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      readLoop zero one ending
    ⦃ fun _ cost final => final.config = ⟨some (.inl .initial),
        view (counterResult zero one last digits counter)
          (crossed ++ digits.flatMap fun bit => code (CodeSymbol.digit bit))
          (code ending ++ suffix) tail⟩ ∧
        final.headPos = origin + 12 * digits.length ∧ cost.steps ≤ elapsed +
          (digits.length + 1) *
            (2 * (crossed.length + counter.length + 13 * digits.length) + 80) ⦄ := by
  have hstage (previous : Option Bool) : lastStage (Γ := Γ) previous ≠ .initial := by
    cases previous <;> simp [lastStage]
  induction digits generalizing last counter crossed origin elapsed with
  | nil =>
    have hbody := selectDigit_spec zero one ending last
      (readCandidates_end_spec zero one ending hending last [false, true]
        counter crossed suffix tail
        (some (.inl (lastStage last))) origin elapsed)
      (fun _ _ hp => by simp [hp.1])
    unfold readLoop
    vcgen [Spec.while_step_spec (loop := readLoop zero one ending) (hloop := rfl), hbody,
      readLoop_done_spec zero one ending
        (view (finishedCounter one last counter) crossed (code ending ++ suffix) tail)
        origin (elapsed + 2 * crossed.length + 2 * counter.length + 56)]
    all_goals simp_all [counterResult]
    all_goals lia
  | cons bit rest ih =>
    have hbody := selectDigit_spec zero one ending last
      (readCandidates_bit_spec zero one ending last [false, true] bit (by cases bit <;> simp)
        counter crossed ((rest.flatMap fun bit => code (CodeSymbol.digit bit)) ++
          code ending ++ suffix) tail (some (.inl (lastStage last))) origin elapsed)
      (fun _ _ hp => by simp [hp.1])
    have htime : 2 * crossed.length + 2 * counter.length + 68 + (rest.length + 1) *
        (2 * ((crossed ++ code (CodeSymbol.digit bit)).length +
          ((if bit then one else zero) :: counter).length + 13 * rest.length) + 80) ≤
        (rest.length + 2) *
          (2 * (crossed.length + counter.length + 13 * (rest.length + 1)) + 80) := by
      simp only [List.length_append, List.length_cons, code_length]
      ring_nf
      lia
    have hrest := ih (some bit) ((if bit then one else zero) :: counter)
      (crossed ++ code (CodeSymbol.digit bit)) (origin + 12)
      (elapsed + 2 * crossed.length + 2 * counter.length + 68)
    change Std.WP.Triple _ _ _ () at hrest
    unfold readLoop
    vcgen [Spec.while_step_spec (loop := readLoop zero one ending) (hloop := rfl), hbody, hrest]
    all_goals simp_all [counterResult, List.append_assoc]
    all_goals lia

/--
This machine template reads a number into the empty counter to its left and stops at its ending.
It preserves the description. The containing machine fixes both digit symbols and the ending
independently of the input. The digits and their number are read from the tape.
-/
noncomputable def readNumber (zero one : Γ) (ending : CodeSymbol) :
    Prog (TMQuery (Parsing.machine (Γ := Γ))) Unit := do [TMQuery (Parsing.machine (Γ := Γ))]
  state ←ₜ .inl (lastStage none)
  readLoop zero one ending

/--
The reader preserves the description, writes the decoded number in the preceding counter, and
stops at the ending symbol. The bound counts moves in terms of the number of digits and their
distance from the counter. It does not depend on the value of the decoded number.
-/
@[spec] theorem readNumber_spec (zero one : Γ) (ending : CodeSymbol)
    (hending : ∀ bit, ending ≠ CodeSymbol.digit bit)
    (digits : List Bool) (crossed suffix : List Γ) (tail : StackTape Γ)
    (label : Option (Parsing.State Γ)) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config = ⟨label, BiTape.segment
        (StackTape.prepend crossed.reverse StackTape.nil)
        ((finiteWordsOver CodeSymbol Γ).encode (digits.map CodeSymbol.digit) ++
          (finiteWordsOver CodeSymbol Γ).encode [ending] ++ suffix) tail⟩ ∧
        current.headPos = origin ∧ cost.steps ≤ elapsed ⦄
      readNumber zero one ending
    ⦃ fun _ cost final => ∃ bits : List Bool,
        final.config = ⟨some (.inl .initial), BiTape.segment
          (StackTape.prepend
            (crossed ++ (finiteWordsOver CodeSymbol Γ).encode (digits.map CodeSymbol.digit)).reverse
            (StackTape.cons none
              (StackTape.mapSome (bits.map (fun bit => if bit then one else zero)).reverse)))
          ((finiteWordsOver CodeSymbol Γ).encode [ending] ++ suffix) tail⟩ ∧
        final.headPos = origin +
          ((finiteWordsOver CodeSymbol Γ).encode (digits.map CodeSymbol.digit)).length ∧
        Nat.ofDigits 2 (bits.reverse.map Bool.toNat) = Computability.decodeNat digits ∧
        bits.length ≤ digits.length + 1 ∧ cost.steps ≤ elapsed +
          (digits.length + 1) * (2 * (crossed.length + 13 * digits.length) + 80) ⦄ := by
  have hinput : (finiteWordsOver CodeSymbol Γ).encode (digits.map CodeSymbol.digit) =
      digits.flatMap (fun bit => code (CodeSymbol.digit bit)) := by
    rw [encode_finiteWordsOver, List.flatMap_map]
    rfl
  have hlength : ((finiteWordsOver CodeSymbol Γ).encode (digits.map CodeSymbol.digit)).length =
      12 * digits.length := by
    rw [hinput, List.length_flatMap]
    simp [code_length, List.sum_replicate, Nat.mul_comm]
  have hresult : counterResult zero one none digits [] =
      (storedBits digits).map (fun bit => if bit then one else zero) := by
    rw [counterResult_eq]
    by_cases hlast : digits.getLast? = some false <;>
      simp [finishedCounter, storedBits, hlast]
  vcgen [readNumber, readLoop_spec zero one ending hending none digits [] crossed suffix tail
    origin elapsed]
  case vc1 => simp_all [view, code, List.append_assoc]
  case vc2 =>
    refine ⟨storedBits digits, ?_, ?_, storedBits_value digits, storedBits_length digits, ?_⟩
    all_goals simp_all [view, code]

end Algolean.Algorithms.TMSATToSAT.Fields
