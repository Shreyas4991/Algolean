/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Parsing
public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Evaluation
public import Algolean.Models.SingleTapeTM.Compiler.Basic

/-!
# A Turing machine that checks SAT certificates

* `verify` first checks how the input is written. It evaluates correctly encoded formula-certificate
  pairs and returns false on every incorrectly written input.
* The program erases the input and leaves one Boolean digit under the head, just after the original
  input. Missing variable values mean false, and repeated assignments use the first listed value.
* `verify_correct` proves the answer and termination on every input word. For input length `n`,
  time is at most `27 * (n + 1) ^ 4` move instructions, and total space is at most that bound
  plus `max 1 n` cells. `verify_decides` states which language the program decides.
* `computer` puts the program and these proofs into `PolyTimeComputable`.
* `transitionTableComputer` compiles it to a finite transition table with a polynomial bound on
  the number of transitions.

One fixed program handles every input. The formula, certificate, and their lengths are read from
its tape, rather than provided as parameters to its definition.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier

open Cslib Cslib.Turing TMQuery Problems.SAT Polynomial
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/--
This Lean function specifies the required answer. A correctly written pair gives the formula's
value under the certificate's assignment. Any other input gives false. The Turing machine below
computes this answer by scanning and changing its tape.
-/
def result (word : List Symbol) : Bool :=
  match verifierEncoding.decode word with
  | some (formula, certificate) => formula.eval (Certificate.assignment certificate)
  | none => false

/-- On an encoded pair, the specified answer is the formula's value under its certificate. -/
@[simp] theorem result_encode (formula : CNF Variable) (certificate : Certificate) :
    result (verifierEncoding.encode (formula, certificate)) =
      formula.eval (Certificate.assignment certificate) := by
  simp [result]

/--
On the word pairs used by NP, the specified answer agrees with the existing SAT checker.
Either incorrectly encoded part makes the answer false.
-/
theorem result_wordPair (word certificate : List CodeSymbol) :
    result ((Alphabet.wordPair CodeSymbol).encode (word, certificate)) =
      Problems.SAT.verify word certificate := by
  simp only [result, verifierEncoding, Computability.Encoding.pair,
    Alphabet.wordPair_encode, Alphabet.readWord_append_marker]
  rw [show (Alphabet.words CodeSymbol 1).decode (certificate.map Sum.inl) = some certificate from
    (Alphabet.words CodeSymbol 1).decode_encode certificate]
  cases hf : encoding.decode word <;> cases hc : certificateEncoding.decode certificate <;>
    simp [Problems.SAT.verify, hf, hc]

/--
This machine gives distinct state names to the format checker and the evaluator. Its transition
rule preserves the current cell and halts; the query program `verify` provides the instructions.
The existing query compiler can turn that program into a transition-table Turing machine.
-/
abbrev machine : SingleTapeTM Symbol where
  State := FormatState ⊕ Evaluation.machine.State
  q₀ := .inl .clauseStart
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This runs the format checker with its state names placed in the combined machine. -/
private def checkInput : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ Sum.inl formatMachine.q₀
  checkFormat.reduceProg (relabelReduction (Sum.inl : FormatState → machine.State))

/-- This starts the evaluator in its own initial state and runs it on the current tape. -/
private def evaluateInput : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ Sum.inr Evaluation.machine.q₀
  Evaluation.evaluate.reduceProg
    (relabelReduction (Sum.inr : Evaluation.machine.State → machine.State))

/-- This erases an incorrectly written input and writes false on the blank just after it. -/
private def rejectInput : Prog (TMQuery machine) Unit := do [TMQuery machine]
  eraseRight machine
  tape ←ₜ some (digit false)

/--
Starting at the first input cell, this program checks the format, then evaluates a correctly
written pair or rejects an incorrectly written word. It leaves only its Boolean answer on the
tape, with the head on that answer at the first cell after the original input.
-/
def verify : Prog (TMQuery machine) Unit := do [TMQuery machine]
  checkInput
  ifₜ state =ₜ some (Sum.inl FormatState.inputEnd) then
    evaluateInput
  else
    rejectInput

/--
The format checker keeps its unchanged tape, starting coordinate, exact move count, and test for
correctly written pairs when its state names are placed in the combined machine.
-/
private theorem checkInput_correct (word : List Symbol) (s : TMState machine)
    (htape : s.config.BiTape = BiTape.mk₁ word) :
    ∃ cost final, Completes checkInput s cost final ∧
      final.config.BiTape = s.config.BiTape ∧ final.headPos = s.headPos ∧
      (final.config.state = some (.inl FormatState.inputEnd) ↔
        ∃ formula certificate, word = verifierEncoding.encode (formula, certificate)) ∧
      cost.steps = 2 * word.length + 2 := by
  let source : TMState formatMachine :=
    ⟨⟨some formatMachine.q₀, s.config.BiTape⟩, s.headPos, s.cellsAllocated, s.cellsVisited⟩
  obtain ⟨cost, final, hr, hf, hp, hformat, ht⟩ :=
    checkFormat_correct word source (by simpa [source, cursor_start] using htape)
  let inject : FormatState → machine.State := Sum.inl
  have hrun := hr.relabel inject Sum.inl_injective
  have hsource : source.relabel inject =
      {s with config.state := some (Sum.inl formatMachine.q₀)} := by
    cases s
    rfl
  rw [hsource] at hrun
  refine ⟨0 + cost, final.relabel inject, (completes_update s _).seq hrun, ?_, ?_, ?_, ?_⟩
  · simpa [TMState.relabel, source] using hf
  · simpa [TMState.relabel, source] using hp
  · have hlabel : final.config.state.map inject = some (.inl FormatState.inputEnd) ↔
        final.config.state = some FormatState.inputEnd := by
      cases final.config.state <;> simp [inject]
    exact hlabel.trans (by simpa [verifierEncoding_encode] using hformat)
  · simpa using ht

/--
The evaluator keeps its output, final head coordinate, and time bound when its states are placed
in the combined machine. It is run only on a correctly encoded formula-certificate pair.
-/
private theorem evaluateInput_correct (formula : CNF Variable) (certificate : Certificate)
    (s : TMState machine)
    (htape : s.config.BiTape = BiTape.mk₁ (verifierEncoding.encode (formula, certificate))) :
    let input := verifierEncoding.encode (formula, certificate)
    ∃ cost final, Completes evaluateInput s cost final ∧
      final.config.BiTape = BiTape.mk₁ [digit (formula.eval (Certificate.assignment certificate))] ∧
      final.headPos = s.headPos + input.length ∧
      cost.steps ≤ 25 * (input.length + 1) ^ 4 := by
  let source : TMState Evaluation.machine :=
    ⟨⟨some Evaluation.machine.q₀, s.config.BiTape⟩, s.headPos,
      s.cellsAllocated, s.cellsVisited⟩
  obtain ⟨cost, final, hr, hf, hp, ht⟩ :=
    Evaluation.evaluate_correct formula certificate source htape
  let inject : Evaluation.machine.State → machine.State := Sum.inr
  have hrun := hr.relabel inject Sum.inr_injective
  have hsource : source.relabel inject =
      {s with config.state := some (Sum.inr Evaluation.machine.q₀)} := by
    cases s
    rfl
  rw [hsource] at hrun
  exact ⟨0 + cost, final.relabel inject, (completes_update s _).seq hrun, hf, hp,
    by simpa using ht⟩

/-- Rejecting any input erases the whole word and leaves false under the final head. -/
private theorem rejectInput_correct (word : List Symbol) (s : TMState machine)
    (htape : s.config.BiTape = BiTape.mk₁ word) :
    Runs rejectInput s (BiTape.mk₁ [digit false]) (s.headPos + word.length) word.length := by
  apply Spec.runs
  vcgen [rejectInput, eraseRight_spec (tm := machine) word StackTape.nil
    s.config.state s.headPos 0]
  all_goals cases word
  all_goals cases hcfg : s.config
  all_goals simp_all [TMState.write, BiTape.mk₁, BiTape.nil, BiTape.write, BiTape.segment]

/--
For every input word on an otherwise blank tape, the verifier finishes with exactly one symbol,
which is its specified Boolean answer, under the head. The head finishes one cell past the
original word. The bound includes format checking and applies to incorrectly written words and
to certificates of any length, using at most `27 * (word.length + 1) ^ 4` head moves.
-/
private theorem verify_correct_impl (word : List Symbol) (s : TMState machine)
    (htape : s.config.BiTape = BiTape.mk₁ word) :
    ∃ cost final, Completes verify s cost final ∧
      final.config.BiTape = BiTape.mk₁ [digit (result word)] ∧
      final.headPos = s.headPos + word.length ∧
      cost.steps ≤ 27 * (word.length + 1) ^ 4 := by
  obtain ⟨a, middle, hformat, hmiddle, hpos, hvalid, ha⟩ := checkInput_correct word s htape
  have hpower : word.length + 1 ≤ (word.length + 1) ^ 4 := Nat.le_self_pow (by decide) _
  by_cases hw : ∃ formula certificate, word = verifierEncoding.encode (formula, certificate)
  · obtain ⟨formula, certificate, hword⟩ := hw
    obtain ⟨b, final, heval, hf, hp, hb⟩ := evaluateInput_correct formula certificate middle
      (by simp [hmiddle, htape, hword])
    have hbranch : Completes
        (branch (.stateIs (some (Sum.inl FormatState.inputEnd))) evaluateInput rejectInput)
        middle b final := by
      apply Completes.branch
      simpa [hvalid.mpr ⟨formula, certificate, hword⟩] using heval
    refine ⟨a + b, final, by simpa [verify] using hformat.seq hbranch, ?_, ?_, ?_⟩
    · simpa [hword] using hf
    · simpa [hpos, hword] using hp
    · have hb' : b.steps ≤ 25 * (word.length + 1) ^ 4 := by simpa [hword] using hb
      have ha' : a.steps ≤ 2 * (word.length + 1) ^ 4 := by lia
      change a.steps + b.steps ≤ _
      lia
  · have hresult : result word = false := by
      cases hd : verifierEncoding.decode word with
      | none => simp [result, hd]
      | some pair =>
        obtain ⟨formula, certificate⟩ := pair
        exact False.elim (hw ⟨formula, certificate, decode_verifierEncoding_eq_some_iff.mp hd⟩)
    obtain ⟨b, final, hrejected, hf, hp, hb⟩ := rejectInput_correct word middle
      (hmiddle.trans htape)
    have hbranch : Completes
        (branch (.stateIs (some (Sum.inl FormatState.inputEnd))) evaluateInput rejectInput)
        middle b final := by
      apply Completes.branch
      have hlabel : middle.config.state ≠ some (.inl FormatState.inputEnd) :=
        fun h => hw (hvalid.mp h)
      simpa [hlabel] using hrejected
    refine ⟨a + b, final, by simpa [verify] using hformat.seq hbranch, ?_, ?_, ?_⟩
    · simpa [hresult] using congrArg SingleTapeTM.Cfg.BiTape hf
    · simpa [hpos] using hp
    · change a.steps + b.steps ≤ _
      lia

/--
The fixed verifier computes its specified answer on every word, including incorrectly encoded
inputs. Time is bounded by `27 * (n + 1) ^ 4` move instructions. Total space also includes the
`max 1 n` cells occupied initially. The input length includes the formula, certificate, and
their separator.
-/
theorem verify_correct :
    ComputesWithin verify (fun word => [digit (result word)])
      (fun n => 27 * (n + 1) ^ 4) (fun n => max 1 n + 27 * (n + 1) ^ 4) := by
  apply TMSolves.of_time_bound
  intro word
  obtain ⟨cost, final, hc, hf, _, ht⟩ :=
    verify_correct_impl word (TMState.init machine word) rfl
  exact ⟨[digit (result word)], cost, final, hc, hf, rfl, ht⟩

/--
This language contains the correctly encoded formula-certificate pairs whose listed values
make every clause true. Missing values mean false, and a repeated variable uses its first
listed value. Incorrectly written words are excluded.
-/
@[expose] def acceptedPairs : Language Symbol := {word | result word = true}

/--
The fixed verifier decides the accepted formula-certificate pairs by leaving the true symbol
under its final head exactly on those pairs. The same time and total space bounds apply to
every input word, including malformed words.
-/
theorem verify_decides :
    DecidesWithin verify acceptedPairs [digit true]
      (fun n => 27 * (n + 1) ^ 4) (fun n => max 1 n + 27 * (n + 1) ^ 4) := by
  apply verify_correct.consequence
  intro word output houtput
  have heq : output = [digit (result word)] := houtput
  simp [heq, acceptedPairs, digit]

/-- This record stores the verifier and its common correctness and resource proof. -/
noncomputable def computer : PolyTimeComputable (fun word => [digit (result word)]) where
  tm := machine
  program := verify
  timeBound n := 27 * (n + 1) ^ 4
  computesWithin := verify_correct
  poly := 27 * (X + 1) ^ 4
  bounds n := by simp

/--
This compiles the verifier into a transition-table Turing machine computing the same answer.
The compiler changes a query bound `T(n)` to `C * T(n) + C`. Here `C` is fixed by this program
and its finite state and symbol sets, so it is independent of the formula and certificate.
The resulting transition bound is therefore still a polynomial of degree four.
-/
noncomputable def transitionTableComputer :
    SingleTapeTM.PolyTimeComputable (fun word => [digit (result word)]) :=
  computer.toTransitionTable

end Algolean.Algorithms.SingleTapeTuringMachines.SAT.Verifier
