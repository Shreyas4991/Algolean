/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Lookup
public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Erasing
public import Mathlib.Tactic.GCongr
public import Algolean.Models.SingleTapeTM.Composition.Relabel

/-!
# Evaluating an encoded formula using a certificate

* The program reads the formula from left to right. It erases each literal after looking up
  its variable, so the next unread name always begins at the start of the occupied tape.
* A true literal makes its clause true. The program then erases the rest of that clause.
  A clause with no true literal makes the whole formula false.
* Lookup preserves the unread formula and the certificate. The same certificate assignment
  therefore provides every variable's value throughout the computation.
* `evaluate_correct` proves that the program leaves only the formula's truth value on the tape,
  with the head on that value. On an encoded pair of length `n`, it makes at most
  `25 * (n + 1) ^ 4` head moves.

The program receives its formula and certificate on the tape. Its definitions have no parameters
for either value or their lengths. The Boolean parameter on literal checking selects one of two
instruction blocks, for an unnegated or a negated variable.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT.Evaluation

open Cslib Cslib.Turing TMQuery Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/-- These three states record the evaluator's progress independently of lookup's states. -/
inductive Flag where
  /-- The clause still needs a true literal. -/
  | checking
  /-- The clause or formula checked so far is true. -/
  | satisfied
  /-- A clause has been checked and is false. -/
  | unsatisfied
  deriving DecidableEq

instance : Fintype Flag := .ofList [.checking, .satisfied, .unsatisfied]
  (by intro flag; cases flag <;> decide)

/--
This machine gives distinct names to lookup's states and to the evaluator's three states.
Its transition table preserves the current symbol and halts; the query program provides the
instructions used during evaluation.
-/
abbrev machine : SingleTapeTM Symbol where
  State := Lookup.State ⊕ Flag
  q₀ := .inr .satisfied
  tr _ symbol := (⟨symbol, none⟩, none)

private abbrev State := machine.State

/-- This program runs lookup using its own state names inside the evaluator's machine. -/
private def lookupOnTape : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ Sum.inl Lookup.machine.q₀
  Lookup.lookup.reduceProg (relabelReduction (Sum.inl : Lookup.State → machine.State))

/--
Changing lookup's state names preserves its result, its unchanged tape, and its move bound.
The extra evaluator states are not used while the lookup program runs.
-/
private theorem lookupOnTape_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (name : Variable) (certificate : Certificate)
    (s : TMState machine) :
    let word := name.map digit ++ nameEnd :: between ++ certificateSeparator ::
      (certificateEncoding.encode certificate).map Sum.inl
    s.config.BiTape = cursor [] word →
    ∃ cost final, Completes lookupOnTape s cost final ∧
      final.config = ⟨some (.inl (.value (Certificate.assignment certificate name))),
        s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 19 * (word.length + 1) ^ 3 := by
  dsimp only
  intro htape
  let source : TMState Lookup.machine :=
    ⟨⟨some Lookup.machine.q₀, s.config.BiTape⟩, s.headPos, s.cellsAllocated, s.cellsVisited⟩
  obtain ⟨cost, final, hr, hf, hp, ht⟩ :=
    Lookup.lookup_between_correct between hbetween name certificate source htape
  let inject : Lookup.State → machine.State := Sum.inl
  have hrun := hr.relabel inject Sum.inl_injective
  have hsource :
      source.relabel inject = {s with config.state := some (.inl Lookup.machine.q₀)} := by
    cases s
    rfl
  rw [hsource] at hrun
  refine ⟨0 + cost, final.relabel inject, (completes_update s _).seq hrun, ?_, ?_, ?_⟩
  · simp [TMState.relabel, hf, source, inject]
  · simpa [TMState.relabel, source] using hp
  · simpa using ht

/-- This state records whether the formula evaluated to true or false. -/
private def resultState (value : Bool) : State :=
  if value then .inr Flag.satisfied else .inr Flag.unsatisfied

/-- This state records whether a literal satisfied its clause or the search must continue. -/
private def literalState (value : Bool) : State :=
  if value then .inr Flag.satisfied else .inr Flag.checking

/--
This program uses the value just returned by lookup. An unnegated variable satisfies the clause
when its value is true; a negated variable satisfies it when its value is false.
-/
private def finishLiteral (positive : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ state =ₜ some ((Sum.inl (Lookup.State.value positive))) then
    state ←ₜ (Sum.inr Flag.satisfied)
  else
    state ←ₜ (Sum.inr Flag.checking)

/--
Starting on a literal's sign, this program erases the sign, looks up the binary name that follows,
and then erases the name and its ending. It leaves the head on the next formula symbol and sets
state `satisfied` if the literal is true, or `checking` if another literal must be checked.
-/
private def checkLiteral (positive : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  eraseAndMove machine
  lookupOnTape
  eraseUntil machine nameEnd
  eraseAndMove machine
  finishLiteral positive

/--
This checks one literal of a clause. On the clause's ending it records `unsatisfied`, meaning that
none of the literals was true. Otherwise it chooses the instructions for the sign on the tape.
-/
private def clauseBody : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ tape =ₜ some clauseEnd then
    state ←ₜ (Sum.inr Flag.unsatisfied)
  else
    ifₜ tape =ₜ some positiveSign then
      checkLiteral true
    else
      checkLiteral false

/-- This loop checks literals until one is true or the clause has no literals left. -/
private def clauseLoop : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some (Sum.inr Flag.checking)) do
    clauseBody

/-- This program erases the unneeded remainder of a clause and its following separator. -/
private def finishClause : Prog (TMQuery machine) Unit := do [TMQuery machine]
  eraseUntil machine clauseSeparator
  eraseAndMove machine

/--
This program starts at the first literal of a clause, or at its ending if the clause is empty.
It checks the clause, erases it and its separator, and stops at the start of the next clause.
State `satisfied` means that the clause was true; `unsatisfied` means it was false.
-/
private def checkClause : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ (Sum.inr Flag.checking)
  clauseLoop
  finishClause

/--
This checks and erases one clause. If that clause is false, it also erases the remaining clauses
up to the formula's ending, since their values cannot make the conjunction true.
-/
private def formulaBody : Prog (TMQuery machine) Unit := do [TMQuery machine]
  checkClause
  ifₜ state =ₜ some (Sum.inr Flag.unsatisfied) then
    eraseUntil machine formulaEnd
  else
    pure ()

/-- This loop checks clauses until the head reaches the formula's ending. -/
private def formulaLoop : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (notₜ tape =ₜ some formulaEnd) do
    formulaBody

/--
This program initially records true, so a formula with no clauses evaluates to true. It then
checks the clauses and stops on the formula's ending with the result recorded in its state.
-/
private def checkFormula : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ (Sum.inr Flag.satisfied)
  formulaLoop

/--
The input must be a correctly encoded formula-certificate pair. This program checks every
required clause, erases the remaining input, and writes the result as a single binary digit.
The result is written on the first blank cell after the original input. Every other cell is blank.
-/
def evaluate : Prog (TMQuery machine) Unit := do [TMQuery machine]
  checkFormula
  eraseRight machine
  ifₜ state =ₜ some (Sum.inr Flag.satisfied) then
    tape ←ₜ some (digit true)
  else
    tape ←ₜ some (digit false)

/-- This is the unread formula data followed by the unchanged certificate. -/
private def tailWord (between : List Symbol) (certificate : Certificate) : List Symbol :=
  between ++ certificateSeparator :: certificateSymbols certificate

/-- The certificate's ending adds one symbol, and every entry adds at least two more. -/
private theorem certificate_length (certificate : Certificate) :
    2 * certificate.length + 1 ≤ (certificateSymbols certificate).length := by
  induction certificate with
  | nil => simp [certificateSymbols_nil]
  | cons literal rest ih =>
    cases literal <;>
      simp only [certificateSymbols_pos, certificateSymbols_neg, List.length_cons,
        List.length_append, List.length_map] <;> lia

/-- The symbols of a clause include at least two symbols for each literal and one clause ending. -/
private theorem clause_length (clause : Clause Variable) :
    2 * clause.length + 1 ≤ (certificateSymbols clause).length := certificate_length clause

/-- The encoded formula is longer than its number of clauses and literal occurrences together. -/
private theorem formula_length (formula : CNF Variable) :
    formula.flatten.length + formula.length + 1 ≤ (formulaSymbols formula).length := by
  induction formula with
  | nil => simp [formulaSymbols_nil]
  | cons clause rest ih =>
    have hclause := clause_length clause
    simp only [List.flatten_cons, List.length_append, List.length_cons, formulaSymbols_cons] at ih ⊢
    lia

/-- The clause separator never appears among a clause's literal names or signs. -/
private theorem clauseSeparator_not_mem (clause : Clause Variable) :
    clauseSeparator ∉ certificateSymbols clause := by
  induction clause with
  | nil => decide
  | cons literal rest ih =>
    cases literal <;>
      simpa [certificateSymbols_pos, certificateSymbols_neg, clauseSeparator, positiveSign,
        negativeSign, nameEnd, digit, List.mem_map] using ih

/-- The formula-ending symbol occurs only at the end of an encoded formula. -/
private theorem formulaSymbols_end (formula : CNF Variable) :
    ∃ before, formulaSymbols formula = before ++ [formulaEnd] ∧ formulaEnd ∉ before := by
  induction formula with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons clause rest ih =>
    obtain ⟨before, hbefore, hnot⟩ := ih
    refine ⟨certificateSymbols clause ++ clauseSeparator :: before, ?_, ?_⟩
    · simp [formulaSymbols_cons, hbefore, List.append_assoc]
    · have hclause : formulaEnd ∉ certificateSymbols clause := by
        induction clause with
        | nil => decide
        | cons literal rest ih =>
          cases literal <;>
            simpa [certificateSymbols_pos, certificateSymbols_neg, formulaEnd, positiveSign,
              negativeSign, nameEnd, digit, List.mem_map] using ih
      simpa [List.mem_append, formulaEnd, clauseSeparator] using And.intro hclause hnot

/--
Checking a literal removes only that literal. The unread formula data and the certificate stay
unchanged. The move bound includes lookup, erasing the sign and name, and recording the result.
-/
private theorem checkLiteral_correct (positive : Bool) (name : Variable) (between : List Symbol)
    (certificate : Certificate) (s : TMState machine)
    (hbetween : certificateSeparator ∉ between)
    (htape : s.config.BiTape =
      cursor [] (sign positive :: name.map digit ++ nameEnd :: tailWord between certificate)) :
    let word := sign positive :: name.map digit ++ nameEnd :: tailWord between certificate
    ∃ cost final, Completes (checkLiteral positive) s cost final ∧
      final.config = ⟨some (literalState
        ((if positive then Literal.pos name else .neg name).eval
          (Certificate.assignment certificate))),
        cursor [] (tailWord between certificate)⟩ ∧
      final.headPos = s.headPos + name.length + 2 ∧ cost.steps ≤ 20 * (word.length + 1) ^ 3 := by
  let initial := (s.write none).move .Right
  obtain ⟨b, middle, hlookup, hmiddle, hlookupPos, hb⟩ :=
    lookupOnTape_correct between hbetween name certificate initial (by
      simp [initial, TMState.write, TMState.move, htape, cursor, BiTape.write,
        BiTape.moveRight, tailWord, certificateSymbols, List.append_assoc])
  let W := (sign positive :: name.map digit ++ nameEnd :: tailWord between certificate).length + 1
  have hlookupBound : b.steps ≤ 19 * W ^ 3 := by
    apply hb.trans
    dsimp [W, tailWord, certificateSymbols]
    gcongr
    simp
  have hlinear : name.length + 2 ≤ W := by simp [W]
  have hcube : W ≤ W ^ 3 := Nat.le_self_pow (by decide) _
  have htotal : b.steps + (name.length + 2) ≤ 20 * W ^ 3 := by
    calc
      _ ≤ 19 * W ^ 3 + W := Nat.add_le_add hlookupBound hlinear
      _ ≤ 19 * W ^ 3 + W ^ 3 := Nat.add_le_add_left hcube _
      _ = 20 * W ^ 3 := by ring
  apply Spec.completes
  vcgen [checkLiteral, eraseAndMove_spec, Spec.steps hlookup 1,
    eraseUntil_spec (tm := machine) nameEnd (name.map digit) (tailWord between certificate)
      (by simp [nameEnd, digit, List.mem_map])
      (some (.inl (.value (Certificate.assignment certificate name)))) (s.headPos + 1)
      (1 + b.steps), finishLiteral]
  all_goals cases hcfg : s.config
  all_goals simp_all [initial, W, TMState.move, TMState.write, TMState.moveCost,
    cursor, BiTape.write, BiTape.moveRight, literalState, Literal.eval, add_assoc]
  all_goals split <;> simp_all
  all_goals lia

/-- Erasing a clause's remaining literals stops after its separating symbol. -/
private theorem finishClause_correct (clause : Clause Variable) (between : List Symbol)
    (certificate : Certificate) (s : TMState machine)
    (htape : s.config.BiTape =
      cursor [] (certificateSymbols clause ++ clauseSeparator :: tailWord between certificate)) :
    Runs finishClause s (cursor [] (tailWord between certificate))
      (s.headPos + (certificateSymbols clause).length + 1)
      ((certificateSymbols clause).length + 1) := by
  apply Spec.runs
  vcgen [finishClause,
    eraseUntil_spec (tm := machine) clauseSeparator (certificateSymbols clause)
      (tailWord between certificate) (clauseSeparator_not_mem clause)
      s.config.state s.headPos 0, eraseAndMove_spec]
  all_goals cases hcfg : s.config
  all_goals simp_all [TMState.write, TMState.move, TMState.moveCost,
    cursor, BiTape.write, BiTape.moveRight, add_assoc]

/--
A literal's sign selects the corresponding one of the two literal-checking instruction blocks.
-/
private theorem clauseBody_literal (positive : Bool) (s final : TMState machine) (cost : TMCost)
    (hhead : s.config.BiTape.head = some (sign positive))
    (h : Completes (checkLiteral positive) s cost final) :
    Completes clauseBody s cost final := by
  have hnot :
      ¬((TMCondition.tapeIs (some clauseEnd) : TMCondition machine).eval s.config = true) := by
    cases positive <;> simp [hhead, sign, clauseEnd, positiveSign, negativeSign]
  unfold clauseBody
  apply Completes.branch
  rw [ite_eq_right hnot]
  apply Completes.branch
  cases positive <;> simpa [hhead, sign, positiveSign, negativeSign] using h

/--
The clause loop followed by erasure decides the clause and removes all of it, including its
separator. The original certificate and the later formula data remain unchanged. `budget` is
only an upper bound used in this proof; the running program never receives it.
-/
private theorem clauseLoop_correct (clause : Clause Variable) (between : List Symbol)
    (certificate : Certificate) (budget : ℕ) (s : TMState machine)
    (hbetween : certificateSeparator ∉ between)
    (htape : s.config.BiTape =
      cursor [] (certificateSymbols clause ++ clauseSeparator :: tailWord between certificate))
    (hsize : (certificateSymbols clause ++ clauseSeparator :: tailWord between certificate).length ≤
      budget)
    (hstate : s.config.state = some (.inr Flag.checking)) :
    ∃ cost final, Completes (do clauseLoop; finishClause) s cost final ∧
      final.config = ⟨some (resultState (clause.eval (Certificate.assignment certificate))),
        cursor [] (tailWord between certificate)⟩ ∧
      final.headPos = s.headPos + (certificateSymbols clause).length + 1 ∧
      cost.steps ≤ 22 * (budget + 1) ^ 3 * (clause.length + 1) := by
  induction clause generalizing s with
  | nil =>
    let middle : TMState machine := {s with config.state := some (Sum.inr Flag.unsatisfied)}
    have hbody : Completes clauseBody s 0 middle := by
      unfold clauseBody
      apply Completes.branch
      simpa [htape, certificateSymbols_nil, middle] using completes_update s (.inr Flag.unsatisfied)
    have hfalse := completes_while_false (.stateIs (some (Sum.inr Flag.checking))) clauseBody middle
      (by simp [middle])
    have hloop : Completes clauseLoop s 0 middle := by
      simpa [clauseLoop] using Completes.while_step (by simp [hstate]) hbody hfalse
    obtain ⟨cost, final, hr, hf, hp, ht⟩ :=
      finishClause_correct [] between certificate middle (by simpa [middle] using htape)
    refine ⟨0 + cost, final, hloop.seq hr, ?_, ?_, ?_⟩
    · simpa [middle, resultState] using hf
    · simpa [middle] using hp
    · have hpow := Nat.one_le_pow' 3 budget
      simp only [zero_add, ht, certificateSymbols_nil, List.length_cons, List.length_nil,
        List.length_nil, zero_add, mul_one]
      lia
  | cons literal rest ih =>
    obtain ⟨positive, name, hliteral⟩ :
        ∃ positive : Bool, ∃ name : Variable,
          literal = if positive then Literal.pos name else .neg name := by
      cases literal with
      | pos name => exact ⟨true, name, rfl⟩
      | neg name => exact ⟨false, name, rfl⟩
    subst literal
    let gap := certificateSymbols rest ++ clauseSeparator :: between
    have hgap : certificateSeparator ∉ gap := by
      simpa [gap, certificateSymbols, List.mem_map, certificateSeparator, clauseSeparator]
        using hbetween
    obtain ⟨a, middle, hliteral, hmiddle, hpos, ha⟩ :=
      checkLiteral_correct positive name gap certificate s hgap
        (by simpa [certificateSymbols_cons, tailWord, gap, List.append_assoc] using htape)
    have hbody := clauseBody_literal positive s middle a
      (by simp [htape, certificateSymbols_cons]) hliteral
    have hrestTape : middle.config.BiTape =
        cursor [] (certificateSymbols rest ++ clauseSeparator :: tailWord between certificate) := by
      simp [hmiddle, tailWord, gap, List.append_assoc]
    have hrestSize : (certificateSymbols rest ++
        clauseSeparator :: tailWord between certificate).length ≤ budget := by
      simp only [certificateSymbols_cons, List.length_cons, List.length_append,
        List.length_map] at hsize ⊢
      lia
    have hfirst : a.steps ≤ 20 * (budget + 1) ^ 3 := by
      apply ha.trans
      gcongr
      simpa [certificateSymbols_cons, tailWord, gap, List.append_assoc] using hsize
    cases hvalue : (if positive then Literal.pos name else .neg name).eval
        (Certificate.assignment certificate) with
    | false =>
      obtain ⟨b, final, hr, hf, hp, hb⟩ := ih middle hrestTape hrestSize
        (by simp [hmiddle, literalState, hvalue])
      have hstep := Completes.while_step_seq (by simp [hstate]) (hbody.seq hr)
      refine ⟨a + b, final, by simpa [clauseLoop] using hstep, ?_, ?_, ?_⟩
      · simpa [Clause.eval, hvalue] using hf
      · rw [hp, hpos]
        simp only [certificateSymbols_cons, List.length_cons, List.length_append,
          List.length_map, Nat.cast_add, Nat.cast_one]
        lia
      · let R := (budget + 1) ^ 3
        have hfirst' : a.steps ≤ 22 * R := hfirst.trans (Nat.mul_le_mul_right R (by decide))
        change a.steps + b.steps ≤ 22 * R * ((_ :: rest).length + 1)
        calc
          a.steps + b.steps ≤ 22 * R + 22 * R * (rest.length + 1) :=
            Nat.add_le_add hfirst' hb
          _ = 22 * R * ((_ :: rest).length + 1) := by simp only [List.length_cons]; ring
    | true =>
      have hfalse := completes_while_false
        (.stateIs (some (Sum.inr Flag.checking))) clauseBody middle
        (by simp [hmiddle, literalState, hvalue])
      obtain ⟨b, final, hr, hf, hp, hb⟩ :=
        finishClause_correct rest between certificate middle hrestTape
      have hstep := Completes.while_step_seq (by simp [hstate])
        (hbody.seq (hfalse.seq hr))
      refine ⟨a + b, final, by simpa [clauseLoop] using hstep, ?_, ?_, ?_⟩
      · simpa [hmiddle, literalState, Clause.eval, hvalue, resultState] using hf
      · rw [hp, hpos]
        simp only [certificateSymbols_cons, List.length_cons, List.length_append,
          List.length_map, Nat.cast_add, Nat.cast_one]
        lia
      · let R := (budget + 1) ^ 3
        have hremaining : b.steps ≤ budget := by
          rw [hb]
          simp only [List.length_cons, List.length_append] at hrestSize
          lia
        have hsmall : b.steps ≤ R := hremaining.trans
          ((Nat.le_succ budget).trans (Nat.le_self_pow (by decide) (budget + 1)))
        have hsum : a.steps + b.steps ≤ 22 * R := by lia
        exact hsum.trans (by
          simpa using Nat.mul_le_mul_left (22 * R)
            (show 1 ≤ ((if positive then Literal.pos name else .neg name) :: rest).length + 1 by
              simp))

/-- Starting the clause loop resets the state but does not change the tape or its time bound. -/
private theorem checkClause_correct (clause : Clause Variable) (between : List Symbol)
    (certificate : Certificate) (budget : ℕ) (s : TMState machine)
    (hbetween : certificateSeparator ∉ between)
    (htape : s.config.BiTape =
      cursor [] (certificateSymbols clause ++ clauseSeparator :: tailWord between certificate))
    (hsize : (certificateSymbols clause ++ clauseSeparator :: tailWord between certificate).length ≤
      budget) :
    ∃ cost final, Completes checkClause s cost final ∧
      final.config = ⟨some (resultState (clause.eval (Certificate.assignment certificate))),
        cursor [] (tailWord between certificate)⟩ ∧
      final.headPos = s.headPos + (certificateSymbols clause).length + 1 ∧
      cost.steps ≤ 22 * (budget + 1) ^ 3 * (clause.length + 1) := by
  let initial : TMState machine := {s with config.state := some (Sum.inr Flag.checking)}
  obtain ⟨cost, final, hr, hf, hp, ht⟩ := clauseLoop_correct clause between certificate budget
    initial hbetween (by simpa [initial] using htape) hsize rfl
  exact ⟨0 + cost, final, (completes_update s (.inr Flag.checking)).seq hr, hf, hp,
    by simpa using ht⟩

/-- Erasing an unread formula stops on its ending and leaves the certificate unchanged. -/
private theorem eraseFormula_correct (formula : CNF Variable) (certificate : Certificate)
    (s : TMState machine)
    (htape : s.config.BiTape = cursor [] (tailWord (formulaSymbols formula) certificate)) :
    Runs (eraseUntil machine formulaEnd) s (cursor [] (tailWord [formulaEnd] certificate))
      (s.headPos + ((formulaSymbols formula).length - 1 : ℕ))
      ((formulaSymbols formula).length - 1) := by
  obtain ⟨before, hbefore, hnot⟩ := formulaSymbols_end formula
  have hlength : (formulaSymbols formula).length - 1 = before.length := by
    simp [hbefore]
  apply Spec.runs
  vcgen [eraseUntil_spec (tm := machine) formulaEnd before
    (certificateSeparator :: certificateSymbols certificate) hnot s.config.state s.headPos 0]
  all_goals cases hcfg : s.config
  all_goals simp_all [tailWord, List.append_assoc]

/--
The formula loop checks clauses until one is false or all have been checked. It erases the
formula except for its ending and keeps the certificate unchanged. The initial state records
true, so a formula with no clauses returns true. The size bound is used only in this proof.
-/
private theorem formulaLoop_correct (formula : CNF Variable) (certificate : Certificate)
    (budget : ℕ) (s : TMState machine)
    (htape : s.config.BiTape = cursor [] (tailWord (formulaSymbols formula) certificate))
    (hsize : (tailWord (formulaSymbols formula) certificate).length ≤ budget)
    (hstate : s.config.state = some (.inr Flag.satisfied)) :
    ∃ cost final, Completes formulaLoop s cost final ∧
      final.config = ⟨some (resultState (CNF.eval formula (Certificate.assignment certificate))),
        cursor [] (tailWord [formulaEnd] certificate)⟩ ∧
      final.headPos = s.headPos + ((formulaSymbols formula).length - 1 : ℕ) ∧
      cost.steps ≤ 24 * (budget + 1) ^ 3 * (formula.flatten.length + formula.length) := by
  induction formula generalizing s with
  | nil =>
    refine ⟨0, s, ?_, ?_, ?_, by simp⟩
    · exact completes_while_false _ _ s (by simp [htape, tailWord, formulaSymbols_nil])
    · have hc : s.config = ⟨s.config.state, s.config.BiTape⟩ := by cases s.config; rfl
      conv_lhs => rw [hc]
      simp [hstate, htape, formulaSymbols_nil, resultState]
    · simp [formulaSymbols_nil]
  | cons clause rest ih =>
    have hbetween : certificateSeparator ∉ formulaSymbols rest :=
      certificateSeparator_not_mem _
    obtain ⟨a, middle, hclause, hmiddle, hpos, ha⟩ :=
      checkClause_correct clause (formulaSymbols rest) certificate budget s hbetween
        (by simpa [tailWord, formulaSymbols_cons, List.append_assoc] using htape)
        (by simpa [tailWord, formulaSymbols_cons, List.append_assoc] using hsize)
    have hrestTape : middle.config.BiTape =
        cursor [] (tailWord (formulaSymbols rest) certificate) := by
      simp [hmiddle]
    have hrestSize : (tailWord (formulaSymbols rest) certificate).length ≤ budget := by
      simp only [tailWord, formulaSymbols_cons, List.length_append, List.length_cons] at hsize ⊢
      lia
    have hcondition :
        (TMCondition.not (.tapeIs (some formulaEnd))).eval s.config = true := by
      cases clause with
      | nil => simp [htape, tailWord, formulaSymbols_cons, certificateSymbols_nil,
          formulaEnd, clauseEnd]
      | cons literal rest =>
        cases literal <;>
          simp [htape, tailWord, formulaSymbols_cons, certificateSymbols_pos,
            certificateSymbols_neg, formulaEnd, positiveSign, negativeSign]
    cases hvalue : clause.eval (Certificate.assignment certificate) with
    | false =>
      obtain ⟨b, final, herase, hfinal, hfinalPos, hb⟩ :=
        eraseFormula_correct rest certificate middle hrestTape
      have hbranch : Completes
          (branch (.stateIs (some (Sum.inr Flag.unsatisfied)))
            (eraseUntil machine formulaEnd) (pure ())) middle b final := by
        apply Completes.branch
        simpa [hmiddle, resultState, hvalue] using herase
      have hbody : Completes formulaBody s (a + b) final := by
        simpa [formulaBody] using hclause.seq hbranch
      have hfalse := completes_while_false (.not (.tapeIs (some formulaEnd))) formulaBody final
        (by simp [hfinal, tailWord])
      refine ⟨a + b + 0, final, ?_, ?_, ?_, ?_⟩
      · exact Completes.while_step hcondition hbody hfalse
      · simp [hfinal, hmiddle, resultState, hvalue, CNF.eval]
      · rw [hfinalPos, hpos]
        have hlength := formula_length rest
        simp only [formulaSymbols_cons, List.length_append, List.length_cons]
        lia
      · let R := (budget + 1) ^ 3
        have hsmall : b.steps ≤ R := by
          rw [hb]
          have hlength : (formulaSymbols rest).length ≤ budget := by
            simp only [tailWord, List.length_append, List.length_cons] at hrestSize
            lia
          exact (Nat.sub_le _ _).trans (hlength.trans
            ((Nat.le_succ budget).trans (Nat.le_self_pow (by decide) (budget + 1))))
        have hsum : a.steps + b.steps + 0 ≤ 24 * R * (clause.length + 1) := by
          calc
            a.steps + b.steps + 0 ≤ 22 * R * (clause.length + 1) + R := by
              simpa using Nat.add_le_add ha hsmall
            _ ≤ 24 * R * (clause.length + 1) := by nlinarith
        apply hsum.trans
        apply Nat.mul_le_mul_left
        simp only [List.flatten_cons, List.length_append, List.length_cons]
        lia
    | true =>
      have hbranch : Completes
          (branch (.stateIs (some (Sum.inr Flag.unsatisfied)))
            (eraseUntil machine formulaEnd) (pure ())) middle 0 middle := by
        apply Completes.branch
        simp [hmiddle, resultState, hvalue]
      have hbody : Completes formulaBody s (a + 0) middle := by
        simpa [formulaBody] using hclause.seq hbranch
      obtain ⟨b, final, hr, hf, hp, hb⟩ := ih middle hrestTape hrestSize
        (by simp [hmiddle, hvalue, resultState])
      refine ⟨a + 0 + b, final, Completes.while_step hcondition hbody hr, ?_, ?_, ?_⟩
      · simpa [CNF.eval, hvalue] using hf
      · rw [hp, hpos]
        have hlength := formula_length rest
        simp only [formulaSymbols_cons, List.length_append, List.length_cons]
        lia
      · let R := (budget + 1) ^ 3
        have hfirst : a.steps ≤ 24 * R * (clause.length + 1) := by
          exact ha.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right R (by decide)))
        calc
          (a + 0 + b).steps ≤
              24 * R * (clause.length + 1) +
                24 * R * (rest.flatten.length + rest.length) := by
            simpa using Nat.add_le_add hfirst hb
          _ = 24 * R * ((clause :: rest).flatten.length + (clause :: rest).length) := by
            simp only [List.flatten_cons, List.length_append, List.length_cons]
            ring

/-- Resetting the evaluator's state makes the formula proof apply to any incoming state. -/
private theorem checkFormula_correct (formula : CNF Variable) (certificate : Certificate)
    (s : TMState machine)
    (htape : s.config.BiTape = cursor [] (tailWord (formulaSymbols formula) certificate)) :
    let size := (tailWord (formulaSymbols formula) certificate).length
    ∃ cost final, Completes checkFormula s cost final ∧
      final.config = ⟨some (resultState (CNF.eval formula (Certificate.assignment certificate))),
        cursor [] (tailWord [formulaEnd] certificate)⟩ ∧
      final.headPos = s.headPos + ((formulaSymbols formula).length - 1 : ℕ) ∧
      cost.steps ≤ 24 * (size + 1) ^ 3 * (formula.flatten.length + formula.length) := by
  let initial : TMState machine := {s with config.state := some (Sum.inr Flag.satisfied)}
  obtain ⟨cost, final, hr, hf, hp, ht⟩ :=
    formulaLoop_correct formula certificate _ initial (by simpa [initial] using htape) le_rfl rfl
  exact ⟨0 + cost, final, (completes_update s (.inr Flag.satisfied)).seq hr, hf, hp,
    by simpa using ht⟩

/--
Starting at the first symbol of an encoded formula-certificate pair on an otherwise blank tape,
`evaluate` finishes with the formula's value under the assignment described by the certificate.
The result is the only symbol left on the tape, and the head rests on it, one cell past the
original input. Missing variable values mean false, and repeated entries use the first value.
For an input of length `n`, the program uses at most `25 * (n + 1) ^ 4` head moves.
-/
theorem evaluate_correct (formula : CNF Variable) (certificate : Certificate)
    (s : TMState machine) :
    let input := verifierEncoding.encode (formula, certificate)
    let value := CNF.eval formula (Certificate.assignment certificate)
    s.config.BiTape = BiTape.mk₁ input →
    ∃ cost final, Completes evaluate s cost final ∧
      final.config.BiTape = BiTape.mk₁ [digit value] ∧
      final.headPos = s.headPos + input.length ∧
      cost.steps ≤ 25 * (input.length + 1) ^ 4 := by
  dsimp only
  intro htape
  let input := tailWord (formulaSymbols formula) certificate
  have hinput : verifierEncoding.encode (formula, certificate) = input :=
    verifierEncoding_symbols formula certificate
  have hinitial : s.config.BiTape = cursor [] input := by
    simpa [hinput, cursor_start] using htape
  obtain ⟨a, middle, hformula, hmiddle, hpos, ha⟩ :=
    checkFormula_correct formula certificate s hinitial
  let n := input.length
  have hmeasure : formula.flatten.length + formula.length ≤ n + 1 := by
    have hlength := formula_length formula
    dsimp [n, input, tailWord]
    simp only [List.length_append, List.length_cons]
    lia
  have hcleanup : (tailWord [formulaEnd] certificate).length ≤ n + 1 := by
    have hlength := formula_length formula
    dsimp [n, input, tailWord]
    simp only [List.length_append, List.length_cons]
    lia
  have hcheck : a.steps ≤ 24 * (n + 1) ^ 4 := by
    calc
      _ ≤ 24 * (n + 1) ^ 3 * (formula.flatten.length + formula.length) := ha
      _ ≤ 24 * (n + 1) ^ 3 * (n + 1) := Nat.mul_le_mul_left _ hmeasure
      _ = 24 * (n + 1) ^ 4 := by ring
  have hpower : n + 1 ≤ (n + 1) ^ 4 := Nat.le_self_pow (by decide) _
  have htotal : a.steps + (tailWord [formulaEnd] certificate).length ≤ 25 * (n + 1) ^ 4 := by
    calc
      _ ≤ 24 * (n + 1) ^ 4 + (n + 1) ^ 4 :=
        Nat.add_le_add hcheck (hcleanup.trans hpower)
      _ = 25 * (n + 1) ^ 4 := by ring
  apply Spec.completes
  vcgen [evaluate, Spec.steps hformula 0,
    eraseRight_spec (tm := machine) (tailWord [formulaEnd] certificate) StackTape.nil
      (some (resultState (CNF.eval formula (Certificate.assignment certificate))))
      (s.headPos + ((formulaSymbols formula).length - 1 : ℕ)) a.steps]
  all_goals
    have hlength := formula_length formula
    cases hv : CNF.eval formula (Certificate.assignment certificate)
    all_goals simp_all [resultState, TMState.write, BiTape.write, BiTape.segment,
      BiTape.nil, BiTape.mk₁, cursor, tailWord, n, input]
    all_goals lia

end Algolean.Algorithms.SingleTapeTuringMachines.SAT.Evaluation
