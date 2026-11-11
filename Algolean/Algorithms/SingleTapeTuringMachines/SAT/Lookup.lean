/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.SAT.Parsing
public import Algolean.Problems.SAT.Verification

/-!
# Looking up a binary variable name in a certificate

The lookup program expects a binary variable name, `nameEnd`, `certificateSeparator`, and an
encoded certificate, in that order. The head starts at the beginning of the name. The certificate
must already be correctly written. The program compares the name with the certificate's names
in their listed order. It uses the first matching value, or false if there is no matching name.

`lookup` has no parameters. Its helpers build instruction blocks for the same machine, using
only Boolean choices and the seven state names below. For example, `lookupLoop` contains both
`checkEntry true` and `checkEntry false`; a test of the certificate's sign selects which block
runs. Both blocks belong to one program. Variable names, certificates, and their lengths are
provided through the tape, and never select a different program.

While comparing two names, the machine temporarily replaces digits it has read: `positiveSign`
stands for a processed zero and `negativeSign` for a processed one. The current certificate
entry's sign is temporarily replaced by `clauseSeparator`, which does not occur in a certificate.
These changes let the machine find its place while moving between the names. It restores every
changed symbol before returning to the start of the query name.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines.SAT.Lookup

open Cslib Cslib.Turing TMQuery Problems.SAT
open scoped TMQuery TMQuery.Spec Std.WP

set_option experimental.vcgen true

/-- These state names record the progress and the result of a variable lookup. -/
inductive State where
  /-- The machine is checking certificate entries until it finds the requested name. -/
  | searching
  /-- The machine is comparing the digits of the query and one certificate name. -/
  | comparing
  /-- The two names just compared are equal. -/
  | equal
  /-- The two names just compared are different. -/
  | different
  /-- This is the truth value returned by the lookup. -/
  | value (result : Bool)
  /-- The machine is moving across or restoring digits that were temporarily changed. -/
  | walking
deriving DecidableEq

instance : Fintype State := .ofList
  [.searching, .comparing, .equal, .different, .value false, .value true, .walking]
  (by
    intro label
    cases label with
    | value result => cases result <;> decide
    | _ => decide)

/--
This machine provides the lookup program's state names. Its transition table preserves the
current symbol and halts; query execution follows the programs defined below. The query compiler
can turn those programs into the transition table of a machine that performs the lookup.
-/
abbrev machine : SingleTapeTM Symbol where
  State := State
  q₀ := .searching
  tr _ symbol := (⟨symbol, none⟩, none)

/-- This temporary replacement remembers a digit's value while recording that it has been read. -/
private def markedDigit (value : Bool) : Symbol := if value then negativeSign else positiveSign

/-- This is the symbol recording a certificate's assigned truth value. -/
private def valueSign (value : Bool) : Symbol := if value then positiveSign else negativeSign

/-- This state records whether the two names just compared were equal. -/
private def comparisonResult (equal : Bool) : State := if equal then .equal else .different

/-- This program optionally restores one digit and then moves right by one cell. -/
private def advanceMarked (restore bit : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  if restore then tape ←ₜ some (digit bit)
  moveₜ .Right

/--
This program moves right across a temporarily replaced digit, restoring it if requested.
On any other symbol it changes the state to `resume` without moving the head.
-/
private def walkMarkedBody (restore : Bool) (resume : State) : Prog (TMQuery machine) Unit :=
    do [TMQuery machine]
  ifₜ tape =ₜ some positiveSign then
    advanceMarked restore false
  else
    ifₜ tape =ₜ some negativeSign then
      advanceMarked restore true
    else
      state ←ₜ resume

/--
While in state `walking`, this program moves right across temporarily replaced digits.
If `restore` is true, it writes each original binary digit back before moving. At the first
other symbol, it stops moving and sets the state to `resume`.
-/
private def walkMarkedLoop (restore : Bool) (resume : State) :
    Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some State.walking) do
    walkMarkedBody restore resume

/--
This program starts `walkMarkedLoop` in state `walking`. It stops on the first symbol that is
not a replaced digit and finishes in state `resume`, which must be different from `walking`.
-/
private def walkMarked (restore : Bool) (resume : State) : Prog (TMQuery machine) Unit :=
    do [TMQuery machine]
  state ←ₜ State.walking
  walkMarkedLoop restore resume

/-- A loop whose state has already changed leaves the machine unchanged. -/
private theorem walkMarkedLoop_finished_spec (restore : Bool) (resume : State)
    (post : Unit → TMCost → TMState machine → Prop) :
    ⦃ fun cost current => current.config.state ≠ some .walking ∧ post () cost current ⦄
      walkMarkedLoop restore resume ⦃ post ⦄ := by
  unfold walkMarkedLoop
  vcgen [Spec.while_false_spec]
  simp_all

/-- The loop restores the replaced digits if requested and stops before the unread name. -/
private theorem walkMarkedLoop_spec (restore : Bool) (resume : State) (bits name : List Bool)
    (left right : List Symbol) (hresume : resume ≠ .walking) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨some .walking, cursor left (bits.map markedDigit ++ name.map digit ++ nameEnd :: right)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      walkMarkedLoop restore resume
    ⦃ fun _ cost final => final.config =
        ⟨some resume, cursor
          ((bits.map (fun b => if restore then digit b else markedDigit b)).reverse ++ left)
          (name.map digit ++ nameEnd :: right)⟩ ∧
        final.headPos = origin + bits.length ∧ cost.steps = elapsed + bits.length ⦄ := by
  induction bits generalizing left origin elapsed with
  | nil =>
    unfold walkMarkedLoop
    vcgen [Spec.while_step_spec (loop := walkMarkedLoop restore resume) (hloop := rfl),
      walkMarkedBody, advanceMarked, walkMarkedLoop_finished_spec]
    all_goals cases name
    all_goals simp_all [positiveSign, negativeSign, digit, nameEnd]
  | cons bit bits ih =>
    unfold walkMarkedLoop
    vcgen [Spec.while_step_spec (loop := walkMarkedLoop restore resume) (hloop := rfl),
      walkMarkedBody, advanceMarked,
      ih ((if restore then digit bit else markedDigit bit) :: left) (origin + 1) (elapsed + 1)]
    all_goals cases bit
    all_goals cases restore
    all_goals simp_all [markedDigit, positiveSign, negativeSign, TMState.move, TMState.moveCost,
      TMState.write, List.reverse_cons, List.append_assoc, add_assoc]
    all_goals lia

/--
Starting inside the query name, this program finds the certificate separator and then the
temporarily replaced sign of the certificate entry being compared. It moves past that sign
and past the replaced digits of the entry, stopping on its next unread digit or its name ending.
-/
private def toCandidate : Prog (TMQuery machine) Unit := do [TMQuery machine]
  seekRightSymbol machine certificateSeparator
  moveₜ .Right
  seekRightSymbol machine clauseSeparator
  moveₜ .Right
  walkMarked false .comparing

/--
Starting at a certificate name, this program returns to the query name at the beginning of the
occupied tape. It passes its replaced digits and stops on the next unread digit or name ending.
-/
private def toQuery : Prog (TMQuery machine) Unit := do [TMQuery machine]
  seekLeftEnd machine
  walkMarked false .comparing

/--
With the comparison result already recorded in the state, this program restores both names
and the certificate entry's original sign. It stops immediately after that entry's name ending.
`value` is the original
truth value of that entry. The head initially lies on its first unread digit or name ending.
-/
private def restoreNames (equal value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  seekLeftEnd machine
  walkMarked true (comparisonResult equal)
  seekRightSymbol machine certificateSeparator
  moveₜ .Right
  seekRightSymbol machine clauseSeparator
  tape ←ₜ some (valueSign value)
  moveₜ .Right
  walkMarked true (comparisonResult equal)
  seekRightSymbol machine nameEnd
  moveₜ .Right

/-- This program records whether the names match, then restores them with `restoreNames`. -/
private def finishComparison (equal value : Bool) : Prog (TMQuery machine) Unit :=
    do [TMQuery machine]
  state ←ₜ comparisonResult equal
  restoreNames equal value

/--
With the head on query digit `bit`, this program replaces that digit and finds the next unread
certificate digit. If the digits match, it replaces that digit too and returns to the query.
Otherwise it restores both names and records that they differ.
-/
private def compareDigit (bit value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  tape ←ₜ some (markedDigit bit)
  moveₜ .Right
  toCandidate
  ifₜ tape =ₜ some (digit bit) then
    tape ←ₜ some (markedDigit bit)
    moveₜ .Right
    toQuery
  else
    finishComparison false value

/--
This compares the next unread query digit with the next unread certificate digit. A matching
pair is marked as read, and the head returns to the next query digit. If the query has ended,
the candidate must end there too. A mismatch or a pair of matching endings finishes the
comparison, restores both names, and records `equal` or `different` after the certificate entry.
-/
private def compareBody (value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ tape =ₜ some (digit false) then
    compareDigit false value
  else
    ifₜ tape =ₜ some (digit true) then
      compareDigit true value
    else
      toCandidate
      ifₜ tape =ₜ some nameEnd then
        finishComparison true value
      else
        finishComparison false value

/-- This loop repeats the digit comparisons until they record equal or different names. -/
private def compareLoop (value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some State.comparing) do
    compareBody value

/-- This program begins comparing names at the first query digit, or at its ending if empty. -/
private def compareNames (value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  state ←ₜ State.comparing
  compareLoop value

/--
Starting at an entry's sign, this program temporarily replaces that sign with `clauseSeparator`
and returns to the query name to compare it with the entry. It returns the entry's value when
the names match, and otherwise sets state `searching` so that the next entry will be checked.
-/
private def checkEntry (value : Bool) : Prog (TMQuery machine) Unit := do [TMQuery machine]
  tape ←ₜ some clauseSeparator
  seekLeftEnd machine
  compareNames value
  ifₜ state =ₜ some State.equal then
    state ←ₜ State.value value
  else
    state ←ₜ State.searching

/--
This checks one certificate entry, or returns false if the head is on the certificate's ending.
A matching name records that entry's value. A different name leaves state `searching` and the
head at the next entry. The comparison restores the checked entry before returning.
-/
private def lookupBody : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ tape =ₜ some clauseEnd then
    state ←ₜ State.value false
  else
    ifₜ tape =ₜ some positiveSign then
      checkEntry true
    else
      checkEntry false

/-- This loop continues checking entries while the state says the name has not been found. -/
private def lookupLoop : Prog (TMQuery machine) Unit := do [TMQuery machine]
  whileₜ (state =ₜ some State.searching) do
    lookupBody

/--
This program looks up the binary name at the start of the tape in the certificate that follows
`nameEnd` and `certificateSeparator`. It returns to that starting cell with all tape symbols
restored. State `value true` or `value false` records the first listed value for that name;
an absent name receives false. The certificate must be correctly written before this is called.
This is one fixed program for all query names and certificates; both are provided on the tape.
-/
def lookup : Prog (TMQuery machine) Unit := do [TMQuery machine]
  seekRightSymbol machine certificateSeparator
  moveₜ .Right
  state ←ₜ State.searching
  lookupLoop
  seekLeftEnd machine

/--
This describes the tape while the head is at the next query digit. The two lists ending in
`Read` describe replaced digits; the two lists ending in `Rest` describe unread binary digits.
`earlier` contains the certificate entries before the one being compared. These lists describe
an execution for the proof and are not arguments to the Turing machine program.
-/
private def queryTape (between : List Symbol) (queryRead queryRest : List Bool)
    (earlier : List Symbol) (candidateRead candidateRest : List Bool)
    (suffix : List Symbol) : BiTape Symbol :=
  cursor (queryRead.map markedDigit).reverse
    (queryRest.map digit ++ nameEnd :: between ++ certificateSeparator :: earlier ++
      clauseSeparator :: candidateRead.map markedDigit ++ candidateRest.map digit ++
        nameEnd :: suffix)

/--
This is the same comparison tape with the head at the next unread certificate digit.
The description records which digits have been temporarily replaced on each side.
-/
private def candidateTape (between : List Symbol) (queryRead queryRest : List Bool)
    (earlier : List Symbol) (candidateRead candidateRest : List Bool)
    (suffix : List Symbol) :=
  cursor (queryRead.map markedDigit ++ queryRest.map digit ++ (nameEnd :: between ++
      [certificateSeparator]) ++
    earlier ++ clauseSeparator :: candidateRead.map markedDigit).reverse
      (candidateRest.map digit ++ nameEnd :: suffix)

/-- Crossing replaced digits preserves the state and records the exact head moves. -/
private theorem walkMarked_name_spec (restore : Bool) (resume : State) (bits name : List Bool)
    (left right : List Symbol) (hresume : resume ≠ .walking) (origin : ℤ) (elapsed : Nat) :
    ⦃ fun cost current => current.config =
        ⟨some resume, cursor left (bits.map markedDigit ++ name.map digit ++ nameEnd :: right)⟩ ∧
        current.headPos = origin ∧ cost.steps = elapsed ⦄
      walkMarked restore resume
    ⦃ fun _ cost final => final.config =
        ⟨some resume, cursor
          ((bits.map (fun b => if restore then digit b else markedDigit b)).reverse ++ left)
          (name.map digit ++ nameEnd :: right)⟩ ∧
        final.headPos = origin + bits.length ∧ cost.steps = elapsed + bits.length ⦄ := by
  vcgen [walkMarked, walkMarkedLoop_spec restore resume bits name left right hresume origin elapsed]
  all_goals simp_all

/--
Moving from the next query digit to the next candidate digit preserves the state and tape.
The crossed entries must not contain `clauseSeparator`, so its temporary occurrence identifies
exactly the candidate being compared.
-/
private theorem toCandidate_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (queryRead queryRest : List Bool)
    (earlier : List Symbol)
    (candidateRead candidateRest : List Bool) (suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      queryTape between queryRead queryRest earlier candidateRead candidateRest suffix)
    (hstate : s.config.state = some .comparing) :
    let distance := queryRest.length + (between.length + earlier.length) + candidateRead.length + 3
    Runs toCandidate s
      (candidateTape between queryRead queryRest earlier candidateRead candidateRest suffix)
      (s.headPos + distance) distance := by
  dsimp only
  have hbetween' : certificateSeparator ∉ queryRest.map digit ++ nameEnd :: between := by
    simpa [List.mem_map, digit, certificateSeparator, nameEnd] using hbetween
  let left := (queryRest.map digit ++ nameEnd :: between).reverse ++
    (queryRead.map markedDigit).reverse
  apply Spec.runs
  vcgen [toCandidate,
    seekRightSymbol_spec (tm := machine) certificateSeparator
      (queryRead.map markedDigit).reverse (queryRest.map digit ++ nameEnd :: between)
      (earlier ++ clauseSeparator :: candidateRead.map markedDigit ++
        candidateRest.map digit ++ nameEnd :: suffix) hbetween' (some .comparing) s.headPos 0,
    seekRightSymbol_spec (tm := machine) clauseSeparator (certificateSeparator :: left) earlier
      (candidateRead.map markedDigit ++ candidateRest.map digit ++ nameEnd :: suffix)
      hearlier (some .comparing)
      (s.headPos + (queryRest.map digit ++ nameEnd :: between).length + 1)
      ((queryRest.map digit ++ nameEnd :: between).length + 1),
    walkMarked_name_spec false .comparing candidateRead candidateRest
      (clauseSeparator :: earlier.reverse ++ certificateSeparator :: left) suffix (by decide)
      (s.headPos + (queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1)
      ((queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1)]
  all_goals cases hcfg : s.config
  all_goals simp_all [queryTape, candidateTape, left, TMState.move, TMState.moveCost,
    List.reverse_append, List.reverse_cons, List.append_assoc]
  all_goals lia

/--
Returning from the next candidate digit stops on the next query digit. It preserves both names
and the comparison state; the extra moves come from passing the already read query digits twice.
-/
private theorem toQuery_correct (between : List Symbol) (queryRead queryRest : List Bool)
    (earlier : List Symbol)
    (candidateRead candidateRest : List Bool) (suffix : List Symbol) (s : TMState machine)
    (htape : s.config.BiTape =
      candidateTape between queryRead queryRest earlier candidateRead candidateRest suffix)
    (hstate : s.config.state = some .comparing) :
    let distance := queryRest.length + (between.length + earlier.length) + candidateRead.length + 3
    Runs toQuery s (queryTape between queryRead queryRest earlier candidateRead candidateRest
      suffix)
      (s.headPos - distance) (distance + 2 * queryRead.length + 2) := by
  dsimp only
  let left := (queryRead.map markedDigit ++ queryRest.map digit ++
    (nameEnd :: between ++ [certificateSeparator]) ++ earlier ++
      clauseSeparator :: candidateRead.map markedDigit).reverse
  apply Spec.runs
  vcgen [toQuery,
    seekLeftEnd_spec (tm := machine) left (candidateRest.map digit ++ nameEnd :: suffix)
      (some .comparing) s.headPos 0,
    walkMarked_name_spec false .comparing queryRead queryRest []
      (between ++ certificateSeparator :: earlier ++ clauseSeparator :: candidateRead.map
        markedDigit ++ candidateRest.map digit ++ nameEnd :: suffix) (by decide)
      (s.headPos - left.length) (left.length + 2)]
  all_goals cases hcfg : s.config
  all_goals simp_all [candidateTape, queryTape, left, List.reverse_append,
    List.reverse_cons, List.append_assoc]
  all_goals lia

/--
This describes the restored tape just after one certificate entry. Both names are ordinary binary
names again, and `value` determines the restored certificate sign. It is a tape description for
proofs, not a program that receives these names as arguments.
-/
private def entryEndTape (between : List Symbol) (query : Variable) (earlier : List Symbol)
    (value : Bool)
    (candidate : Variable) (suffix : List Symbol) : BiTape Symbol :=
  cursor (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++ earlier ++
    valueSign value :: candidate.map digit ++ [nameEnd]).reverse suffix

/--
Restoring a comparison returns both names and the entry's sign to their original symbols.
The head finishes immediately after that entry. The state recording the comparison result
is preserved, and the stated move count includes returning to the query and reading right again.
-/
private theorem restoreNames_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (equal value : Bool)
    (queryRead queryRest : List Bool)
    (earlier : List Symbol) (candidateRead candidateRest : List Bool) (suffix : List Symbol)
    (s : TMState machine) (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      candidateTape between queryRead queryRest earlier candidateRead candidateRest suffix)
    (hstate : s.config.state = some (comparisonResult equal)) :
    Runs (restoreNames equal value) s
      (entryEndTape between (queryRead ++ queryRest) earlier value (candidateRead ++
        candidateRest) suffix)
      (s.headPos + candidateRest.length + 1)
      (2 * (queryRead.length + queryRest.length + (between.length + earlier.length) +
        candidateRead.length) +
        candidateRest.length + 9) := by
  have hresume : comparisonResult equal ≠ .walking := by cases equal <;> decide
  have hbetween' : certificateSeparator ∉ queryRest.map digit ++ nameEnd :: between := by
    simpa [List.mem_map, digit, certificateSeparator, nameEnd] using hbetween
  let left := (queryRead.map markedDigit ++ queryRest.map digit ++
    (nameEnd :: between ++ [certificateSeparator]) ++ earlier ++
      clauseSeparator :: candidateRead.map markedDigit).reverse
  let rest := between ++ certificateSeparator :: earlier ++ clauseSeparator ::
    candidateRead.map markedDigit ++ candidateRest.map digit ++ nameEnd :: suffix
  let afterQuery := (queryRest.map digit ++ nameEnd :: between).reverse ++
    (queryRead.map digit).reverse
  apply Spec.runs
  unfold restoreNames
  rw [← bind_assoc]
  apply Std.WP.Triple.bind (mid := fun _ cost current => current.config =
    ⟨some (comparisonResult equal), cursor (queryRead.map digit).reverse
      (queryRest.map digit ++ nameEnd :: rest)⟩ ∧
    current.headPos = s.headPos - left.length + queryRead.length ∧
    cost.steps = left.length + 2 + queryRead.length)
  · vcgen [seekLeftEnd_spec (tm := machine) left
        (candidateRest.map digit ++ nameEnd :: suffix)
        (some (comparisonResult equal)) s.headPos 0,
      walkMarked_name_spec true (comparisonResult equal) queryRead queryRest [] rest hresume
        (s.headPos - left.length) (left.length + 2)]
    all_goals cases hcfg : s.config
    all_goals simp_all [candidateTape, left, rest, List.reverse_append,
      List.reverse_cons, List.append_assoc]
  · intro _
    vcgen [seekRightSymbol_spec (tm := machine) certificateSeparator
        (queryRead.map digit).reverse (queryRest.map digit ++ nameEnd :: between)
        (earlier ++ clauseSeparator :: candidateRead.map markedDigit ++
          candidateRest.map digit ++ nameEnd :: suffix) hbetween'
        (some (comparisonResult equal))
        (s.headPos - left.length + queryRead.length) (left.length + 2 + queryRead.length),
      seekRightSymbol_spec (tm := machine) clauseSeparator
        (certificateSeparator :: afterQuery) earlier
        (candidateRead.map markedDigit ++ candidateRest.map digit ++ nameEnd :: suffix)
        hearlier (some (comparisonResult equal))
        (s.headPos - left.length + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1)
        (left.length + 2 + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1),
      walkMarked_name_spec true (comparisonResult equal) candidateRead candidateRest
        (valueSign value :: earlier.reverse ++ certificateSeparator :: afterQuery) suffix hresume
        (s.headPos - left.length + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1)
        (left.length + 2 + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1),
      seekRightSymbol_spec (tm := machine) nameEnd
        ((candidateRead.map digit).reverse ++ valueSign value :: earlier.reverse ++
          certificateSeparator :: afterQuery) (candidateRest.map digit) suffix
        (by simp [List.mem_map, digit, nameEnd]) (some (comparisonResult equal))
        (s.headPos - left.length + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1 +
          candidateRead.length)
        (left.length + 2 + queryRead.length +
          (queryRest.map digit ++ nameEnd :: between).length + 1 + earlier.length + 1 +
          candidateRead.length)]
    all_goals simp_all [rest, afterQuery, left, entryEndTape, TMState.move, TMState.moveCost,
      TMState.write, List.map_append, List.reverse_append, List.reverse_cons,
      List.append_assoc]
    all_goals lia

/--
Finishing a comparison records its Boolean result, restores the complete tape, and stops after
the certificate entry. The move count is the same as for `restoreNames`, since setting the state
uses no head moves.
-/
private theorem finishComparison_correct (between : List Symbol) (hbetween :
    certificateSeparator ∉ between) (equal value : Bool) (queryRead queryRest : List Bool)
    (earlier : List Symbol) (candidateRead candidateRest : List Bool) (suffix : List Symbol)
    (s : TMState machine) (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      candidateTape between queryRead queryRest earlier candidateRead candidateRest suffix) :
    ∃ cost final, Completes (finishComparison equal value) s cost final ∧
      final.config = ⟨some (comparisonResult equal),
        entryEndTape between (queryRead ++ queryRest) earlier value
          (candidateRead ++ candidateRest) suffix⟩ ∧
      final.headPos = s.headPos + candidateRest.length + 1 ∧
      cost.steps = 2 * (queryRead.length + queryRest.length + (between.length + earlier.length) +
        candidateRead.length) + candidateRest.length + 9 := by
  let initial : TMState machine := {s with config.state := some (comparisonResult equal)}
  obtain ⟨cost, final, hr, hfinal, hpos, hsteps⟩ :=
    restoreNames_correct between hbetween equal value queryRead queryRest earlier candidateRead
      candidateRest suffix
      initial hearlier (by simpa [initial] using htape) rfl
  exact ⟨0 + cost, final, (completes_update s _).seq hr, hfinal, hpos, by simpa using hsteps⟩

/-- Replacing the next query digit and moving right makes that digit part of the read prefix. -/
private theorem markQuery_correct (between : List Symbol) (bit : Bool) (seen queryRest
    candidateRest : List Bool)
    (earlier suffix : List Symbol) (s : TMState machine)
    (htape : s.config.BiTape =
      queryTape between seen (bit :: queryRest) earlier seen candidateRest suffix) :
    Runs (do FreeM.lift (.write (some (markedDigit bit))); FreeM.lift (.move .Right)) s
      (queryTape between (seen ++ [bit]) queryRest earlier seen candidateRest suffix)
      (s.headPos + 1) 1 := by
  apply Spec.runs
  vcgen
  simp_all [queryTape, TMState.move, TMState.moveCost, TMState.write,
    List.map_append, List.reverse_append]

/--
If the next digits match, comparing them restores neither yet: it marks both as read and returns
to the next query digit in state `comparing`. All other tape symbols are unchanged.
-/
private theorem compareDigit_match (between : List Symbol) (hbetween : certificateSeparator ∉
    between) (bit value : Bool) (seen queryRest candidateRest : List Bool)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      queryTape between seen (bit :: queryRest) earlier seen (bit :: candidateRest) suffix)
    (hstate : s.config.state = some .comparing) :
    Runs (compareDigit bit value) s
      (queryTape between (seen ++ [bit]) queryRest earlier (seen ++ [bit]) candidateRest suffix)
      (s.headPos + 1) (4 * seen.length + 2 * queryRest.length + 2 * (between.length +
        earlier.length) + 13) := by
  have hmark := markQuery_correct between bit seen queryRest (bit :: candidateRest) earlier
      suffix s htape
  have hthere := hmark.seq (q := toCandidate) (by
    intro middle hmiddle hpos
    have h := toCandidate_correct between hbetween (seen ++ [bit]) queryRest earlier seen (bit
      :: candidateRest)
      suffix middle hearlier (by simp [hmiddle]) (by simp [hmiddle, hstate])
    simpa [hpos] using h)
  have hback := hthere.seq (q := branch (.tapeIs (some (digit bit)))
      (do FreeM.lift (.write (some (markedDigit bit))); FreeM.lift (.move .Right); toQuery)
      (finishComparison false value)) (by
    intro middle hmiddle hpos
    have htarget : Runs
        (do FreeM.lift (.write (some (markedDigit bit))); FreeM.lift (.move .Right)) middle
        (candidateTape between (seen ++ [bit]) queryRest earlier (seen ++ [bit]) candidateRest
          suffix)
        (middle.headPos + 1) 1 := by
      apply Spec.runs
      vcgen
      simp_all [candidateTape, TMState.move, TMState.moveCost, TMState.write,
        List.map_append, List.reverse_append, List.append_assoc]
    have hreturn := htarget.seq (q := toQuery) (by
      intro final hfinal hfinalPos
      have h := toQuery_correct between (seen ++ [bit]) queryRest earlier (seen ++ [bit])
        candidateRest
        suffix final (by simp [hfinal]) (by simp [hfinal, hmiddle, hstate])
      simpa [hfinalPos] using h)
    have hbranch : Runs (branch (.tapeIs (some (digit bit)))
        (do FreeM.lift (.write (some (markedDigit bit))); FreeM.lift (.move .Right); toQuery)
        (finishComparison false value)) middle _ _ _ :=
      Runs.branch (by simpa [hmiddle, candidateTape] using hreturn)
    simpa [hpos] using hbranch)
  convert hback using 1 <;>
    (try simp only [compareDigit, bind_assoc]) <;> lia

/--
If the certificate name ends early or its next digit differs, comparing the query digit restores
both full names and finishes after the certificate entry in state `different`.
-/
private theorem compareDigit_mismatch (between : List Symbol) (hbetween : certificateSeparator ∉
    between) (bit value : Bool) (seen queryRest candidateRest : List Bool)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier) (hdifferent : candidateRest.head? ≠ some bit)
    (htape : s.config.BiTape =
      queryTape between seen (bit :: queryRest) earlier seen candidateRest suffix)
    (hstate : s.config.state = some .comparing) :
    ∃ cost final, Completes (compareDigit bit value) s cost final ∧
      final.config = ⟨some .different,
        entryEndTape between (seen ++ bit :: queryRest) earlier value (seen ++ candidateRest)
          suffix⟩ ∧
      final.headPos = s.headPos + queryRest.length + (between.length + earlier.length) +
        seen.length +
        candidateRest.length + 5 ∧
      cost.steps = 5 * seen.length + 3 * queryRest.length + 3 * (between.length + earlier.length) +
        candidateRest.length + 15 := by
  have hmark := markQuery_correct between bit seen queryRest candidateRest earlier suffix s htape
  have hthere := hmark.seq (q := toCandidate) (by
    intro middle hmiddle hpos
    have h := toCandidate_correct between hbetween (seen ++ [bit]) queryRest earlier seen
      candidateRest suffix
      middle hearlier (by simp [hmiddle]) (by simp [hmiddle, hstate])
    simpa [hpos] using h)
  obtain ⟨a, middle, hpre, hmiddle, hpos, ha⟩ := hthere
  obtain ⟨b, final, hfinish, hfinal, hfinalPos, hb⟩ :=
    finishComparison_correct between hbetween false value (seen ++ [bit]) queryRest earlier seen
      candidateRest
      suffix middle hearlier (by simp [hmiddle])
  have hhead : middle.config.BiTape.head ≠ some (digit bit) := by
    cases candidateRest with
    | nil => simp [hmiddle, candidateTape, nameEnd, digit]
    | cons other rest =>
      have hne : other ≠ bit := by simpa using hdifferent
      simp [hmiddle, candidateTape, digit, hne]
  have hbranch : Completes (branch (.tapeIs (some (digit bit)))
      (do FreeM.lift (.write (some (markedDigit bit))); FreeM.lift (.move .Right); toQuery)
      (finishComparison false value)) middle b final :=
    Completes.branch (by simpa [hhead] using hfinish)
  refine ⟨a + b, final, ?_, ?_, ?_, ?_⟩
  · simpa [compareDigit] using hpre.seq hbranch
  · simpa [comparisonResult, List.append_assoc] using hfinal
  · rw [hfinalPos, hpos]
    lia
  · simp only [TMCost.add_steps, ha]
    simp only [List.length_append, List.length_singleton] at hb
    lia

/-- The first query digit selects the instructions comparing that digit. -/
private theorem compareBody_digit (bit value : Bool) (s final : TMState machine) (cost : TMCost)
    (hhead : s.config.BiTape.head = some (digit bit))
    (h : Completes (compareDigit bit value) s cost final) :
    Completes (compareBody value) s cost final := by
  unfold compareBody
  apply Completes.branch
  cases bit with
  | false => simpa [hhead] using h
  | true =>
    rw [ite_eq_right (show ¬((TMCondition.tapeIs (some (digit false)) : TMCondition machine).eval
      s.config = true) by simp [hhead, digit])]
    apply Completes.branch
    simpa [hhead, digit] using h

/-- When the query name has ended, the body checks that the candidate name ends there too. -/
private theorem compareBody_end (between : List Symbol) (hbetween : certificateSeparator ∉
    between) (value : Bool) (seen candidateRest : List Bool)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape = queryTape between seen [] earlier seen candidateRest suffix)
    (hstate : s.config.state = some .comparing) :
    ∃ cost final, Completes (compareBody value) s cost final ∧
      final.config = ⟨some (comparisonResult (decide (candidateRest = []))),
        entryEndTape between seen earlier value (seen ++ candidateRest) suffix⟩ ∧
      final.headPos = s.headPos + (between.length + earlier.length) + seen.length +
        candidateRest.length + 4 ∧
      cost.steps = 5 * seen.length + 3 * (between.length + earlier.length) +
        candidateRest.length + 12 := by
  obtain ⟨a, middle, hpre, hmiddle, hpos, ha⟩ :=
    toCandidate_correct between hbetween seen [] earlier seen candidateRest suffix s hearlier
      htape hstate
  obtain ⟨b, final, hfinish, hfinal, hfinalPos, hb⟩ :=
    finishComparison_correct between hbetween (decide (candidateRest = [])) value seen []
      earlier seen candidateRest
      suffix middle hearlier (by simp [hmiddle])
  have hbranch : Completes (branch (.tapeIs (some nameEnd)) (finishComparison true value)
      (finishComparison false value)) middle b final := by
    apply Completes.branch
    cases candidateRest with
    | nil => simpa [hmiddle, candidateTape] using hfinish
    | cons bit rest => simpa [hmiddle, candidateTape, digit, nameEnd] using hfinish
  have hselected := hpre.seq hbranch
  have hbody : Completes (compareBody value) s (a + b) final := by
    unfold compareBody
    apply Completes.branch
    rw [ite_eq_right (show ¬((TMCondition.tapeIs (some (digit false)) : TMCondition machine).eval
      s.config = true) by simp [htape, queryTape, nameEnd, digit])]
    apply Completes.branch
    simpa [htape, queryTape, nameEnd, digit] using hselected
  refine ⟨a + b, final, hbody, by simpa using hfinal, ?_, ?_⟩
  · rw [hfinalPos, hpos]
    simp only [List.length_nil]
    lia
  · simp only [TMCost.add_steps, ha, List.length_nil]
    simp only [List.length_nil] at hb
    lia

/-- Once the body records a result other than `comparing`, the comparison loop finishes. -/
private theorem compareLoop_done (value : Bool) (s final : TMState machine) (cost : TMCost)
    (hstate : s.config.state = some .comparing)
    (hbody : Completes (compareBody value) s cost final)
    (hfinal : final.config.state ≠ some .comparing) :
    Completes (compareLoop value) s cost final := by
  have hend := completes_while_false (.stateIs (some State.comparing)) (compareBody value) final
    (by simp [hfinal])
  simpa [compareLoop] using Completes.while_step (by simp [hstate]) hbody hend

/--
Comparing the unread parts of two names decides their equality and restores both whole names.
The bound counts all moves between the two names, including the moves needed to restore them.
The lists in this theorem describe the tape; the program itself only receives the tape.
-/
private theorem compareLoop_correct (between : List Symbol) (hbetween : certificateSeparator ∉
    between) (value : Bool) (seen query candidate : List Bool)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape = queryTape between seen query earlier seen candidate suffix)
    (hstate : s.config.state = some .comparing) :
    let K := 16 * (2 * seen.length + query.length + candidate.length +
      (between.length + earlier.length) + suffix.length + 5)
    ∃ cost final, Completes (compareLoop value) s cost final ∧
      final.config = ⟨some (comparisonResult (decide (query = candidate))),
        entryEndTape between (seen ++ query) earlier value (seen ++ candidate) suffix⟩ ∧
      final.headPos = s.headPos + query.length + (between.length + earlier.length) + seen.length +
        candidate.length + 4 ∧ cost.steps ≤ K * (query.length + 1) := by
  induction query generalizing seen candidate s with
  | nil =>
    obtain ⟨cost, final, hb, hf, hp, ht⟩ :=
      compareBody_end between hbetween value seen candidate earlier suffix s hearlier htape hstate
    have hn : final.config.state ≠ some State.comparing := by
      by_cases h : candidate = [] <;> simp [hf, comparisonResult, h]
    refine ⟨cost, final, compareLoop_done value s final cost hstate hb hn, ?_, ?_, ?_⟩
    · simpa [eq_comm] using hf
    · simpa using hp
    · simp only [List.length_nil, zero_add, mul_one]
      rw [ht]
      lia
  | cons bit query ih =>
    by_cases hhead : candidate.head? = some bit
    · cases candidate with
      | nil => simp at hhead
      | cons other candidate =>
        have heq : other = bit := by simpa using hhead
        subst other
        obtain ⟨a, middle, hstep, hmiddle, hpos, ha⟩ :=
          compareDigit_match between hbetween bit value seen query candidate earlier suffix s
            hearlier htape hstate
        have hb := compareBody_digit bit value s middle a (by simp [htape, queryTape]) hstep
        obtain ⟨b, final, hr, hf, hp, hbound⟩ :=
          ih (seen ++ [bit]) candidate middle (by simp [hmiddle]) (by simp [hmiddle, hstate])
        refine ⟨a + b, final, Completes.while_step (by simp [hstate]) hb hr, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hf
        · simp only [List.length_append, List.length_singleton] at hp
          rw [hp, hpos]
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          lia
        · let K := 16 * (2 * seen.length + (bit :: query).length +
            (bit :: candidate).length + (between.length + earlier.length) + suffix.length + 5)
          have hfirst : a.steps ≤ K := by
            rw [ha]
            dsimp [K]
            lia
          have hrest : b.steps ≤ K * (query.length + 1) := by
            convert hbound using 1
            simp only [K, List.length_append, List.length_cons, List.length_nil]
            ring
          change a.steps + b.steps ≤ K * ((bit :: query).length + 1)
          calc
            a.steps + b.steps ≤ K + K * (query.length + 1) := Nat.add_le_add hfirst hrest
            _ = K * ((bit :: query).length + 1) := by simp only [List.length_cons]; ring
    · obtain ⟨cost, final, hd, hf, hp, ht⟩ :=
        compareDigit_mismatch between hbetween bit value seen query candidate earlier suffix s
          hearlier hhead
          htape hstate
      have hne : bit :: query ≠ candidate := by
        rintro rfl
        exact hhead rfl
      have hb := compareBody_digit bit value s final cost (by simp [htape, queryTape]) hd
      have hn : final.config.state ≠ some State.comparing := by simp [hf]
      refine ⟨cost, final, compareLoop_done value s final cost hstate hb hn, ?_, ?_, ?_⟩
      · simpa [hne, comparisonResult] using hf
      · simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hp]
        lia
      · let K := 16 * (2 * seen.length + (bit :: query).length + candidate.length +
          (between.length + earlier.length) + suffix.length + 5)
        have hcost : cost.steps ≤ K := by
          rw [ht]
          dsimp [K]
          lia
        exact hcost.trans (by
          change K ≤ K * ((bit :: query).length + 1)
          simpa using Nat.mul_le_mul_left K (show 1 ≤ (bit :: query).length + 1 by simp))

/--
Starting a comparison with no replaced digits decides equality and restores the original names.
-/
private theorem compareNames_correct (between : List Symbol) (hbetween : certificateSeparator ∉
    between) (value : Bool) (query candidate : Variable)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape = queryTape between [] query earlier [] candidate suffix) :
    ∃ cost final, Completes (compareNames value) s cost final ∧
      final.config = ⟨some (comparisonResult (decide (query = candidate))),
        entryEndTape between query earlier value candidate suffix⟩ ∧
      final.headPos = s.headPos + query.length + (between.length + earlier.length) +
        candidate.length + 4 ∧
      cost.steps ≤ 16 * (query.length + candidate.length + (between.length + earlier.length) +
        suffix.length + 5) *
        (query.length + 1) := by
  let initial : TMState machine := {s with config.state := some State.comparing}
  obtain ⟨cost, final, hr, hf, hp, ht⟩ :=
    compareLoop_correct between hbetween value [] query candidate earlier suffix initial hearlier
      (by simpa [initial] using htape) rfl
  refine ⟨0 + cost, final, (completes_update s .comparing).seq hr, ?_, ?_, ?_⟩
  · simpa using hf
  · simpa [initial] using hp
  · simpa using ht

/--
Checking one entry restores it and either returns its value or continues the search. Its sign
is remembered by the Boolean `value`, which is selected by the tape test in `lookupBody`.
-/
private theorem checkEntry_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (value : Bool) (query candidate : Variable)
    (earlier suffix : List Symbol) (s : TMState machine)
    (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      cursor (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++ earlier).reverse
        (valueSign value :: candidate.map digit ++ nameEnd :: suffix)) :
    ∃ cost final, Completes (checkEntry value) s cost final ∧
      final.config = ⟨some (if query = candidate then State.value value else .searching),
        entryEndTape between query earlier value candidate suffix⟩ ∧
      final.headPos = s.headPos + candidate.length + 2 ∧
      cost.steps ≤ 17 * (query.length + candidate.length + (between.length + earlier.length) +
        suffix.length + 5) *
        (query.length + 1) := by
  let left := (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++
    earlier).reverse
  have hstart : Runs (do [TMQuery machine]
      tape ←ₜ some clauseSeparator
      seekLeftEnd machine) s
      (cursor [] (left.reverse ++ clauseSeparator :: candidate.map digit ++ nameEnd :: suffix))
      (s.headPos - left.length) (left.length + 2) := by
    apply Spec.runs
    vcgen [seekLeftEnd_spec (tm := machine) left
      (clauseSeparator :: candidate.map digit ++ nameEnd :: suffix)
      s.config.state s.headPos 0]
    all_goals cases hcfg : s.config
    all_goals simp_all [left, TMState.write]
  obtain ⟨a, initial, hpre, hinitial, hstartPos, ha⟩ := hstart
  obtain ⟨b, middle, hcompare, hmiddle, hpos, hb⟩ :=
    compareNames_correct between hbetween value query candidate earlier suffix initial hearlier
      (by simpa [queryTape, left, List.append_assoc] using
        congrArg SingleTapeTM.Cfg.BiTape hinitial)
  let result := if query = candidate then State.value value else .searching
  let final : TMState machine := {middle with config.state := some result}
  have hbranch : Completes (branch (.stateIs (some State.equal))
      (FreeM.lift (.update (State.value value))) (FreeM.lift (.update State.searching)))
      middle 0 final := by
    apply Completes.branch
    by_cases heq : query = candidate
    · simpa [hmiddle, comparisonResult, heq, final, result] using
        completes_update middle (.value value)
    · simpa [hmiddle, comparisonResult, heq, final, result] using
        completes_update middle .searching
  refine ⟨a + b + 0, final, ?_, ?_, ?_, ?_⟩
  · simpa [checkEntry] using (hpre.seq hcompare).seq hbranch
  · simp [final, hmiddle, result]
  · change middle.headPos = _
    rw [hpos, hstartPos]
    simp only [left, List.length_reverse, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
    lia
  · let W := query.length + candidate.length + (between.length + earlier.length) + suffix.length + 5
    have hpreBound : a.steps ≤ W := by
      rw [ha]
      dsimp [W, left]
      simp only [List.length_reverse, List.length_append, List.length_map, List.length_cons,
        List.length_nil]
      lia
    have hfirst : a.steps ≤ W * (query.length + 1) := hpreBound.trans (by
      simpa using Nat.mul_le_mul_left W (show 1 ≤ query.length + 1 by simp))
    change a.steps + b.steps + 0 ≤ 17 * W * (query.length + 1)
    calc
      a.steps + b.steps + 0 ≤ W * (query.length + 1) + 16 * W * (query.length + 1) := by
        simpa using Nat.add_le_add hfirst hb
      _ = 17 * W * (query.length + 1) := by ring

/-- A certificate sign selects the instructions for checking the entry with that truth value. -/
private theorem lookupBody_entry (value : Bool) (s final : TMState machine) (cost : TMCost)
    (hhead : s.config.BiTape.head = some (valueSign value))
    (h : Completes (checkEntry value) s cost final) :
    Completes lookupBody s cost final := by
  unfold lookupBody
  apply Completes.branch
  cases value with
  | false =>
    rw [ite_eq_right (show ¬((TMCondition.tapeIs (some clauseEnd) : TMCondition machine).eval
      s.config = true) by simp [hhead, valueSign, clauseEnd, negativeSign])]
    apply Completes.branch
    simpa [hhead, valueSign, negativeSign, positiveSign] using h
  | true =>
    rw [ite_eq_right (show ¬((TMCondition.tapeIs (some clauseEnd) : TMCondition machine).eval
      s.config = true) by simp [hhead, valueSign, clauseEnd, positiveSign])]
    apply Completes.branch
    simpa [hhead, valueSign, positiveSign] using h

/-- Every certificate entry uses at least two symbols, and one final symbol ends the certificate. -/
private theorem certificate_length_le (certificate : Certificate) :
    2 * certificate.length + 1 ≤ (certificateSymbols certificate).length := by
  induction certificate with
  | nil => simp [certificateSymbols_nil]
  | cons literal rest ih =>
    cases literal <;>
      simp only [certificateSymbols_pos, certificateSymbols_neg, List.length_cons,
        List.length_append, List.length_map] <;> lia

/-- Adding an assignment writes its sign and binary name before the remaining certificate. -/
private theorem certificateSymbols_entry (name : Variable) (value : Bool) (rest : Certificate) :
    certificateSymbols (Certificate.entry name value :: rest) =
      valueSign value :: name.map digit ++ nameEnd :: certificateSymbols rest := by
  cases value <;>
    simp [Certificate.entry, certificateSymbols_pos, certificateSymbols_neg,
      valueSign]

/-- One completed search iteration can precede the remaining loop and the return to the start. -/
private theorem lookupReturn_step (s final : TMState machine) (cost : TMCost)
    (hstate : s.config.state = some .searching)
    (h : Completes (do lookupBody; lookupLoop; seekLeftEnd machine) s cost final) :
    Completes (do lookupLoop; seekLeftEnd machine) s cost final := by
  obtain ⟨fuel, h⟩ := h
  refine ⟨fuel + 1, ?_⟩
  simpa [lookupLoop, FuelExecMonad.execute_bind, execute_while_succ, hstate,
    bind_assoc, Option.bind_assoc, add_assoc] using h

/--
Searching the remaining entries returns the first listed value for the query, or false if absent.
It restores the whole word and returns to the query's first cell. Earlier entries are part of the
unchanged tape; the bound counts the whole occupied word, including those earlier entries.
-/
private theorem lookupLoop_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (query : Variable) (certificate : Certificate)
    (earlier : List Symbol) (s : TMState machine) (hearlier : clauseSeparator ∉ earlier)
    (htape : s.config.BiTape =
      cursor (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++ earlier).reverse
        (certificateSymbols certificate))
    (hstate : s.config.state = some .searching) :
    let W := query.length + (between.length + earlier.length) + (certificateSymbols
      certificate).length + 3
    ∃ cost final, Completes (do lookupLoop; seekLeftEnd machine) s cost final ∧
      final.config = ⟨some (.value (Certificate.assignment certificate query)),
        cursor [] (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++ earlier ++
          certificateSymbols certificate)⟩ ∧
      final.headPos = s.headPos - (query.length + (between.length + earlier.length) + 2) ∧
      cost.steps ≤ 18 * W * (query.length + 1) * (certificate.length + 1) := by
  induction certificate generalizing earlier s with
  | nil =>
    let middle : TMState machine :=
      {s with config := ⟨some (State.value false), s.config.BiTape⟩}
    have hb : Completes lookupBody s 0 middle := by
      unfold lookupBody
      apply Completes.branch
      simpa [htape, certificateSymbols_nil, middle] using
        completes_update s (.value false)
    have hfalse := completes_while_false (.stateIs (some State.searching)) lookupBody middle
      (by simp [middle])
    have hloopexec : Completes lookupLoop s 0 middle := by
      simpa [lookupLoop] using Completes.while_step (by simp [hstate]) hb hfalse
    let W := query.length + (between.length + earlier.length) + 4
    have hbound : W ≤ 18 * W * (query.length + 1) := by
      calc
        W ≤ 18 * W := by lia
        _ ≤ 18 * W * (query.length + 1) := by
          simpa using Nat.mul_le_mul_left (18 * W) (show 1 ≤ query.length + 1 by lia)
    apply Spec.completes
    vcgen [Spec.steps hloopexec 0,
      seekLeftEnd_spec (tm := machine)
        (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++ earlier).reverse
        (certificateSymbols []) (some (.value false)) s.headPos 0]
    all_goals simp_all [middle, Certificate.assignment, W, certificateSymbols_nil,
      List.reverse_append, List.append_assoc]
    all_goals lia
  | cons literal rest ih =>
    obtain ⟨candidate, value, hliteral⟩ :
        ∃ candidate value, literal = Certificate.entry candidate value := by
      cases literal with
      | pos name => exact ⟨name, true, rfl⟩
      | neg name => exact ⟨name, false, rfl⟩
    subst literal
    let W := query.length + (between.length + earlier.length) +
      (certificateSymbols (Certificate.entry candidate value :: rest)).length + 3
    obtain ⟨a, middle, hcheck, hmiddle, hpos, ha⟩ :=
      checkEntry_correct between hbetween value query candidate earlier
        (certificateSymbols rest) s hearlier
        (by simpa [certificateSymbols_entry] using htape)
    have hbody := lookupBody_entry value s middle a
      (by simp [htape, certificateSymbols_entry]) hcheck
    have hfirst : a.steps ≤ 17 * W * (query.length + 1) := by
      convert ha using 1
      simp only [W, certificateSymbols_entry, List.length_cons, List.length_append, List.length_map]
      ring
    by_cases hsame : query = candidate
    · have hstop : middle.config.state ≠ some State.searching := by simp [hmiddle, hsame]
      have hfalse := completes_while_false (.stateIs (some State.searching)) lookupBody middle
        (by simp [hstop])
      have hloopexec : Completes lookupLoop s a middle := by
        simpa [lookupLoop] using Completes.while_step (by simp [hstate]) hbody hfalse
      have hassign : Certificate.assignment (Certificate.entry candidate value :: rest) query =
          value := by cases value <;> simp [Certificate.entry, Certificate.assignment, hsame]
      let left := (query.map digit ++ (nameEnd :: between ++ [certificateSeparator]) ++
        earlier ++ valueSign value :: candidate.map digit ++ [nameEnd]).reverse
      have hreturn : left.length + 2 ≤ W := by
        have hrestLength := certificate_length_le rest
        dsimp [left, W]
        simp only [certificateSymbols_entry, List.length_cons, List.length_append,
          List.length_map, List.length_reverse, List.length_nil]
        lia
      have hreturn' : left.length + 2 ≤ W * (query.length + 1) := hreturn.trans (by
        simpa using Nat.mul_le_mul_left W (show 1 ≤ query.length + 1 by lia))
      have hbound : a.steps + (left.length + 2) ≤
          18 * W * (query.length + 1) * (rest.length + 2) := by
        calc
          _ ≤ 17 * W * (query.length + 1) + W * (query.length + 1) :=
            Nat.add_le_add hfirst hreturn'
          _ = 18 * W * (query.length + 1) := by ring
          _ ≤ 18 * W * (query.length + 1) * (rest.length + 2) :=
            Nat.le_mul_of_pos_right _ (by lia)
      apply Spec.completes
      vcgen [Spec.steps hloopexec 0,
        seekLeftEnd_spec (tm := machine) left (certificateSymbols rest) (some (.value value))
          (s.headPos + candidate.length + 2) a.steps]
      all_goals simp_all [entryEndTape, left, certificateSymbols_entry,
        List.reverse_append, List.append_assoc]
      all_goals lia
    · let earlierNext := earlier ++ valueSign value :: candidate.map digit ++ [nameEnd]
      have hnext : clauseSeparator ∉ earlierNext := by
        have htail : clauseSeparator ∉ valueSign value :: candidate.map digit ++ [nameEnd] := by
          cases value <;>
            simp [valueSign, clauseSeparator, positiveSign, negativeSign, nameEnd, digit,
              List.mem_map]
        simp only [earlierNext, List.append_assoc]
        intro h
        rcases List.mem_append.mp h with h | h
        · exact hearlier h
        · exact htail h
      obtain ⟨b, final, hr, hf, hp, hb⟩ := ih earlierNext middle hnext
        (by simpa [earlierNext, entryEndTape, List.append_assoc] using
          congrArg SingleTapeTM.Cfg.BiTape hmiddle)
        (by simp [hmiddle, hsame])
      have hassign : Certificate.assignment (Certificate.entry candidate value :: rest) query =
          Certificate.assignment rest query := by
        cases value <;> simp [Certificate.entry, Certificate.assignment, Ne.symm hsame]
      have htail : b.steps ≤ 18 * W * (query.length + 1) * (rest.length + 1) := by
        convert hb using 1
        simp only [W, earlierNext, certificateSymbols_entry, List.length_cons,
          List.length_append, List.length_map, List.length_nil]
        ring
      refine ⟨a + b, final, lookupReturn_step s final (a + b) hstate (hbody.seq hr), ?_, ?_, ?_⟩
      · simpa [hassign, earlierNext, certificateSymbols_entry, List.append_assoc] using hf
      · simp only [earlierNext, List.length_append, List.length_cons, List.length_map,
          List.length_nil] at hp
        rw [hp, hpos]
        lia
      · have hfirst' : a.steps ≤ 18 * W * (query.length + 1) := hfirst.trans (by
          exact Nat.mul_le_mul_right (query.length + 1)
            (Nat.mul_le_mul_right W (by decide)))
        calc
          a.steps + b.steps ≤ 18 * W * (query.length + 1) +
              18 * W * (query.length + 1) * (rest.length + 1) := Nat.add_le_add hfirst' htail
          _ = 18 * W * (query.length + 1) *
              ((Certificate.entry candidate value :: rest).length + 1) := by
            simp only [List.length_cons]
            ring

private theorem lookup_correct_impl (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (name : Variable) (certificate : Certificate)
    (s : TMState machine) :
    let word := name.map digit ++ nameEnd :: between ++ certificateSeparator ::
      (certificateEncoding.encode certificate).map Sum.inl
    s.config.BiTape = cursor [] word →
    ∃ cost final, Completes lookup s cost final ∧
      final.config = ⟨some (.value (Certificate.assignment certificate name)), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 19 * (word.length + 1) ^ 3 := by
  dsimp only
  intro htape
  have hbetween' : certificateSeparator ∉ name.map digit ++ nameEnd :: between := by
    simpa [List.mem_map, digit, certificateSeparator, nameEnd] using hbetween
  have hstart : Runs (do [TMQuery machine]
      seekRightSymbol machine certificateSeparator
      moveₜ .Right) s
      (cursor (certificateSeparator :: (name.map digit ++ nameEnd :: between).reverse)
        (certificateSymbols certificate))
      (s.headPos + (name.map digit ++ nameEnd :: between).length + 1)
      ((name.map digit ++ nameEnd :: between).length + 1) := by
    apply Spec.runs
    vcgen [seekRightSymbol_spec (tm := machine) certificateSeparator []
      (name.map digit ++ nameEnd :: between) (certificateSymbols certificate) hbetween'
      s.config.state s.headPos 0]
    all_goals cases hcfg : s.config
    all_goals simp_all [certificateSymbols, TMState.move, TMState.moveCost, List.append_assoc]
  obtain ⟨a, middle, hpre, hmiddle, hpos, ha⟩ := hstart
  let initial : TMState machine := {middle with config.state := some State.searching}
  obtain ⟨b, final, hr, hf, hp, hb⟩ := lookupLoop_correct between hbetween name certificate []
      initial (by simp)
    (by simpa [initial, TMState.move, List.reverse_append, List.append_assoc] using
      congrArg SingleTapeTM.Cfg.BiTape hmiddle) rfl
  refine ⟨a + (0 + b), final, ?_, ?_, ?_, ?_⟩
  · simpa [lookup, bind_assoc] using hpre.seq ((completes_update middle .searching).seq hr)
  · simpa [htape, certificateSymbols, List.append_assoc] using hf
  · simp [initial, hpos] at hp
    simpa [add_assoc] using hp
  · let W := name.length + between.length + (certificateSymbols certificate).length + 3
    have hname : name.length + 1 ≤ W := by dsimp [W]; lia
    have hcertificateLength := certificate_length_le certificate
    have hcertificate : certificate.length + 1 ≤ W := by dsimp [W]; lia
    have hpreBound : a.steps ≤ W := by rw [ha]; dsimp [W]; simp; lia
    have hloop : b.steps ≤ 18 * W ^ 3 := by
      calc
        b.steps ≤ 18 * W * (name.length + 1) * (certificate.length + 1) := by simpa [W] using hb
        _ ≤ 18 * W * W * W :=
          Nat.mul_le_mul (Nat.mul_le_mul_left (18 * W) hname) hcertificate
        _ = 18 * W ^ 3 := by ring
    have hpositive : 1 ≤ W := by dsimp [W]; lia
    have hcube : W ≤ W ^ 3 := by
      calc
        W = W * 1 * 1 := by ring
        _ ≤ W * W * W := Nat.mul_le_mul (Nat.mul_le_mul_left W hpositive) hpositive
        _ = W ^ 3 := by ring
    have htotal : a.steps + b.steps ≤ 19 * W ^ 3 := by
      calc
        a.steps + b.steps ≤ W + 18 * W ^ 3 := Nat.add_le_add hpreBound hloop
        _ ≤ W ^ 3 + 18 * W ^ 3 := Nat.add_le_add_right hcube _
        _ = 19 * W ^ 3 := by ring
    convert htotal using 1 <;>
      (try simp only [W, certificateSymbols, List.length_append, List.length_map,
        List.length_cons, TMCost.add_steps, zero_add])
    all_goals ring

/--
The tape initially contains the binary query name, its ending, the certificate separator, and
an encoded certificate. The lookup returns to the starting cell with every tape symbol restored.
Its final state records exactly the value given by `Certificate.assignment` from the SAT checker:
the first matching entry wins, and an absent name receives false. For an input word of length
`n`, the program uses at most `19 * (n + 1) ^ 3` head moves. The same program handles every name
and every correctly encoded certificate, regardless of their lengths.
-/
theorem lookup_correct (name : Variable) (certificate : Certificate) (s : TMState machine) :
    let word := name.map digit ++ nameEnd :: certificateSeparator ::
      (certificateEncoding.encode certificate).map Sum.inl
    s.config.BiTape = cursor [] word →
    ∃ cost final, Completes lookup s cost final ∧
      final.config = ⟨some (.value (Certificate.assignment certificate name)), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 19 * (word.length + 1) ^ 3 :=
  by
    simpa only [List.append_assoc, List.singleton_append] using
      lookup_correct_impl [] (by simp) name certificate s

/--
The lookup also works when additional occupied cells lie between the query name's ending and
the certificate separator. These cells may contain the rest of a formula. They must not contain
the certificate separator itself. The program preserves all of them, restores both names, and
returns to the starting cell. The move bound counts this additional part of the input too.
-/
theorem lookup_between_correct (between : List Symbol)
    (hbetween : certificateSeparator ∉ between) (name : Variable) (certificate : Certificate)
    (s : TMState machine) :
    let word := name.map digit ++ nameEnd :: between ++ certificateSeparator ::
      (certificateEncoding.encode certificate).map Sum.inl
    s.config.BiTape = cursor [] word →
    ∃ cost final, Completes lookup s cost final ∧
      final.config = ⟨some (.value (Certificate.assignment certificate name)), s.config.BiTape⟩ ∧
      final.headPos = s.headPos ∧ cost.steps ≤ 19 * (word.length + 1) ^ 3 :=
  lookup_correct_impl between hbetween name certificate s

end Algolean.Algorithms.SingleTapeTuringMachines.SAT.Lookup
