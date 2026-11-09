/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.BasicTMs
public import Algolean.Complexity.NP

/-!
# Checking encoded certificates and the verifier program

These examples show that the separator distinguishes input-certificate pairs even when joining
their words without a separator would give the same result. They also check a verifier that
requires a nonempty certificate. A separate example checks that the underlying Turing machine
program construction still works over an alphabet with one symbol.
The execution checks inspect the complete tape, including both sides of the head and internal
blanks.

The concrete verifier discards the certificate and appends a true bit to the retained input.
It is checked on empty words, distinct certificate boundaries, and missing or repeated separators.
A second program checks that adding symbols to the alphabet preserves tests, loops, and changes
to the control label. It also checks that execution fails when its step limit is too small.
-/

@[expose] public section

namespace AlgoleanTests.NP

open Algolean Algolean.Algorithms Cslib.Turing TMQuery SingleTapeTuringMachines
open scoped TMQuery

/--
For any chosen word, the language containing exactly that word belongs to `P`. The Turing machine
program leaves its input unchanged, so its output equals the chosen word exactly when the input
belongs to that language.
-/
theorem singleton_inP {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [Nontrivial Symbol]
    (yes : List Symbol) :
    P (fun input => input = yes) :=
  ⟨id, yes, ⟨TMQuery.PolyTimeComputable.id⟩, fun _ => Iff.rfl⟩

-- These pairs have identical concatenations but distinct separator encodings.
example : ([false] ++ [true] : List Bool) = [false, true] ++ [] := rfl

example : (Alphabet.wordPair Bool).encode ([false], [true]) ≠
    (Alphabet.wordPair Bool).encode ([false, true], []) := by decide

-- Decoding a pair preserves both word boundaries, including empty words.
example (input certificate : List Bool) :
    (Alphabet.wordPair Bool).decode ((Alphabet.wordPair Bool).encode (input, certificate)) =
      some (input, certificate) := by simp

/--
The language containing only the empty Boolean word belongs to `NP`. Its verifier accepts
exactly the encoded pair `([], [true])`, and its certificate-length bound is one. The required
certificate is nonempty, so this example checks that the separator preserves the boundary
between the input and its certificate.
-/
theorem emptyWord_withCertificate : Algorithms.NP (fun input : List Bool => input = []) := by
  refine ⟨fun word => word = (Alphabet.wordPair Bool).encode ([], [true]),
    1, singleton_inP _, ?_⟩
  intro input
  constructor
  · rintro rfl
    exact ⟨[true], by simp, rfl⟩
  · rintro ⟨certificate, _, h⟩
    exact congrArg Prod.fst ((Alphabet.wordPair Bool).encode_injective h)

-- The program construction still works with one ordinary symbol before the separator is added.
example : Nonempty (TMQuery.PolyTimeComputable
    (fun input : List (Alphabet.Extended Unit 1) => (Alphabet.firstWord input).map Sum.inl)) :=
  ⟨(TMQuery.PolyTimeComputable.id (Symbol := Unit)).onFirstWord⟩

-- The inclusion of P in NP uses the two-symbol assumption of the language classes.
example : Algorithms.NP (fun input : List Bool => input = []) := NP.ofP (singleton_inP [])

/--
This machine supplies two control labels for testing the verifier and the addition of alphabet
symbols. Its transition table preserves symbols and moves right. The tests execute the supplied
Turing machine programs, whose instructions determine the operations performed.
-/
abbrev machine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr q symbol := (⟨symbol, some .right⟩, some q)

/--
This value records the symbol under the head and every represented cell on either side.
Comparing two such values detects internal blanks and occupied cells on both sides of the head.
-/
structure TapeSnapshot (Symbol : Type) where
  /-- This is the symbol under the head, or `none` if that cell is blank. -/
  head : Option Symbol
  /-- These are the cells to the left of the head, nearest first, including internal blanks. -/
  left : List (Option Symbol)
  /-- These are the cells to the right of the head, nearest first, including internal blanks. -/
  right : List (Option Symbol)
deriving DecidableEq

/--
This Lean function records the entire represented tape. It retains the symbol under the head,
the cells on both sides, and every blank between occupied cells.
-/
def snapshot {Symbol : Type} (viewed : BiTape Symbol) : TapeSnapshot Symbol :=
  ⟨viewed.head, viewed.left.toList, viewed.right.toList⟩

/--
This function runs the stored polynomial-time Turing machine program on the supplied input with
a limit of 1000 execution steps. On success, it reports the complete final tape, the head
coordinate, and the number of head-move instructions. It returns `none` if the limit is reached
before the program finishes.
-/
def observe {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {f : List Symbol → List Symbol} (computer : TMQuery.PolyTimeComputable f)
    (input : List Symbol) :=
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  (execute 1000 computer.program (TMState.init computer.tm input)).map fun (result, final) =>
    (snapshot final.machine.config.BiTape, final.machine.headPos, result.tell.steps)

/--
This verifier erases the first separator and everything after it, then appends a true bit to the
retained input. The certificate is therefore removed before the append program runs.
-/
noncomputable def verifier := (appendBitPolyTimeComputable (tm := machine) true).onFirstWord

example : observe verifier ((Alphabet.wordPair Bool).encode ([false], [true])) =
    some (snapshot (BiTape.mk₁ [.inl false, .inl true]), 0, 12) := by decide +kernel

example : observe verifier ((Alphabet.wordPair Bool).encode ([false, true], [])) =
    some (snapshot (BiTape.mk₁ [.inl false, .inl true, .inl true]), 0, 14) := by decide +kernel

example : observe verifier [] =
    some (snapshot (BiTape.mk₁ [.inl true]), 0, 6) := by decide +kernel

example : observe verifier [.inr 0] =
    some (snapshot (BiTape.mk₁ [.inl true]), 0, 6) := by decide +kernel

-- Missing separators retain the whole input; extra separators in the suffix are erased.
example : observe verifier [.inl false, .inl true] =
    some (snapshot (BiTape.mk₁ [.inl false, .inl true, .inl true]), 0, 14) := by decide +kernel

example : observe verifier [.inl false, .inr 0, .inr 0, .inl true] =
    some (snapshot (BiTape.mk₁ [.inl false, .inl true]), 0, 14) := by decide +kernel

/--
When its control label is false, this Turing machine program changes consecutive true bits to
false while moving right, then sets the label to true. Otherwise, it writes false at the current
cell. The tests check that adding symbols to the alphabet preserves the tests and writes inside
the conditional and loop.
-/
def nested : Prog (TMQuery machine) Unit := do [TMQuery machine]
  ifₜ state =ₜ some false then
    whileₜ (tape =ₜ some true) do
      tape ←ₜ some false
      moveₜ .Right
    state ←ₜ true
  else
    tape ←ₜ some false

example :
    (execute 9 (nested.reduceProg (alphabetReduction (markers := 1)))
      (TMState.init (machine.extendAlphabet (markers := 1))
        [.inl true, .inl true, .inl false])).map (fun (result, final) =>
          (snapshot final.machine.config.BiTape, final.machine.config.state,
            final.machine.headPos, result.tell.steps, result.tell.cellsAllocated, final.fuel)) =
      some (⟨some (.inl false), [some (.inl false), some (.inl false)], []⟩,
        some true, 2, 2, 0, 0) := by decide +kernel

example : execute 8 (nested.reduceProg (alphabetReduction (markers := 1)))
    (TMState.init (machine.extendAlphabet (markers := 1))
      [.inl true, .inl true, .inl false]) = none := by decide +kernel

-- A lifted verified computer preserves a noninitial control label and existing allocation history.
example :
    let initial : TMState machine :=
      {TMState.init machine [false] with
        config.state := some true
        headPos := 37
        cellsAllocated := Finset.Icc 35 40
        cellsVisited := {37, 40}}
    let lifted := EncodedComputer.extendAlphabet (markers := 1)
      (appendBitComputer (tm := machine) true)
    (execute 100 lifted.program initial.extendAlphabet).map (fun (result, final) =>
      (snapshot final.machine.config.BiTape, final.machine.config.state,
        final.machine.headPos, result.tell.steps, result.tell.cellsAllocated,
        final.machine.cellsAllocated.card)) =
      some (snapshot (BiTape.mk₁ [.inl false, .inl true]), some true, 37, 4, 0, 6) := by
  decide +kernel

end AlgoleanTests.NP
