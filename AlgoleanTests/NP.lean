/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.NP
public import Algolean.Complexity.TMComplexity

/-!
# Checking encoded certificates and the verifier program

These examples distinguish pairs that raw concatenation identifies, use a nonempty certificate
in an `NP` witness, and check that `P ⊆ NP` works over a singleton alphabet. The execution checks
inspect the complete tape, including both sides of the head and internal blanks.

The concrete verifier discards the certificate and appends a true bit to the retained input.
It is checked on empty words, distinct certificate boundaries, and malformed encodings. A second
program exercises alphabet lifting inside a branch and loop, including state updates and fuel
exhaustion.
-/

@[expose] public section

namespace AlgoleanTests.NP

open Algolean Algolean.Algorithms Cslib.Turing TMQuery SingleTapeTuringMachines
open scoped TMQuery

/--
Every singleton language is in `P`: the identity Turing machine program leaves the input word
unchanged, and the acceptance word is the singleton language's chosen member.
-/
theorem singleton_inP {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (yes : List Symbol) :
    P (fun input => input = yes) :=
  ⟨id, yes, ⟨TMQuery.PolyTimeComputable.id⟩, fun _ => Iff.rfl⟩

-- These pairs have identical concatenations but distinct separator encodings.
example : ([false] ++ [true] : List Bool) = [false, true] ++ [] := rfl

example : (Alphabet.wordPair Bool).encode ([false], [true]) ≠
    (Alphabet.wordPair Bool).encode ([false, true], []) := by decide

-- Decoding a pair preserves both word boundaries, including empty words.
example (input certificate : List Bool) :
    (Alphabet.wordPair Bool).decode ((Alphabet.wordPair Bool).encode (input, certificate)) =
      some (input, certificate) := (Alphabet.wordPair Bool).decode_encode (input, certificate)

/--
The language containing only the empty Boolean word has an `NP` witness whose verifier accepts
exactly the encoded pair `([], [true])`. Its certificate bound is one, and its successful
certificate is nonempty, so the proof exercises the boundary between input and certificate.
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

-- The P-to-NP construction does not depend on having two ordinary tape symbols.
example : Algorithms.NP (fun input : List Unit => input = []) := NP.ofP (singleton_inP [])

/--
This machine supplies two control labels for the executable verifier and alphabet-lifting tests.
Its transition table preserves symbols and moves right; query programs specify the tested code.
-/
abbrev machine : SingleTapeTM Bool where
  State := Bool
  q₀ := false
  tr q symbol := (⟨symbol, some .right⟩, some q)

/--
This observation records the head symbol and both complete tape stacks. Its decidable equality
retains internal blanks and detects occupied cells on either side of the head.
-/
structure TapeSnapshot (Symbol : Type) where
  head : Option Symbol
  left : List (Option Symbol)
  right : List (Option Symbol)
deriving DecidableEq

/--
This pure Lean function records the entire represented tape, retaining the head symbol, both
stacks, and every internal blank.
-/
def snapshot {Symbol : Type} (viewed : BiTape Symbol) : TapeSnapshot Symbol :=
  ⟨viewed.head, viewed.left.toList, viewed.right.toList⟩

/--
This function runs a polynomial-time Turing machine program on its initialized input tape and
reports its complete final tape, absolute head coordinate, and head-move cost.
-/
def observe {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
    {f : List Symbol → List Symbol} (computer : TMQuery.PolyTimeComputable f)
    (input : List Symbol) :=
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  (execute 1000 computer.program (TMState.init computer.tm input)).map fun (result, final) =>
    (snapshot final.machine.config.BiTape, final.machine.headPos, result.tell.steps)

/--
This value is the verifier program obtained by preparing the first encoded word and then running
the existing Boolean program that appends a true bit. The certificate is erased before the append.
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
This Turing machine program tests its control label, clears consecutive true bits while moving
right, and then sets the label to true. Its nested control flow checks that alphabet lifting
translates conditions and writes inside both branches and loops.
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
