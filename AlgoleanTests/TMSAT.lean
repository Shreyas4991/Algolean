/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.TMSAT.Compiler

/-!
# Checking Turing machine satisfiability and its encoding

* Stationary transitions still cost time, and a true bit accepts only after halting.
* Certificate lengths and time bounds are independent, and a verifier can require a nonempty word.
* Encodings preserve complete descriptions and reject invalid tables and malformed fields.
* Size bounds apply to successfully decoded words with noncanonical machine descriptions.
* Compiled query verifiers preserve acceptance and rejection on input-certificate words.
-/

@[expose] public section

namespace AlgoleanTests.TMSAT

open Algolean.Problems Algolean.Problems.TMSAT Computability Cslib.Turing Relation
open Algolean.Algorithms.Alphabet
open Algolean.Algorithms

/-- This source machine has one logical label and a table that writes false and halts. -/
abbrev rejectingControl : SingleTapeTM TapeSymbol where
  State := Fin 1
  q₀ := 0
  tr _ _ := (⟨some (.inl false), none⟩, none)

/-- This query verifier leaves its input unchanged, despite its source table writing false. -/
def identityVerifier : TMQuery.TimeComputable (id : List TapeSymbol → List TapeSymbol) where
  tm := rejectingControl
  program := pure ()
  timeBound _ := 0
  outputsFunInTime input :=
    ⟨0, ⟨(), 0⟩, ⟨TMState.init rejectingControl input, 0⟩, rfl, rfl, le_rfl⟩

-- A completed query program still needs the compiled machine's halting transition.
example : Instance.ofQueryVerifier identityVerifier [true] 2 ∈ satisfiable := by
  rw [mem_satisfiable_ofQueryVerifier_iff]
  exact ⟨[false, false], rfl, rfl⟩

-- An accepting bit in the certificate cannot replace a rejecting bit at the output head.
example : Instance.ofQueryVerifier identityVerifier [false] 1 ∉ satisfiable := by
  rw [mem_satisfiable_ofQueryVerifier_iff]
  rintro ⟨certificate, _, hhead⟩
  simp [wordPair_encode] at hhead

-- Empty input leaves the separator at the head, which is distinct from an accepting bit.
example : encoding.encode (Instance.ofQueryVerifier identityVerifier [] 1) ∉ language := by
  rw [encode_ofQueryVerifier_mem_language_iff]
  rintro ⟨certificate, _, hhead⟩
  simp [wordPair_encode] at hhead

/-- This verifier accepts in one stationary transition by writing a true bit and halting. -/
def accept : SingleTapeTM.Description TapeSymbol where
  states := 0
  initial := 0
  transition _ _ := (some (.inl true), none, none)

/-- This verifier rejects in one stationary transition by writing a false bit and halting. -/
def reject : SingleTapeTM.Description TapeSymbol where
  states := 0
  initial := 0
  transition _ _ := (some (.inl false), none, none)

/-- This verifier moves right once and then halts, leaving the scanned symbol unchanged. -/
def readCertificate : SingleTapeTM.Description TapeSymbol where
  states := 1
  initial := 0
  transition state symbol :=
    if state = 0 then (symbol, some true, some 1) else (symbol, none, none)

-- A stationary write and halt takes one transition, rather than zero transitions.
example (input : List Bool) (certificateLength : ℕ) :
    (⟨accept, input, certificateLength, 1⟩ : Instance) ∈ satisfiable := by
  refine ⟨List.replicate certificateLength false, by simp, ?_⟩
  apply (acceptsWithin_one_iff _ _).mpr
  exact ⟨⟨none, (BiTape.mk₁ _).write (some (.inl true))⟩, ⟨rfl, rfl⟩, rfl⟩

example (input : List Bool) (certificateLength : ℕ) :
    (⟨accept, input, certificateLength, 0⟩ : Instance) ∉ satisfiable := by simp

-- Halting with a false bit rejects even when the machine meets its time bound.
example (input : List Bool) (certificateLength : ℕ) :
    (⟨reject, input, certificateLength, 1⟩ : Instance) ∉ satisfiable := by
  rintro ⟨certificate, _, h⟩
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff _ _).mp h
  simp only [accepting, Set.mem_ofPred_eq] at hfinal
  have hhead := congrArg (fun result => result.map (fun cfg => cfg.BiTape.head)) hstep
  rw [Option.map_some, hfinal.2] at hhead
  simp [SingleTapeTM.Description.machine, reject, SingleTapeTM.initCfg,
    BiTape.optionMove, BiTape.write] at hhead

-- A running state with a true bit under the head is not an accepting configuration.
example : (⟨some (0 : Fin 1), BiTape.mk₁ [.inl true]⟩ : accept.machine.Cfg) ∉
    accepting accept := by
  simp [accepting]

-- On empty input, the verifier reads the certificate's first bit after crossing the separator.
example : (⟨readCertificate, [], 1, 2⟩ : Instance) ∈ satisfiable := by
  let tape : BiTape TapeSymbol := (BiTape.mk₁ [.inr 0, .inl true]).moveRight
  let middle : readCertificate.machine.Cfg := ⟨some (1 : Fin 2), tape⟩
  let final : readCertificate.machine.Cfg := ⟨none, tape⟩
  refine ⟨[true], by decide, final, ⟨rfl, rfl⟩, ?_⟩
  exact (RelatesWithinSteps.single (b := middle) (by rfl)).trans
    (RelatesWithinSteps.single (by rfl))

/-- This verifier always needs two transitions, even when the scanned bit is already true. -/
theorem readCertificate_not_accept_one (word : List TapeSymbol) :
    ¬AcceptsWithin readCertificate word 1 := by
  intro h
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff _ _).mp h
  simp only [accepting, Set.mem_ofPred_eq] at hfinal
  have hstate := congrArg (fun result => result.map (fun cfg => cfg.state)) hstep
  rw [Option.map_some, hfinal.1] at hstate
  simp [SingleTapeTM.Description.machine, readCertificate, SingleTapeTM.initCfg] at hstate

example : (⟨readCertificate, [], 1, 1⟩ : Instance) ∉ satisfiable := by
  rintro ⟨certificate, _, h⟩
  exact readCertificate_not_accept_one _ h

-- Increasing the time bound cannot introduce a certificate of a different length.
example : (⟨readCertificate, [], 0, 2⟩ : Instance) ∉ satisfiable := by
  rw [mem_satisfiable_zero_length]
  rintro ⟨final, hfinal, steps, hle, hrun⟩
  have hcases : steps = 0 ∨ steps = 1 ∨ steps = 2 := by lia
  rcases hcases with h | h | h
  · subst steps
    exact not_acceptsWithin_zero _ _ ⟨final, hfinal, 0, le_rfl, hrun⟩
  · subst steps
    exact readCertificate_not_accept_one _ ⟨final, hfinal, 1, le_rfl, hrun⟩
  · subst steps
    obtain ⟨middle, hfirst, hrest⟩ := hrun.succ'
    change some (⟨some (1 : Fin 2), (BiTape.mk₁ [.inr 0]).moveRight⟩ :
      readCertificate.machine.Cfg) = some middle at hfirst
    cases Option.some.inj hfirst
    obtain ⟨last, hzero, hlast⟩ := hrest.succ
    have heq := hzero.zero
    subst last
    change some (⟨none, (BiTape.mk₁ [.inr 0]).moveRight⟩ :
      readCertificate.machine.Cfg) = some final at hlast
    cases Option.some.inj hlast
    exact (by decide : (none : Option TapeSymbol) ≠ some (.inl true)) hfinal.2

-- Every finite description, including its transition function, survives encoding and decoding.
example (verifier : SingleTapeTM.Description TapeSymbol) :
    SingleTapeTM.Description.encoding.decode
      (SingleTapeTM.Description.encoding.encode verifier) = some verifier := by simp

-- Finite function decoding rejects a list with the wrong number of entries.
example : ((Encoding.ofEncodable Bool).finFunction 2).decode
    ((Encoding.ofEncodable Bool).list.encode [true]) = none := by decide +kernel

-- A transition cannot refer to state one in a description with only state zero.
example : (Encoding.ofEncodable (SingleTapeTM.Transition TapeSymbol 0)).decode
    ((Encoding.ofEncodable (SingleTapeTM.Transition TapeSymbol 1)).encode
      (some (.inl true), none, some 1)) = none := by decide +kernel

-- Unary fields reject false bits.
example : unaryEncoding.decode [true, false] = none := by decide

-- The language has exactly the same answers as the structured instances on encoded inputs.
example (problem : Instance) : encoding.encode problem ∈ language ↔ problem ∈ satisfiable := by
  simp

-- A missing outer separator prevents decoding and therefore prevents language membership.
example : encoding.decode [] = none := rfl

example : [] ∉ language := not_mem_encodedLanguage_of_decode_eq_none _ _ rfl

/-- This three-state verifier writes a true bit and halts in one transition. -/
def threeStateAccept : SingleTapeTM.Description TapeSymbol where
  states := 2
  initial := 0
  transition _ _ := (some (.inl true), none, none)

/-- The state header uses the noncanonical binary word `[false]` to represent the number two. -/
def noncanonicalMachineCode : List SingleTapeTM.Description.CodeSymbol :=
  let header : List SingleTapeTM.Description.BodySymbol :=
    ((([false] : List Bool).map Sum.inl).map Sum.inl).map Sum.inl
  let body := (SingleTapeTM.Description.bodyEncoding (Symbol := TapeSymbol) 2).encode
    (threeStateAccept.initial, threeStateAccept.transition)
  header.map Sum.inl ++ .inr 0 :: (words SingleTapeTM.Description.BodySymbol 1).encode body

/-- The shorter state header still decodes to the complete three-state verifier. -/
theorem noncanonicalMachineCode_decodes :
    SingleTapeTM.Description.encoding.decode noncanonicalMachineCode = some threeStateAccept := by
  simp only [SingleTapeTM.Description.encoding, Encoding.ofEquiv, noncanonicalMachineCode,
    Encoding.sigma, readWord_append_marker, Encoding.decode_encode]
  rw [show (((encodingNatBool.comp (words Bool 2)).comp
    (words SingleTapeTM.Description.RowSymbol 2)).comp
      (words SingleTapeTM.Description.TableSymbol 1)).decode
        (((([false] : List Bool).map Sum.inl).map Sum.inl).map Sum.inl) = some 2 from by decide]
  simp only [Encoding.decode_encode]
  rfl

/-- This payload combines the noncanonical machine description with a two-bit input. -/
def noncanonicalPayload : List PayloadSymbol :=
  ((encodingList SingleTapeTM.Description.CodeSymbol).pair
    SingleTapeTM.Description.bitEncoding).encode (noncanonicalMachineCode, [false, true])

/-- This complete instance uses a one-bit certificate and a time bound of two transitions. -/
def noncanonicalWord : List CodeSymbol :=
  ((encodingList PayloadSymbol).pair boundsEncoding).encode (noncanonicalPayload, (1, 2))

/-- All four instance fields survive decoding when the machine header is noncanonical. -/
theorem noncanonicalWord_decodes : encoding.decode noncanonicalWord =
    some ⟨threeStateAccept, [false, true], 1, 2⟩ := by
  rw [encoding, Encoding.decode_ofEquiv_eq_some_iff]
  apply (Encoding.decode_pair_eq_some_iff _ _).mpr
  refine ⟨noncanonicalPayload, boundsEncoding.encode (1, 2), rfl, ?_, by simp⟩
  apply (Encoding.decode_pair_eq_some_iff _ _).mpr
  exact ⟨noncanonicalMachineCode, SingleTapeTM.Description.bitEncoding.encode [false, true],
    rfl, noncanonicalMachineCode_decodes, by simp⟩

-- The supplied word is genuinely shorter than the canonical encoding of the decoded instance.
example : noncanonicalWord.length + 1 =
    (encoding.encode ⟨threeStateAccept, [false, true], 1, 2⟩).length := by decide +kernel

-- The decoder-side bound applies to the shorter word, including both independent unary fields.
example : 2 + 1 + 2 + 3 ≤ noncanonicalWord.length :=
  input_length_add_bounds_le_length_of_decode noncanonicalWord_decodes

end AlgoleanTests.TMSAT
