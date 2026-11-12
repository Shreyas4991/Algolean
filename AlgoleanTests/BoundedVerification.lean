/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.BoundedVerificationCompiler
public import Algolean.Models.SingleTapeTM.DescriptionEncoding

/-!
# Checking bounded certificate verification

* Every transition costs time, including transitions that leave the head in place.
* Acceptance requires a halted machine and a tape containing only the chosen answer symbol.
* Certificate lengths remain fixed when the time bound is increased.
* Compiling a Query verifier preserves its answers over Boolean, three-symbol, and one-symbol
  alphabets.
* Finite descriptions survive encoding and reject invalid state references and table lengths.
-/

@[expose] public section

namespace AlgoleanTests.BoundedVerification

open Computability Cslib.Turing Relation
open Cslib.Turing.SingleTapeTM.BoundedVerification
open Algolean.Algorithms.Alphabet
open Algolean.Algorithms

local notation "TapeSymbol" => Cslib.Turing.SingleTapeTM.BoundedVerification.TapeSymbol Bool
local notation "Verification" => SingleTapeTM.BoundedVerification Bool
local notation "accepted" => Cslib.Turing.SingleTapeTM.BoundedVerification.accepted true
local notation "accepting" => Cslib.Turing.SingleTapeTM.BoundedVerification.accepting true
local notation "AcceptsWithin" => Cslib.Turing.SingleTapeTM.BoundedVerification.AcceptsWithin true

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
  computesWithin := TMQuery.ComputesWithin.of_outputsWithinTime (fun input =>
    ⟨0, ⟨(), 0⟩, ⟨TMState.init rejectingControl input, 0⟩, rfl, rfl, le_rfl⟩)

-- An unchanged input with a true first bit still has the separator and certificate on its tape.
example : ofQueryVerifier identityVerifier [true] 2 ∉ accepted := by
  rw [mem_accepted_ofQueryVerifier_iff]
  rintro ⟨certificate, hlength, houtput⟩
  have := congrArg List.length houtput
  simp [wordPair_encode, hlength] at this

-- An accepting bit in the certificate cannot replace a rejecting bit at the output head.
example : ofQueryVerifier identityVerifier [false] 1 ∉ accepted := by
  rw [mem_accepted_ofQueryVerifier_iff]
  rintro ⟨certificate, _, hhead⟩
  simp [wordPair_encode] at hhead

-- Empty input leaves the separator at the head, which is distinct from an accepting bit.
example : ofQueryVerifier identityVerifier [] 1 ∉ accepted := by
  rw [mem_accepted_ofQueryVerifier_iff]
  rintro ⟨certificate, _, hhead⟩
  simp [wordPair_encode] at hhead

/-- This verifier writes a true bit and halts in one stationary transition. -/
def accept : SingleTapeTM.Description TapeSymbol where
  states := 0
  initial := 0
  transition _ _ := (some (.inl true), none, none)

/-- This verifier rejects in one stationary transition by writing a false bit and halting. -/
def reject : SingleTapeTM.Description TapeSymbol where
  states := 0
  initial := 0
  transition _ _ := (some (.inl false), none, none)

/-- This verifier erases the first cell, moves right once, and halts over the next cell. -/
def readCertificate : SingleTapeTM.Description TapeSymbol where
  states := 1
  initial := 0
  transition state symbol :=
    if state = 0 then (none, some true, some 1) else (symbol, none, none)

-- A stationary write and halt takes one transition, rather than zero transitions.
example : (⟨accept, [], 0, 1⟩ : Verification) ∈ accepted := by
  refine ⟨[], rfl, ?_⟩
  apply (acceptsWithin_one_iff true _ _).mpr
  exact ⟨⟨none, (BiTape.mk₁ _).write (some (.inl true))⟩, ⟨rfl, rfl⟩, rfl⟩

example (input : List Bool) (certificateLength : ℕ) :
    (⟨accept, input, certificateLength, 0⟩ : Verification) ∉ accepted := by simp

-- Halting with a false bit rejects even when the machine meets its time bound.
example (input : List Bool) (certificateLength : ℕ) :
    (⟨reject, input, certificateLength, 1⟩ : Verification) ∉ accepted := by
  rintro ⟨certificate, _, h⟩
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff true _ _).mp h
  simp only [Cslib.Turing.SingleTapeTM.BoundedVerification.accepting, Set.mem_ofPred_eq] at hfinal
  have hhead := congrArg (fun result => result.map (fun cfg => cfg.BiTape.head)) hstep
  rw [Option.map_some, congrArg BiTape.head hfinal.2] at hhead
  simp [SingleTapeTM.Description.machine, reject, SingleTapeTM.initCfg,
    BiTape.optionMove, BiTape.write, BiTape.mk₁] at hhead

-- A running state with a true bit under the head is not an accepting configuration.
example : (⟨some (0 : Fin 1), BiTape.mk₁ [.inl true]⟩ : accept.machine.Cfg) ∉
    accepting accept := by
  simp [Cslib.Turing.SingleTapeTM.BoundedVerification.accepting]

/-- Halting over true still rejects when another symbol remains to the right. -/
example : (⟨none, BiTape.mk₁ [.inl true, .inl false]⟩ : accept.machine.Cfg) ∉
    accepting accept := by
  intro h
  have hright := congrArg (fun tape => tape.right.head) h.2
  change (some (.inl false) : Option TapeSymbol) = none at hright
  cases hright

/-- Halting over true still rejects when another symbol remains to the left. -/
example : (⟨none, (BiTape.mk₁ [.inl false, .inl true]).moveRight⟩ : accept.machine.Cfg) ∉
    accepting accept := by
  intro h
  have hleft := congrArg (fun tape => tape.left.head) h.2
  change (some (.inl false) : Option TapeSymbol) = none at hleft
  cases hleft

-- Erasing the separator leaves a clean answer one cell to the right of the original head.
example : (⟨readCertificate, [], 1, 2⟩ : Verification) ∈ accepted := by
  let tape : BiTape TapeSymbol := ((BiTape.mk₁ [.inr 0, .inl true]).write none).moveRight
  let middle : readCertificate.machine.Cfg := ⟨some (1 : Fin 2), tape⟩
  let final : readCertificate.machine.Cfg := ⟨none, tape⟩
  refine ⟨[true], by decide, ?_⟩
  apply (acceptsWithin_iff_exists true _ _ _).mpr
  refine ⟨final, ⟨rfl, rfl⟩, ?_⟩
  exact (RelatesWithinSteps.single (b := middle) (by rfl)).trans
    (RelatesWithinSteps.single (by rfl))

/-- This verifier always needs two transitions, even when the scanned bit is already true. -/
theorem readCertificate_not_accept_one (word : List TapeSymbol) :
    ¬AcceptsWithin readCertificate word 1 := by
  intro h
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff true _ _).mp h
  simp only [Cslib.Turing.SingleTapeTM.BoundedVerification.accepting, Set.mem_ofPred_eq] at hfinal
  have hstate := congrArg (fun result => result.map (fun cfg => cfg.state)) hstep
  rw [Option.map_some, hfinal.1] at hstate
  simp [SingleTapeTM.Description.machine, readCertificate, SingleTapeTM.initCfg] at hstate

example : (⟨readCertificate, [], 1, 1⟩ : Verification) ∉ accepted := by
  rintro ⟨certificate, _, h⟩
  exact readCertificate_not_accept_one _ h

-- Increasing the time bound cannot introduce a certificate of a different length.
example : (⟨readCertificate, [], 0, 2⟩ : Verification) ∉ accepted := by
  rw [mem_accepted_zero_length, acceptsWithin_iff_exists]
  rintro ⟨final, hfinal, steps, hle, hrun⟩
  have hcases : steps = 0 ∨ steps = 1 ∨ steps = 2 := by lia
  rcases hcases with h | h | h
  · subst steps
    exact not_acceptsWithin_zero true _ _
      ((acceptsWithin_iff_exists true _ _ _).mpr ⟨final, hfinal, 0, le_rfl, hrun⟩)
  · subst steps
    exact readCertificate_not_accept_one _
      ((acceptsWithin_iff_exists true _ _ _).mpr ⟨final, hfinal, 1, le_rfl, hrun⟩)
  · subst steps
    obtain ⟨middle, hfirst, hrest⟩ := hrun.succ'
    change some (⟨some (1 : Fin 2), ((BiTape.mk₁ [.inr 0]).write none).moveRight⟩ :
      readCertificate.machine.Cfg) = some middle at hfirst
    cases Option.some.inj hfirst
    obtain ⟨last, hzero, hlast⟩ := hrest.succ
    have heq := hzero.zero
    subst last
    change some (⟨none, ((BiTape.mk₁ [.inr 0]).write none).moveRight⟩ :
      readCertificate.machine.Cfg) = some final at hlast
    cases Option.some.inj hlast
    exact (by decide : (none : Option TapeSymbol) ≠ some (.inl true))
      (congrArg BiTape.head hfinal.2)

-- Every finite description, including its transition function, survives encoding and decoding.
example (verifier : SingleTapeTM.Description TapeSymbol) :
    SingleTapeTM.Description.encoding.decode
      (SingleTapeTM.Description.encoding.encode verifier) = some verifier := by simp

-- Finite function decoding rejects a list with the wrong number of entries.
example : ((Encoding.ofEncodable Bool).finFunction 2).decode
    ((Encoding.ofEncodable Bool).list.encode [true]) = none := by decide +kernel

-- A transition cannot refer to state one in a description with only state zero.
example : (SingleTapeTM.Description.transitionEncoding (Symbol := TapeSymbol) 0).decode
    ((SingleTapeTM.Description.transitionEncoding (Symbol := TapeSymbol) 1).encode
      (some (.inl true), none, some 1)) = none := by
  suffices (Encoding.ofEncodable (Option (Fin 1))).decode
      ((Encoding.ofEncodable (Option (Fin 2))).encode (some 1)) = none by
    simp [SingleTapeTM.Description.transitionEncoding, Encoding.pair, Encoding.comp, this]
  decide +kernel


/-- This three-state verifier writes a true bit and halts in one transition. -/
def threeStateAccept : SingleTapeTM.Description TapeSymbol where
  states := 2
  initial := 0
  transition _ _ := (some (.inl true), none, none)

/-- The state header uses the noncanonical binary word `[false]` to represent the number two. -/
def noncanonicalMachineCode : List SingleTapeTM.Description.CodeSymbol :=
  let header : List SingleTapeTM.Description.BodySymbol :=
    ((SingleTapeTM.Description.rowBits.encode [false]).map Sum.inl).map Sum.inl
  let body := (SingleTapeTM.Description.bodyEncoding (Symbol := TapeSymbol) 2).encode
    (threeStateAccept.initial, threeStateAccept.transition)
  header.map Sum.inl ++ .inr 0 :: (words SingleTapeTM.Description.BodySymbol 1).encode body

/-- The shorter state header still decodes to the complete three-state verifier. -/
theorem noncanonicalMachineCode_decodes :
    SingleTapeTM.Description.encoding.decode noncanonicalMachineCode = some threeStateAccept := by
  simp only [SingleTapeTM.Description.encoding, Encoding.ofEquiv, noncanonicalMachineCode,
    Encoding.sigma, readWord_append_marker, Encoding.decode_encode]
  rw [show (((encodingNatBool.comp SingleTapeTM.Description.rowBits).comp
    (words SingleTapeTM.Description.RowSymbol 2)).comp
      (words SingleTapeTM.Description.TableSymbol 1)).decode
        (((SingleTapeTM.Description.rowBits.encode [false]).map Sum.inl).map Sum.inl) =
          some 2 from by decide]
  simp only [Encoding.decode_encode]
  rfl


/-- This finite description writes a chosen symbol and halts after one stationary transition. -/
def writesAndHalts {Γ : Type} (yes : Γ) :
    SingleTapeTM.Description (Extended Γ 1) where
  states := 0
  initial := 0
  transition _ _ := (some (.inl yes), none, none)

/--
For any fixed finite alphabet, overwriting the separator accepts an empty input and certificate
in one transition. This includes alphabets with just one symbol.
-/
theorem accepts_chosen_symbol {Γ : Type} [Fintype Γ]
    (yes : Γ) :
    (⟨writesAndHalts yes, [], 0, 1⟩ : SingleTapeTM.BoundedVerification Γ) ∈
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted yes := by
  refine ⟨[], rfl, ?_⟩
  apply (acceptsWithin_one_iff yes _ _).mpr
  exact ⟨⟨none, (BiTape.mk₁ _).write (some (.inl yes))⟩, ⟨rfl, rfl⟩, rfl⟩

/-- A three-symbol instance accepts when its chosen accepting symbol is two. -/
theorem ternary_accepts :
    (⟨writesAndHalts (2 : Fin 3), [], 0, 1⟩ : SingleTapeTM.BoundedVerification (Fin 3)) ∈
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted 2 := accepts_chosen_symbol _

/-- The same three-symbol instance rejects when the chosen accepting symbol is one. -/
theorem ternary_rejects_other_symbol :
    (⟨writesAndHalts (2 : Fin 3), [], 0, 1⟩ : SingleTapeTM.BoundedVerification (Fin 3)) ∉
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted 1 := by
  rintro ⟨certificate, _, h⟩
  obtain ⟨final, hfinal, hstep⟩ := (acceptsWithin_one_iff (1 : Fin 3) _ _).mp h
  have hhead := congrArg (fun result => result.map (fun cfg => cfg.BiTape.head)) hstep
  rw [Option.map_some, congrArg BiTape.head hfinal.2] at hhead
  simp [SingleTapeTM.Description.machine, writesAndHalts, SingleTapeTM.initCfg,
    BiTape.optionMove, BiTape.write, BiTape.mk₁] at hhead


/-- A one-symbol input alphabet is permitted without assuming a second ordinary symbol. -/
theorem unary_accepts :
    (⟨writesAndHalts (), [], 0, 1⟩ : SingleTapeTM.BoundedVerification Unit) ∈
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted () := accepts_chosen_symbol _

/-- Compilation rejects an unchanged pair even when its first symbol is the accepting symbol. -/
theorem ternary_compiled_query :
    ofQueryVerifier
      (TMQuery.TimeComputable.id (Symbol := Extended (Fin 3) 1)) [2] 2 ∉
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted (2 : Fin 3) := by
  rw [mem_accepted_ofQueryVerifier_iff]
  rintro ⟨certificate, hlength, houtput⟩
  have := congrArg List.length houtput
  simp [wordPair_encode, hlength] at this


/-- Compilation rejects an unchanged input-certificate pair over a one-symbol alphabet. -/
theorem unary_compiled_query :
    ofQueryVerifier (TMQuery.TimeComputable.id (Symbol := Extended Unit 1)) [()] 1 ∉
      Cslib.Turing.SingleTapeTM.BoundedVerification.accepted () := by
  rw [mem_accepted_ofQueryVerifier_iff]
  rintro ⟨certificate, hlength, houtput⟩
  have := congrArg List.length houtput
  simp [wordPair_encode, hlength] at this

end AlgoleanTests.BoundedVerification
