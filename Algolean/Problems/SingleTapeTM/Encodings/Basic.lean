/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.Basic
public import Algolean.Models.SingleTapeTM.Alphabet.Encoding
public import Mathlib.Computability.Encoding
public import Mathlib.Data.List.Basic

/-!
# Representing decision problems as languages

`encodedLanguage` combines a mathematical problem with an encoding. A word belongs to the
language when it decodes to an input satisfying the problem. Words that fail to decode do not
belong to the language. No machine or time bound is part of this construction.
-/

@[expose] public section

namespace Algolean.Problems

variable {α : Type u} {Symbol : Type v}

/-- A word belongs to this language when it decodes to an input whose answer is yes. -/
def encodedLanguage (problem : DecisionProblem α) (encoding : Computability.Encoding α Symbol) :
    Language Symbol :=
  encoding.decode ⁻¹' (some '' problem)

/-- Encoding an input and then its word gives the same language as those two steps in succession. -/
theorem encodedLanguage_comp {Γ : Type w} (problem : DecisionProblem α)
    (first : Computability.Encoding α Symbol) (second : Computability.Encoding (List Symbol) Γ) :
    encodedLanguage problem (first.comp second) =
      encodedLanguage (encodedLanguage problem first) second := by
  ext word
  cases h : second.decode word <;>
    simp [encodedLanguage, Computability.Encoding.comp, h]

/-- Encoding an input preserves its answer to the problem. -/
@[simp] theorem mem_encodedLanguage_encode (problem : DecisionProblem α)
    (encoding : Computability.Encoding α Symbol) (input : α) :
    encoding.encode input ∈ encodedLanguage problem encoding ↔ input ∈ problem := by
  simp [encodedLanguage]

/-- Successful decoding reduces membership in the language to the answer on the decoded input. -/
theorem mem_encodedLanguage_iff_of_decode_eq_some (problem : DecisionProblem α)
    (encoding : Computability.Encoding α Symbol) {word : List Symbol} {input : α}
    (h : encoding.decode word = some input) :
    word ∈ encodedLanguage problem encoding ↔ input ∈ problem := by
  simp [encodedLanguage, h]

/-- A word that fails to decode does not belong to the encoded language. -/
theorem not_mem_encodedLanguage_of_decode_eq_none (problem : DecisionProblem α)
    (encoding : Computability.Encoding α Symbol) {word : List Symbol}
    (h : encoding.decode word = none) : word ∉ encodedLanguage problem encoding := by
  simp [encodedLanguage, h]

/--
This represents a language on a shared tape alphabet by replacing each symbol with its chosen
image. Words containing symbols outside that image do not belong to the represented language.
-/
def symbolLanguage {Γ Δ : Type} (symbols : Γ ↪ Δ) (language : Language Γ) : Language Δ :=
  List.map symbols '' language

/-- An injective change of symbols preserves membership of every represented word. -/
@[simp] theorem mem_symbolLanguage_map {Γ Δ : Type} (symbols : Γ ↪ Δ)
    (language : Language Γ) (word : List Γ) :
    word.map symbols ∈ symbolLanguage symbols language ↔ word ∈ language := by
  simp [symbolLanguage, (List.map_injective_iff.mpr symbols.injective).eq_iff]

/-- Keeping each symbol unchanged leaves the language unchanged. -/
@[simp] theorem symbolLanguage_refl {Γ : Type} (language : Language Γ) :
    symbolLanguage (Function.Embedding.refl Γ) language = language := by
  change List.map id '' language = language
  simp

end Algolean.Problems
