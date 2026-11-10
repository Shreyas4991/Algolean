/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum

/-!
# Adding symbols to a tape alphabet

This file adds a chosen number of fresh symbols to an alphabet. Setting the number to one or
two gives the extensions needed for separators and other markers. Original symbols are stored
with [Sum.inl](##Sum.inl), and the new symbols are numbered and stored with [Sum.inr](##Sum.inr).
These two kinds of symbols cannot be equal.

A tape cell also has a blank value, represented by [Option.none](##Option.none). That blank is
separate from every symbol in the extended alphabet. Arora and Barak's
[definition of a Turing machine](https://theory.cs.princeton.edu/complexity/), §1.2, includes a
blank and a start symbol. In our tape representation, adding one start marker supplies the
second of those symbols; blank is already present.

## Main definitions and results

* [Extended](##Algolean.Algorithms.Alphabet.Extended) adds the specified number of symbols.
* `Extended.flattenEquiv` combines two extensions into one, preserving the order of their markers.
* [Fintype.card_sum](##Fintype.card_sum) counts the original symbols and the added markers.
* [Fintype.card_option](##Fintype.card_option) also counts the blank cell.
-/

@[expose] public section

namespace Algolean.Algorithms.Alphabet

/-- This alphabet contains every original symbol and the specified number of fresh markers. -/
abbrev Extended (Symbol : Type u) (markers : ℕ) := Symbol ⊕ Fin markers

namespace Extended

/-- Adding two groups of markers is equivalent to adding their combined number in one step. -/
def flattenEquiv (Symbol : Type u) (first second : ℕ) :
    Extended (Extended Symbol first) second ≃ Extended Symbol (first + second) :=
  (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)

/-- Three successive extensions combine into one, with the marker groups kept in order. -/
def flattenThreeEquiv (Symbol : Type u) (first second third : ℕ) :
    Extended (Extended (Extended Symbol first) second) third ≃
      Extended Symbol (first + second + third) :=
  (Equiv.sumCongr (flattenEquiv Symbol first second) (Equiv.refl (Fin third))).trans
    (flattenEquiv Symbol (first + second) third)

/-- Combining extensions leaves every original symbol unchanged. -/
@[simp] theorem flattenEquiv_original (symbol : Symbol) :
    flattenEquiv Symbol first second (.inl (.inl symbol)) = .inl symbol := rfl

/-- The first extension's markers retain their numbers in the combined extension. -/
@[simp] theorem flattenEquiv_first (marker : Fin first) :
    flattenEquiv Symbol first second (.inl (.inr marker)) = .inr (Fin.castAdd second marker) := rfl

/-- The second extension's markers follow all markers of the first extension. -/
@[simp] theorem flattenEquiv_second (marker : Fin second) :
    flattenEquiv Symbol first second (.inr marker) = .inr (Fin.natAdd first marker) := rfl

end Extended

end Algolean.Algorithms.Alphabet
