/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Option

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
* [Fintype.card_sum](##Fintype.card_sum) counts the original symbols and the added markers.
* [Fintype.card_option](##Fintype.card_option) also counts the blank cell.
-/

@[expose] public section

namespace Algolean.Algorithms.Alphabet

/-- This alphabet contains every original symbol and the specified number of fresh markers. -/
abbrev Extended (Symbol : Type u) (markers : ℕ) := Symbol ⊕ Fin markers

end Algolean.Algorithms.Alphabet
