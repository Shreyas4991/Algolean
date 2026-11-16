/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Reduction.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Log

/-!
# The least payload width for an alphabet reduction

For a target alphabet with at least two symbols, `Nat.clog (card Δ) (card Γ)` is the least
width admitting an injective assignment of source symbols to target tuples. The logarithm's
base is the target alphabet size. The separator adds one character to each encoded symbol.

Empty and singleton source alphabets are allowed: their payload width is zero. Empty or unary
target alphabets are excluded from the logarithmic construction; a unary alphabet has only
one fixed-width payload at every width and cannot represent two distinct source symbols.
-/

@[expose] public section

namespace Algolean.Algorithms.Alphabet

variable (Γ Δ : Type) [Fintype Γ] [Fintype Δ]

/-- The ceiling logarithm of the source alphabet size in the target alphabet size. -/
def payloadWidth : ℕ := Nat.clog (Fintype.card Δ) (Fintype.card Γ)

/-- A width is sufficient exactly when it offers at least as many payloads as source symbols. -/
theorem nonempty_blockCode_iff (width : ℕ) :
    Nonempty (BlockCode Γ Δ width) ↔ Fintype.card Γ ≤ Fintype.card Δ ^ width := by
  classical
  constructor
  · rintro ⟨code⟩
    simpa using Fintype.card_le_of_embedding code.digits
  · intro h
    obtain ⟨digits⟩ := Function.Embedding.nonempty_of_card_le
      (α := Γ) (β := Fin width → Δ) (by simpa using h)
    exact ⟨⟨digits⟩⟩

/-- The ceiling logarithm is the least possible fixed payload width. -/
theorem payloadWidth_le_iff [Nontrivial Δ] (width : ℕ) :
    payloadWidth Γ Δ ≤ width ↔ Nonempty (BlockCode Γ Δ width) := by
  rw [payloadWidth, Nat.clog_le_iff_le_pow Fintype.one_lt_card, nonempty_blockCode_iff]

/-- Choose a code at the least width. The choice is fixed independently of the input word. -/
noncomputable def logarithmicCode [Nontrivial Δ] : BlockCode Γ Δ (payloadWidth Γ Δ) :=
  Classical.choice ((payloadWidth_le_iff Γ Δ _).mp le_rfl)

/-- The exact word length is the input length times the ceiling logarithm plus one separator. -/
@[simp] theorem length_logarithmicCode [Nontrivial Δ] (word : List Γ) :
    ((logarithmicCode Γ Δ).encoding.encode word).length =
      word.length * (Nat.clog (Fintype.card Δ) (Fintype.card Γ) + 1) :=
  BlockCode.length_encode _ _

end Algolean.Algorithms.Alphabet
