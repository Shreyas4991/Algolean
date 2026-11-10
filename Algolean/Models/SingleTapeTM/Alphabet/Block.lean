/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Encoding
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fintype.EquivFin

/-!
# Writing a finite alphabet using two chosen symbols

* `blockWords` represents every source symbol by a word of one fixed positive length.
* Concatenating these words represents an arbitrary source word without adding tape symbols.
* Decoding rejects incomplete words and words containing an unrecognized symbol block.
* The encoded length is the source length multiplied by the fixed block length.

The two target symbols are chosen once, independently of the word being encoded. These
encodings describe words; their Turing machine implementations require separate proofs.
-/

public section

namespace Algolean.Algorithms.Alphabet

open Computability

variable {α Γ : Type}

private def readBlocks (width : Nat) (read : List Γ → Option α) :
    Nat → List Γ → Option (List α)
  | 0, word => if word.isEmpty then some [] else none
  | fuel + 1, word =>
    if word.isEmpty then some []
    else if width ≤ word.length then do
      let symbol ← read (word.take width)
      let rest ← readBlocks width read fuel (word.drop width)
      pure (symbol :: rest)
    else none

private theorem readBlocks_encode (code : Encoding α Γ) (width : Nat)
    (hwidth : 0 < width) (hcode : ∀ symbol, (code.encode symbol).length = width)
    (word : List α) (fuel : Nat) (hfuel : word.length ≤ fuel) :
    readBlocks width code.decode fuel (word.flatMap code.encode) = some word := by
  induction word generalizing fuel with
  | nil => cases fuel <;> simp [readBlocks]
  | cons symbol rest ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hne : (code.encode symbol ++ rest.flatMap code.encode).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff]
        intro heq
        have hl := congrArg List.length heq
        simp only [List.length_append, hcode, List.length_nil] at hl
        lia
      have hrest := ih fuel (by simpa using hfuel)
      simp only [List.flatMap_cons, readBlocks, hne, Bool.false_eq_true, ite_false]
      have hlen : width ≤ (code.encode symbol ++ rest.flatMap code.encode).length := by
        simp only [List.length_append, hcode]
        lia
      rw [ite_eq_left hlen, ← hcode symbol]
      simp [hcode, hrest]

private theorem readBlocks_length_le (width : Nat) (hwidth : 0 < width)
    (read : List Γ → Option α) (fuel : Nat) (word : List Γ) (decoded : List α)
    (h : readBlocks width read fuel word = some decoded) : decoded.length ≤ word.length := by
  induction fuel generalizing word decoded with
  | zero =>
    simp only [readBlocks] at h
    split at h
    · cases Option.some.inj h
      simp
    · cases h
  | succ fuel ih =>
    simp only [readBlocks] at h
    split at h
    · cases Option.some.inj h
      simp
    · split at h
      · cases hs : read (word.take width) with
        | none => simp [hs] at h
        | some symbol =>
          cases hr : readBlocks width read fuel (word.drop width) with
          | none => simp [hs, hr] at h
          | some rest =>
            change Option.bind (read (word.take width)) (fun symbol =>
              Option.bind (readBlocks width read fuel (word.drop width))
                (fun rest => some (symbol :: rest))) = some decoded at h
            simp only [hs, hr, Option.bind_some, Option.some.injEq] at h
            subst decoded
            have ht := ih (word.drop width) rest hr
            simp only [List.length_cons, List.length_drop] at *
            lia
      · cases h

private theorem readBlocks_eq_encode (code : Encoding α Γ) (width : Nat)
    (hread : ∀ {word symbol}, code.decode word = some symbol → word = code.encode symbol)
    (fuel : Nat) (word : List Γ) (decoded : List α)
    (h : readBlocks width code.decode fuel word = some decoded) :
    word = decoded.flatMap code.encode := by
  induction fuel generalizing word decoded with
  | zero =>
    simp only [readBlocks] at h
    split at h
    · cases Option.some.inj h
      simpa using List.isEmpty_iff.mp ‹word.isEmpty = true›
    · cases h
  | succ fuel ih =>
    simp only [readBlocks] at h
    split at h
    · cases Option.some.inj h
      simpa using List.isEmpty_iff.mp ‹word.isEmpty = true›
    · split at h
      · cases hs : code.decode (word.take width) with
        | none => simp [hs] at h
        | some symbol =>
          cases hr : readBlocks width code.decode fuel (word.drop width) with
          | none => simp [hs, hr] at h
          | some rest =>
            change Option.bind (code.decode (word.take width)) (fun symbol =>
              Option.bind (readBlocks width code.decode fuel (word.drop width))
                (fun rest => some (symbol :: rest))) = some decoded at h
            simp only [hs, hr, Option.bind_some, Option.some.injEq] at h
            subst decoded
            rw [List.flatMap_cons, ← hread hs, ← ih _ _ hr, List.take_append_drop]
      · cases h

/--
This represents a list by concatenating its symbol encodings. Every symbol encoding must have
exactly `width` symbols, with positive width. The decoder reads one whole block at a time.
-/
def blockWords (code : Encoding α Γ) (width : Nat) (hwidth : 0 < width)
    (hcode : ∀ symbol, (code.encode symbol).length = width) : Encoding (List α) Γ where
  encode word := word.flatMap code.encode
  decode word := readBlocks width code.decode word.length word
  decode_encode word := by
    apply readBlocks_encode code width hwidth hcode
    have hlength : (word.flatMap code.encode).length = word.length * width := by
      induction word <;> simp_all [Nat.add_mul, Nat.add_comm]
    rw [hlength]
    exact Nat.le_mul_of_pos_right _ hwidth

/-- The fixed symbol length makes the length of an encoded word exactly multiplicative. -/
@[simp] theorem length_blockWords (code : Encoding α Γ) (width : Nat) (hwidth : 0 < width)
    (hcode : ∀ symbol, (code.encode symbol).length = width) (word : List α) :
    ((blockWords code width hwidth hcode).encode word).length = word.length * width := by
  induction word <;> simp_all [blockWords, Nat.add_mul, Nat.add_comm]

/-- A successfully decoded source word cannot be longer than the target word. -/
theorem length_le_of_decode_blockWords (code : Encoding α Γ) (width : Nat) (hwidth : 0 < width)
    (hcode : ∀ symbol, (code.encode symbol).length = width) {word : List Γ} {decoded : List α}
    (h : (blockWords code width hwidth hcode).decode word = some decoded) :
    decoded.length ≤ word.length :=
  readBlocks_length_le width hwidth code.decode word.length word decoded h

/--
If each symbol decoder accepts only its encoder's words, decoding a list also accepts only the
complete word produced by its encoder. Incomplete or unrecognized symbol encodings are rejected.
-/
theorem decode_blockWords_eq_some_iff (code : Encoding α Γ) (width : Nat) (hwidth : 0 < width)
    (hcode : ∀ symbol, (code.encode symbol).length = width)
    (hread : ∀ {word symbol}, code.decode word = some symbol → word = code.encode symbol)
    {word : List Γ} {decoded : List α} :
    (blockWords code width hwidth hcode).decode word = some decoded ↔
      word = (blockWords code width hwidth hcode).encode decoded := by
  constructor
  · exact readBlocks_eq_encode code width hread word.length word decoded
  · rintro rfl
    exact (blockWords code width hwidth hcode).decode_encode decoded

private def blockSymbol (zero one : Γ) {width : Nat} (symbol : Fin width) : List Γ :=
  List.ofFn fun position => if position = symbol then one else zero

private theorem blockSymbol_injective (zero one : Γ) (hne : zero ≠ one) (width : Nat) :
    Function.Injective (blockSymbol zero one : Fin width → List Γ) := by
  intro first second heq
  have hf := List.ofFn_injective heq
  by_contra hne'
  have h := congrFun hf first
  simp [hne'] at h
  exact hne h.symm

variable [DecidableEq Γ]

private def symbolCode (zero one : Γ) (hne : zero ≠ one) (width : Nat) :
    Encoding (Fin width) Γ where
  encode := blockSymbol zero one
  decode word := (List.finRange width).find?
    (fun symbol => decide (blockSymbol zero one symbol = word))
  decode_encode symbol := by
    have hfind (symbols : List (Fin width)) (hmem : symbol ∈ symbols) :
        symbols.find? (fun candidate => decide (blockSymbol zero one candidate =
          blockSymbol zero one symbol)) = some symbol := by
      induction symbols with
      | nil => simp at hmem
      | cons candidate rest ih =>
        by_cases hsame : candidate = symbol
        · subst candidate
          simp
        · have hcode : blockSymbol zero one candidate ≠ blockSymbol zero one symbol :=
            fun h => hsame (blockSymbol_injective zero one hne width h)
          simpa [hcode] using ih (by simpa [Ne.symm hsame] using hmem)
    exact hfind _ (by simp)

private theorem symbolCode_eq_encode (zero one : Γ) (hne : zero ≠ one) (width : Nat)
    {word : List Γ} {symbol : Fin width}
    (h : (symbolCode zero one hne width).decode word = some symbol) :
    word = (symbolCode zero one hne width).encode symbol := by
  change (List.finRange width).find?
    (fun symbol => decide (blockSymbol zero one symbol = word)) = some symbol at h
  have hsymbol := List.find?_some h
  exact (of_decide_eq_true hsymbol).symm

/--
This encodes words over a nonempty finite source alphabet using only `zero` and `one` on the
target alphabet. A source alphabet with `k` symbols uses blocks of length `k`. The choice of
numbering and both target symbols are fixed independently of the input word.
-/
noncomputable def finiteWords [Fintype α] [Nonempty α] (zero one : Γ) (hne : zero ≠ one) :
    Encoding (List α) Γ :=
  let rename := Fintype.equivFin α
  (blockWords (symbolCode zero one hne (Fintype.card α)) (Fintype.card α)
    Fintype.card_pos (by intro symbol; simp [symbolCode, blockSymbol])).ofEquiv
      (Equiv.listEquivOfEquiv rename)

/-- Encoding a finite-alphabet word multiplies its length by the fixed alphabet size. -/
@[simp] theorem length_finiteWords [Fintype α] [Nonempty α]
    (zero one : Γ) (hne : zero ≠ one) (word : List α) :
    ((finiteWords zero one hne).encode word).length = word.length * Fintype.card α := by
  simp [finiteWords, Encoding.ofEquiv, Equiv.listEquivOfEquiv]

/-- Decoding succeeds exactly on the complete representation of the recovered word. -/
theorem decode_finiteWords_eq_some_iff [Fintype α] [Nonempty α]
    (zero one : Γ) (hne : zero ≠ one) {word : List Γ} {decoded : List α} :
    (finiteWords zero one hne).decode word = some decoded ↔
      word = (finiteWords zero one hne).encode decoded := by
  rw [finiteWords, Encoding.decode_ofEquiv_eq_some_iff]
  exact decode_blockWords_eq_some_iff _ _ _ _ (fun h => symbolCode_eq_encode _ _ _ _ h)

/-- Decoding words between finite alphabets cannot increase their lengths. -/
theorem length_le_of_decode_finiteWords [Fintype α] [Nonempty α]
    (zero one : Γ) (hne : zero ≠ one) {word : List Γ} {decoded : List α}
    (h : (finiteWords zero one hne).decode word = some decoded) :
    decoded.length ≤ word.length := by
  have hr := (Encoding.decode_ofEquiv_eq_some_iff _ _).mp h
  have hl := length_le_of_decode_blockWords _ _ _ _ hr
  simpa [Equiv.listEquivOfEquiv] using hl

omit [DecidableEq Γ] in
/--
This chooses two distinct target symbols and uses them to encode every source word. The source
alphabet is finite and nonempty; the target only needs two distinct symbols. These choices are
fixed for the whole encoding and do not depend on the input word.
-/
noncomputable def finiteWordsOver (α Γ : Type) [Fintype α] [Nonempty α] [Nontrivial Γ] :
    Encoding (List α) Γ := by
  classical
  let digits : {pair : Γ × Γ // pair.1 ≠ pair.2} := Classical.choice (by
    obtain ⟨zero, one, hne⟩ := exists_pair_ne Γ
    exact ⟨⟨(zero, one), hne⟩⟩)
  exact finiteWords digits.val.1 digits.val.2 digits.property

omit [DecidableEq Γ] in
/-- Choosing the target symbols does not change the fixed multiplier in encoded word lengths. -/
@[simp] theorem length_finiteWordsOver [Fintype α] [Nonempty α] [Nontrivial Γ]
    (word : List α) :
    ((finiteWordsOver α Γ).encode word).length = word.length * Fintype.card α := by
  simp [finiteWordsOver]

omit [DecidableEq Γ] in
/--
Decoding succeeds exactly on the recovered word's complete encoding. This also rejects symbols
outside the two chosen target symbols and incomplete symbol encodings.
-/
theorem decode_finiteWordsOver_eq_some_iff [Fintype α] [Nonempty α] [Nontrivial Γ]
    {word : List Γ} {decoded : List α} :
    (finiteWordsOver α Γ).decode word = some decoded ↔
      word = (finiteWordsOver α Γ).encode decoded := by
  classical
  dsimp only [finiteWordsOver]
  exact decode_finiteWords_eq_some_iff _ _ _

omit [DecidableEq Γ] in
/-- Choosing the target symbols also preserves the length bound for every successful decoding. -/
theorem length_le_of_decode_finiteWordsOver [Fintype α] [Nonempty α] [Nontrivial Γ]
    {word : List Γ} {decoded : List α}
    (h : (finiteWordsOver α Γ).decode word = some decoded) : decoded.length ≤ word.length := by
  classical
  dsimp only [finiteWordsOver] at h
  exact length_le_of_decode_finiteWords _ _ _ h

omit [DecidableEq Γ] in
/-- Encoding concatenated source words concatenates their encodings. -/
theorem encode_finiteWordsOver_append [Fintype α] [Nonempty α] [Nontrivial Γ]
    (first second : List α) :
    (finiteWordsOver α Γ).encode (first ++ second) =
      (finiteWordsOver α Γ).encode first ++ (finiteWordsOver α Γ).encode second := by
  classical
  simp [finiteWordsOver, finiteWords, Encoding.ofEquiv, Equiv.listEquivOfEquiv, blockWords]

omit [DecidableEq Γ] in
/-- A word's encoding concatenates the fixed code words of its symbols. -/
theorem encode_finiteWordsOver [Fintype α] [Nonempty α] [Nontrivial Γ] (word : List α) :
    (finiteWordsOver α Γ).encode word =
      word.flatMap (fun symbol => (finiteWordsOver α Γ).encode [symbol]) := by
  classical
  induction word with
  | nil => simp [finiteWordsOver, finiteWords, Encoding.ofEquiv,
      Equiv.listEquivOfEquiv, blockWords]
  | cons symbol word ih =>
    simpa using (encode_finiteWordsOver_append (Γ := Γ) [symbol] word).trans (by rw [ih])


omit [DecidableEq Γ] in
/-- Encoding an empty word writes no symbols. -/
@[simp] theorem encode_finiteWordsOver_nil [Fintype α] [Nonempty α] [Nontrivial Γ] :
    (finiteWordsOver α Γ).encode [] = [] := by
  rw [encode_finiteWordsOver]
  rfl

omit [DecidableEq Γ] in
/-- Encoding a concatenation of words encodes each word and then concatenates the results. -/
theorem encode_finiteWordsOver_flatMap {β : Type} [Fintype α] [Nonempty α] [Nontrivial Γ]
    (input : List β) (f : β → List α) :
    (finiteWordsOver α Γ).encode (input.flatMap f) =
      input.flatMap (fun a => (finiteWordsOver α Γ).encode (f a)) := by
  induction input with
  | nil => simp
  | cons a input ih => simp only [List.flatMap_cons, encode_finiteWordsOver_append, ih]

omit [DecidableEq Γ] in
/-- Encoding repeated symbols repeats their fixed code word the same number of times. -/
theorem encode_finiteWordsOver_replicate [Fintype α] [Nonempty α] [Nontrivial Γ]
    (n : Nat) (symbol : α) :
    (finiteWordsOver α Γ).encode (List.replicate n symbol) =
      (List.replicate n ((finiteWordsOver α Γ).encode [symbol])).flatten := by
  rw [encode_finiteWordsOver]
  simp only [List.flatMap_replicate]

end Algolean.Algorithms.Alphabet
