/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Flatten

/-!
# Giving certificates a fixed length

* `CertificatePadding.encode` adds a symbol before each certificate symbol and a different
  symbol after the last one. It fills the remaining space to reach the required length.
* `CertificatePadding.decode` removes those added symbols and ignores the unused suffix.
* A certificate of length at most `b` has an encoded certificate of length exactly `2 * b + 1`.
* Conversely, decoding a word of that exact length gives a certificate of length at most `b`.

The two distinguished symbols belong to the original alphabet. Certificate symbols can have any
value, including either distinguished symbol: their positions distinguish them from the added
symbols. The definitions describe words; Turing machine implementations need separate proofs.
-/

@[expose] public section

namespace Algolean.Problems.CertificatePadding

variable {Γ : Type} [DecidableEq Γ]

/--
This writes `next` before each certificate symbol, then `stop`, then enough copies of `next`
to fill the length allowance. Its length theorem requires the certificate to fit the bound.
-/
def encode (next stop : Γ) (bound : Nat) (certificate : List Γ) : List Γ :=
  certificate.flatMap (fun symbol => [next, symbol]) ++
    stop :: List.replicate (2 * (bound - certificate.length)) next

/--
This reads pairs consisting of `next` and a certificate symbol until it reaches `stop`.
It ignores everything after `stop` and rejects a missing ending or an incomplete pair.
-/
def decode (next stop : Γ) : List Γ → Option (List Γ)
  | [] => none
  | tag :: rest =>
    if tag = stop then some []
    else if tag = next then
      match rest with
      | [] => none
      | symbol :: suffix => (symbol :: ·) <$> decode next stop suffix
    else none

/-- The ending symbol terminates the certificate, independently of the unused suffix. -/
@[simp] theorem decode_stop (next stop : Γ) (suffix : List Γ) :
    decode next stop (stop :: suffix) = some [] := by
  cases suffix <;> simp [decode]

/-- A pair beginning with `next` contributes its second symbol to the recovered certificate. -/
@[simp] theorem decode_next (next stop : Γ) (hne : next ≠ stop)
    (symbol : Γ) (suffix : List Γ) :
    decode next stop (next :: symbol :: suffix) =
      (symbol :: ·) <$> decode next stop suffix := by
  simp [decode, hne]

/-- A symbol other than the two chosen symbols cannot begin a certificate entry. -/
theorem decode_other (next stop tag : Γ) (hstop : tag ≠ stop) (hnext : tag ≠ next)
    (suffix : List Γ) : decode next stop (tag :: suffix) = none := by
  cases suffix <;> simp [decode, hstop, hnext]

/-- Decoding recovers the certificate independently of the amount of unused suffix. -/
theorem decode_pairs (next stop : Γ) (hne : next ≠ stop)
    (certificate suffix : List Γ) :
    decode next stop (certificate.flatMap (fun symbol => [next, symbol]) ++ stop :: suffix) =
      some certificate := by
  induction certificate with
  | nil => simp
  | cons symbol rest ih => simp [hne, ih]

/-- Adding the length allowance does not change the certificate recovered by decoding. -/
@[simp] theorem decode_encode (next stop : Γ) (hne : next ≠ stop)
    (bound : Nat) (certificate : List Γ) :
    decode next stop (encode next stop bound certificate) = some certificate := by
  exact decode_pairs next stop hne certificate _

omit [DecidableEq Γ] in
/-- A certificate that fits the bound is encoded using exactly `2 * bound + 1` symbols. -/
theorem length_encode (next stop : Γ) (bound : Nat) (certificate : List Γ)
    (hbound : certificate.length ≤ bound) :
    (encode next stop bound certificate).length = 2 * bound + 1 := by
  have hpairs : (certificate.flatMap (fun symbol => [next, symbol])).length =
      2 * certificate.length := by
    induction certificate <;> simp_all; lia
  simp only [encode, List.length_append, List.length_cons, List.length_replicate, hpairs]
  lia

/-- Every recovered certificate uses two symbols per entry and one symbol for its ending. -/
theorem length_le_of_decode (next stop : Γ) {word certificate : List Γ}
    (h : decode next stop word = some certificate) : 2 * certificate.length + 1 ≤ word.length := by
  induction word using List.twoStepInduction generalizing certificate with
  | nil => simp [decode] at h
  | singleton tag =>
    simp only [decode] at h
    split at h
    · simp_all
    · split at h <;> simp_all
  | cons_cons tag symbol rest ih _ =>
    simp only [decode] at h
    split at h
    · simp_all
    · split at h
      · cases hd : decode next stop rest with
        | none => simp [hd] at h
        | some tail =>
          change Option.map (List.cons symbol) (decode next stop rest) = some certificate at h
          simp only [hd, Option.map_some, Option.some.injEq] at h
          subst certificate
          have := ih hd
          simp only [List.length_cons]
          lia
      · simp at h

/-- A recovered certificate fits the original bound when the encoded word has the fixed length. -/
theorem length_le_bound_of_decode (next stop : Γ) {bound : Nat} {word certificate : List Γ}
    (h : decode next stop word = some certificate) (hlen : word.length = 2 * bound + 1) :
    certificate.length ≤ bound := by
  have := length_le_of_decode next stop h
  lia

/--
An accepting certificate of length at most the bound exists exactly when some word of the fixed
length decodes to an accepting certificate. This holds for any property of certificates.
-/
theorem exists_fixed_length_iff (next stop : Γ) (hne : next ≠ stop)
    (bound : Nat) (accepts : List Γ → Prop) :
    (∃ certificate, certificate.length ≤ bound ∧ accepts certificate) ↔
      ∃ word, word.length = 2 * bound + 1 ∧
        ∃ certificate, decode next stop word = some certificate ∧ accepts certificate := by
  constructor
  · rintro ⟨certificate, hlen, haccept⟩
    exact ⟨encode next stop bound certificate, length_encode next stop bound certificate hlen,
      certificate, decode_encode next stop hne bound certificate, haccept⟩
  · rintro ⟨word, hlen, certificate, hdecode, haccept⟩
    exact ⟨certificate, length_le_bound_of_decode next stop hdecode hlen, haccept⟩

end Algolean.Problems.CertificatePadding
