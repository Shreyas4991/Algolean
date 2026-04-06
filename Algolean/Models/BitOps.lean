/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

@[expose] public section

/-!
# Bit operations for qubit indexing

Bit manipulation utilities for working with computational basis state
indices in an `n`-qubit system. Basis states are indexed by `Fin (2 ^ n)`,
and individual qubits correspond to individual bits.

## Main definitions

- `getBit`: Extract the value of qubit `q` from a basis state index.
- `flipBit`: Flip qubit `q` in a basis state index via XOR.

## Main results

- `flipBit_flipBit`: Flipping a bit twice is the identity.
- `flipBit_comm`: Flips on different qubits commute.
- `getBit_eq_testBit`: `getBit` agrees with `Nat.testBit`.
- `getBit_flipBit_ne`: `getBit` is unchanged by `flipBit` on a different qubit.
- `getBit_flipBit_self`: `getBit` sees the flipped value after `flipBit` on the same qubit.
-/

namespace Algolean

namespace Algorithms

/-! ### Bit manipulation for qubit indexing -/

/-- Extract bit `q` from basis state index `i`. -/
def getBit (i : Fin (2 ^ n)) (q : Fin n) : Bool :=
  (i.val / 2 ^ q.val) % 2 = 1

/-- Flip bit `q` in basis state index `i`. -/
def flipBit (i : Fin (2 ^ n)) (q : Fin n) : Fin (2 ^ n) :=
  ⟨i.val ^^^ (2 ^ q.val), by
    apply Nat.xor_lt_two_pow
    · exact i.isLt
    · exact Nat.pow_lt_pow_right (by omega) q.isLt⟩

/-! ### Bit manipulation lemmas -/

@[simp]
theorem getBit_zero_zero (h : 0 < n) :
    getBit (0 : Fin (2 ^ n)) ⟨0, h⟩ = false := by
  simp [getBit]

/-- `getBit` of 0 is always false. -/
theorem getBit_zero_of (q : Fin n) :
    getBit (⟨0, Nat.two_pow_pos n⟩ : Fin (2 ^ n)) q = false := by
  simp [getBit]

/-- Flipping bit `q` twice is the identity. -/
@[simp]
theorem flipBit_flipBit (i : Fin (2 ^ n)) (q : Fin n) :
    flipBit (flipBit i q) q = i := by
  ext
  simp [flipBit, Nat.xor_assoc, Nat.xor_self]

/-- `flipBit` on different qubits commutes. -/
theorem flipBit_comm (i : Fin (2 ^ n)) (q₁ q₂ : Fin n) :
    flipBit (flipBit i q₁) q₂ = flipBit (flipBit i q₂) q₁ := by
  ext
  simp [flipBit, Nat.xor_assoc, Nat.xor_comm (2 ^ q₁.val)]

/-- `getBit` agrees with `Nat.testBit`. -/
theorem getBit_eq_testBit (i : Fin (2 ^ n)) (q : Fin n) :
    getBit i q = i.val.testBit q.val := by
  unfold getBit Nat.testBit
  simp only [Nat.shiftRight_eq_div_pow]
  have hmod : i.val / 2 ^ q.val % 2 = 0 ∨ i.val / 2 ^ q.val % 2 = 1 := by omega
  rcases hmod with h | h <;> simp [h]

/-- `getBit` is unchanged by `flipBit` on a different qubit. -/
theorem getBit_flipBit_ne (i : Fin (2 ^ n)) (q₁ q₂ : Fin n) (h : q₁ ≠ q₂) :
    getBit (flipBit i q₁) q₂ = getBit i q₂ := by
  simp only [getBit_eq_testBit, flipBit]
  rw [Nat.testBit_xor]
  simp [Fin.val_ne_of_ne h]

/-- `getBit` sees the flipped value after `flipBit` on the same qubit. -/
theorem getBit_flipBit_self (i : Fin (2 ^ n)) (q : Fin n) :
    getBit (flipBit i q) q = !getBit i q := by
  simp only [getBit_eq_testBit, flipBit]
  rw [Nat.testBit_xor]
  simp

end Algorithms

end Algolean
