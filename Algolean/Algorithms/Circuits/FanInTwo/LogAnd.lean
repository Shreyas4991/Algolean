/-
Copyright (c) 2026 Bashar Hamade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bashar Hamade
-/

module

public import Algolean.Models.FanInTwoCircuits
public import Mathlib

@[expose] public section

open Algolean.Algorithms.Prog
open FanInTwoCircuit

namespace Algolean.Algorithms

/-- Recursive helper for `CircAndSplit`: builds an AND circuit with `m` inputs
    by splitting into two halves. -/
def do_CircAndSplit : (m : ℕ) → (Fin m → FanInTwoCircuit Bool Bool) →
    FanInTwoCircuit Bool Bool
  | 0,     _  => const true
  | 1,     x  => x 0
  | m + 2, x  =>
      mul (do_CircAndSplit ((m+2)/2) (Fin.take ((m+2)/2) (by
        have : (m+2)/2 ≤ m+2 := by grind
        exact this) x))
          (do_CircAndSplit ((m+2) - (m+2)/2) (fun i => x ⟨i.val + (m+2)/2, by
            have hi : i.val < (m+2) - (m+2)/2 := i.is_lt
            grind⟩))

/-- An "And" circuit with `n` input parameters which are arbitrary circuits,
splitting the circuit into two halves -/
def CircAndSplit (n : ℕ) (x : Fin n → FanInTwoCircuit Bool Bool) :
    Prog (FanInTwoCircuit Bool) Bool :=
  do_CircAndSplit n x

/-- Recursive helper for `CircAndSplitSimple`: builds an AND circuit with `m` inputs
    by splitting into two halves. -/
def do_CircAndSplitSimple : (m : ℕ) → (Fin m → Bool) → FanInTwoCircuit Bool Bool
  | 0,     _  => const true
  | 1,     x  => const (x 0)
  | m + 2, x  =>
      mul (do_CircAndSplitSimple ((m+2)/2) (Fin.take ((m+2)/2) (by
        have : (m+2)/2 ≤ m+2 := by grind
        exact this) x))
          (do_CircAndSplitSimple ((m+2) - (m+2)/2) (fun i => x ⟨i.val + (m+2)/2, by
            have hi : i.val < (m+2) - (m+2)/2 := i.is_lt
            grind⟩))

/-- An "And" circuit with `n` input parameters which are constants,
splitting the circuit into two halves -/
def CircAndSplitSimple (n : ℕ) (x : Fin n → Bool) : Prog (FanInTwoCircuit Bool) Bool :=
  do_CircAndSplitSimple n x

/-- The depth of the equally split "And" circuit with `n` input constant parameters
    has O(log(n)) bound -/
theorem CircAndSplitSimple_depth (n : ℕ) (x : Fin n → Bool) :
    (do_CircAndSplitSimple n x).depthOf ≤ Nat.clog 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0
    | 1
    | 2 => simp [do_CircAndSplitSimple, FanInTwoCircuit.depthOf]
    | n + 2 =>
      have h_left : (do_CircAndSplitSimple ((n+2)/2)
            (Fin.take ((n+2)/2) (by grind) x)).depthOf
          ≤ Nat.clog 2 ((n+2)/2) + 1 :=
        ih ((n+2)/2) (by grind) (Fin.take ((n+2)/2) (by grind) x)
      have h_right : (do_CircAndSplitSimple (n+2-(n+2)/2)
            (fun i : Fin (n+2-(n+2)/2) => x ⟨i.val + (n+2)/2, by grind⟩)).depthOf
          ≤ Nat.clog 2 (n+2-(n+2)/2) + 1 :=
        ih (n+2-(n+2)/2) (by grind) (fun i : Fin (n+2-(n+2)/2) => x ⟨i.val + (n+2)/2, by grind⟩)
      simp only [do_CircAndSplitSimple, FanInTwoCircuit.depthOf]
      rw [Nat.add_comm (Nat.clog 2 (n+2)) 1]
      apply add_le_add
      · exact le_refl 1
      · apply max_le
        · apply Nat.le_trans h_left
          have hn2 : 2 ≤ n+2 := by grind
          rw [Nat.clog_of_two_le (by decide) hn2]
          apply Nat.add_le_add_right
          apply Nat.clog_mono_right 2
          grind
        · apply Nat.le_trans h_right
          have hn2 : 2 ≤ n+2 := by grind
          rw [Nat.clog_of_two_le (by decide) hn2]
          apply Nat.add_le_add_right
          apply Nat.clog_mono_right 2
          grind

/-- The size of the equally split "And" circuit with 0 constant parameters
    is less than or equal 1 -/
theorem CircAndSplitSimple_size_zero (x : Fin 0 → Bool) :
    (do_CircAndSplitSimple 0 x).circuitSize ≤ 1 := by
      simp only [do_CircAndSplitSimple, circuitSize, subcircuits.eq_1,
      insert_empty_eq, Finset.card_singleton, Std.le_refl]

/-- The size of the equally split "And" circuit with n > 0 input constant parameters
    has O(n) bound -/
theorem CircAndSplitSimple_size_pos (n : ℕ) (hn : 0 < n) (x : Fin n → Bool) :
    (do_CircAndSplitSimple n x).circuitSize ≤ 2 * n - 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 1 =>
      simp only [do_CircAndSplitSimple, circuitSize, subcircuits.eq_1,
                 insert_empty_eq, Finset.card_singleton,
                 Std.le_refl]
    | n + 2 =>
      have h_left : (do_CircAndSplitSimple ((n+2)/2)
            (Fin.take ((n+2)/2) (by grind) x)).circuitSize
          ≤ 2 * ((n+2)/2) - 1 :=
        ih ((n+2)/2) (by grind) (by grind) (Fin.take ((n+2)/2) (by grind) x)
      have h_right : (do_CircAndSplitSimple (n+2-(n+2)/2)
            (fun i : Fin (n+2-(n+2)/2) => x ⟨i.val + (n+2)/2, by grind⟩)).circuitSize
          ≤ 2 * (n+2-(n+2)/2) - 1 :=
        ih (n+2-(n+2)/2) (by grind) (by grind) (fun i : Fin (n+2-(n+2)/2)
            => x ⟨i.val + (n+2)/2, by grind⟩)
      simp only [do_CircAndSplitSimple]
      have h_mul_size : ((do_CircAndSplitSimple ((n+2)/2)
            (Fin.take ((n+2)/2) (by grind) x)).mul
            (do_CircAndSplitSimple (n+2-(n+2)/2)
              (fun i : Fin (n+2-(n+2)/2) => x ⟨i.val + (n+2)/2, by grind⟩))).circuitSize
          ≤ 1 + (do_CircAndSplitSimple ((n+2)/2)
              (Fin.take ((n+2)/2) (by grind) x)).circuitSize
              + (do_CircAndSplitSimple (n+2-(n+2)/2)
                (fun i : Fin (n+2-(n+2)/2) => x ⟨i.val + (n+2)/2, by grind⟩)).circuitSize := by
        grind [circuitSize, subcircuits, Finset.card_insert_le,
          Finset.card_union_le, fanInTwocircuitSize_eq_subcircuits_card]
      grind

end Algolean.Algorithms
