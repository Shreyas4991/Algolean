/-
Copyright (c) 2025 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.FanInTwoCircuits
public import Mathlib

@[expose] public section

/-!
# Examples of Progs for Circuits

This file contains examples and tests of fan-in 2 circuits written in the Prog Model
-/
namespace AlgoleanTests

open Cslib Algolean Algorithms Prog

open FanInTwoCircuit

/-- An example circuit with only 4 distinct nodes and no input parameters -/
def exCircuit1 : Prog (FanInTwoCircuit Bool) Bool := do
  let x := const true
  let y := const true
  let z := add x y
  let w := mul x y
  add z w

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval exCircuit1.eval circModel

-- /--
-- info: { depth := 2, size := 4 }
-- -/
-- #guard_msgs in
-- #eval exCircuit1.time circModel


/-- An example circuit with only 4 distinct nodes, no redundant nodes, and no input parameters -/
def exCircuit2 : Prog (FanInTwoCircuit ℚ) ℚ := do
  let x := const (1 : ℚ)
  let y := const (2 : ℚ)
  let z := add x y
  mul z z

-- /--
-- info: 9
-- -/
-- #guard_msgs in
-- #eval exCircuit2.eval circModel

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval exCircuit2.time circModel == ⟨2,4⟩


/-- An example circuit with two input parameters occurring redundantly -/
def exCircuit3 (x y : FanInTwoCircuit ℚ ℚ) : Prog (FanInTwoCircuit ℚ) ℚ := do
  let z := add x y
  let w := mul x y
  mul z w

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (exCircuit3 (.const (1 : ℚ)) (.const (21 : ℚ))).eval circModel == 462

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (exCircuit3 (.const (1 : ℚ)) (.const (2 : ℚ))).time circModel



/-- An example circuit with `n` input parameters which are arbitrary circuits -/
def CircAnd (n : ℕ) (x : Fin n → FanInTwoCircuit Bool Bool) : FanInTwoCircuit Bool Bool :=
  match n with
  | 0 => const true
  | m + 1 =>
      let x_head := x 0
      let x_cons := CircAnd m (Fin.tail x)
      mul x_head x_cons

/-- An execution of the circuit for a given input circuit vector -/
def execCircAnd (x : Fin n → FanInTwoCircuit Bool Bool) : Prog (FanInTwoCircuit Bool) Bool := do
  CircAnd n x

theorem CircAnd_size : ∀ n : ℕ, ∀ x : Fin n → FanInTwoCircuit Bool Bool,
    (CircAnd n x).circuitSize
      ≤ 1 + 2 * n + (Fin.sum (FinVec.map FanInTwoCircuit.circuitSize x)) := by
  intro n x
  induction n with
  | zero =>
      simp [CircAnd]
  | succ m ih =>
      specialize ih (Fin.tail x)
      have hsum : Fin.sum (FinVec.map FanInTwoCircuit.circuitSize x)
          = (x 0).circuitSize + Fin.sum (FinVec.map FanInTwoCircuit.circuitSize (Fin.tail x)) := by
        simpa [FinVec.map] using
          (Fin.sum_univ_succ (f := fun i : Fin (m + 1) => FanInTwoCircuit.circuitSize (x i)))
      have hmul : (CircAnd (m + 1) x).circuitSize
          ≤ 1 + (x 0).circuitSize + (CircAnd m (Fin.tail x)).circuitSize := by
        grind [CircAnd, FanInTwoCircuit.circuitSize, FanInTwoCircuit.subcircuits,
          Finset.card_insert_le, Finset.card_union_le, fanInTwocircuitSize_eq_subcircuits_card]
      grind


/-- An example circuit with `n` input parameters which are constants -/
def CircAndSimple (n : ℕ) (x : Fin n → Bool) : FanInTwoCircuit Bool Bool :=
  match n with
  | 0 => const true
  | m + 1 =>
      let x_head := .const (x 0)
      let x_cons := CircAndSimple m (Fin.tail x)
      mul x_head x_cons

/-- An execution of the circuit for a given input boolean vector -/
def execCircAndSimple (x : Fin n → Bool) : Prog (FanInTwoCircuit Bool) Bool := do
  CircAndSimple n x

theorem CircAndSimple_size : ∀ n : ℕ, ∀ x : Fin n → Bool,
    (CircAndSimple n x).circuitSize ≤ 1 + 2 * n + 2 := by
  intro n x
  induction n with
  | zero =>
      simp [CircAndSimple]
  | succ m ih =>
      specialize ih (Fin.tail x)
      simp only [FanInTwoCircuit.circuitSize, CircAndSimple, FanInTwoCircuit.subcircuits.eq_3,
        FanInTwoCircuit.subcircuits.eq_1, insert_empty_eq, Finset.singleton_union]
      grind[Finset.card_insert_le, fanInTwocircuitSize_eq_subcircuits_card]

private lemma tail_image_subset (m : ℕ) (x : Fin (m + 1) → FanInTwoCircuit Bool Bool) :
    Finset.univ.image (fun i : Fin m => (Fin.tail x i).depthOf) ⊆
    Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf) := by
  intro d hd
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
  exact Finset.mem_image.mpr ⟨Fin.succ i, Finset.mem_univ _, by simp [Fin.tail]⟩

private lemma tail_max_le_full_max (m : ℕ) (x : Fin (m + 1) → FanInTwoCircuit Bool Bool) :
    (Finset.univ.image (fun i : Fin m => (Fin.tail x i).depthOf)).max.getD 0 ≤
    (Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf)).max.getD 0 := by
  have h_mono := Finset.max_mono (tail_image_subset m x)
  cases h_s : (Finset.univ.image (fun i : Fin m => (Fin.tail x i).depthOf)).max <;>
  cases h_t : (Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf)).max <;>
<<<<<<< HEAD
    simp_all only [Std.le_refl, bot_le, ge_iff_le, le_bot_iff,
      WithBot.coe_ne_bot, WithBot.coe_le_coe] <;>
=======
    simp_all [Std.le_refl,bot_le,ge_iff_le,le_bot_iff,WithBot.coe_ne_bot, WithBot.coe_le_coe] <;>
>>>>>>> 3a9a339 (depth proof update & build)
    first | exact Nat.zero_le _ | exact h_mono

private lemma head_le_full_max (m : ℕ) (x : Fin (m + 1) → FanInTwoCircuit Bool Bool) :
    (x 0).depthOf ≤
    (Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf)).max.getD 0 := by
  have hmem : (x 0).depthOf ∈ Finset.univ.image (fun i => (x i).depthOf) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  obtain ⟨l, hl⟩ := Finset.max_of_nonempty ⟨_, hmem⟩
  simp only [hl]
  exact Finset.le_max_of_eq hmem hl

theorem AndDepthAtMostOne (n : ℕ) (x : Fin n → FanInTwoCircuit Bool Bool) :
    (CircAnd n x).depthOf ≤ n +
      (Finset.univ.image (fun i : Fin n => (x i).depthOf)).max.getD 0 := by
  induction n with
  | zero =>
      simp [CircAnd, FanInTwoCircuit.depthOf]
  | succ m ih =>
      specialize ih (Fin.tail x)
      simp only [CircAnd, FanInTwoCircuit.depthOf]
      calc
        (mul (x 0) (CircAnd m (Fin.tail x))).depthOf
        _ = 1 + max (x 0).depthOf (CircAnd m (Fin.tail x)).depthOf := rfl
        _ ≤ 1 + (m + max (x 0).depthOf
              ((Finset.univ.image (fun i : Fin m => (Fin.tail x i).depthOf)).max.getD 0)) :=
            by gcongr; grind
        _ = (m + 1) + max (x 0).depthOf
              ((Finset.univ.image (fun i : Fin m => (Fin.tail x i).depthOf)).max.getD 0) :=
            by ring
        _ ≤ (m + 1) + max (x 0).depthOf
              ((Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf)).max.getD 0) :=
            by gcongr; apply tail_max_le_full_max
        _ = (m + 1) + (Finset.univ.image (fun i : Fin (m + 1) => (x i).depthOf)).max.getD 0 :=
            by rw [max_eq_right (head_le_full_max m x)]

theorem CircAndSimple_depth (n : ℕ) (x : Fin n → Bool) :
    (CircAndSimple n x).depthOf ≤ n + 1 := by
  induction n with
  | zero =>
      simp [CircAndSimple, FanInTwoCircuit.depthOf]
  | succ m ih =>
      specialize ih (Fin.tail x)
      simp only [CircAndSimple, FanInTwoCircuit.depthOf]
      calc
        1 + (CircAndSimple m (Fin.tail x)).depthOf
        _ ≤ 1 + (m + 1) := by gcongr
        _ = m + 1 + 1 := by ring



def CircAndSplit : (n : ℕ) → (Fin n → FanInTwoCircuit Bool Bool) → FanInTwoCircuit Bool Bool
  | 0,     _  => const true
  | 1,     x  => x ⟨0, by omega⟩
  | n + 2, x  =>
      let half := (n + 2) / 2
      have h_le : half ≤ n + 2 := Nat.div_le_self _ _
      let x_left  := CircAndSplit half (Fin.take half h_le x)
      let x_right := CircAndSplit ((n + 2) - half)
        (fun i => x ⟨i.val + half, by omega⟩)
      mul x_left x_right

def CircAndSplitSimple : (n : ℕ) → (Fin n → Bool) → FanInTwoCircuit Bool Bool
  | 0,     _  => const true
  | 1,     x  =>  const (x 0)
  | n + 2, x  =>
      let half := (n + 2) / 2
      have h_le : half ≤ n + 2 := Nat.div_le_self _ _
      let x_left  := CircAndSplitSimple half (Fin.take half h_le x)
      let x_right := CircAndSplitSimple ((n + 2) - half)
        (fun i => x ⟨i.val + half, by omega⟩)
      mul x_left x_right


theorem CircAndSplitSimple_depth (n : ℕ) (x : Fin n → Bool) :
    (CircAndSplitSimple n x).depthOf ≤ Nat.clog 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [CircAndSplitSimple, FanInTwoCircuit.depthOf]
    | 1 => simp [CircAndSplitSimple, FanInTwoCircuit.depthOf]
    | 2 => simp [CircAndSplitSimple, FanInTwoCircuit.depthOf]
    | n + 2 =>
      let half := (n + 2) / 2
      let N    := n + 2
      unfold CircAndSplitSimple
      simp only [FanInTwoCircuit.depthOf]
      -- IH applied to both halves
      have h_left : (CircAndSplitSimple half
            (Fin.take half (by omega : half ≤ N) x)).depthOf
          ≤ Nat.clog 2 half + 1 :=
        ih half (by omega) _
      have h_right : (CircAndSplitSimple (N - half)
            (fun i : Fin (N - half) => x ⟨i.val + half, by omega⟩)).depthOf
          ≤ Nat.clog 2 (N - half) + 1 :=
        ih (N - half) (by omega) _
      -- N - half is the ceiling half, which equals (N+1)/2
      have h_right_eq : N - half = (N + 1) / 2 := by
        simp [half, N]; omega
      have h_clog : Nat.clog 2 N = Nat.clog 2 ((N + 1) / 2) + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) (by omega)]
        grind
      -- Left half ≤ ceil half, so clog is monotone
      have h_left_log : Nat.clog 2 half + 1 ≤ Nat.clog 2 N := by
        rw [h_clog]
        apply Nat.add_le_add_right
        apply Nat.clog_mono_right
        simp [half, N]; grind
      have h_right_log : Nat.clog 2 (N - half) + 1 ≤ Nat.clog 2 N := by
        rw [h_clog, h_right_eq]
      have h_max : 1 +
            max (CircAndSplitSimple half (Fin.take half (by omega : half ≤ N) x)).depthOf
                (CircAndSplitSimple (N - half)
                (fun i : Fin (N - half) => x ⟨i.val + half, by omega⟩)).depthOf
          ≤ Nat.clog 2 N + 1 := by
        have := max_le (a := (CircAndSplitSimple half (Fin.take half
        (by omega : half ≤ N) x)).depthOf)
                      (b := (CircAndSplitSimple (N - half) (fun i : Fin (N - half)
                      => x ⟨i.val + half, by omega⟩)).depthOf)
                      (c := Nat.clog 2 N)
                      (by grind) (by grind)
        grind
      grind






-- /--
-- info: true
-- -/
-- #guard_msgs in
--#eval (execCircAnd ![.const false, .const true, .const true]).eval circModel == true

-- /--
-- info: true
-- -/
-- #guard_msgs in
-- #eval (execCircAnd ![.const true, .const false, .const true]).time circModel


end AlgoleanTests
