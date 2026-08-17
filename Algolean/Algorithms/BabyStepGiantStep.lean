/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Algorithms.DiscreteLog
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Baby-step giant-step discrete logarithm in a generic group

In this file we state and prove the correctness and complexity of the baby-step giant-step
discrete logarithm algorithm in the model of `Algolean.Models.GenericGroup`. Given a generator
`g`, a target `h` and the order of the group, write `m` for `Nat.sqrt order + 1`, so that
`order < m * m`. The algorithm

* takes `m` *baby steps*, tabulating the elements `h + j • g` for `j < m`;
* takes up to `m` *giant steps*, walking through the multiples `(i * m) • g` for `1 ≤ i ≤ m` and
  looking each one up in the baby step table.

A hit `(i * m) • g = h + j • g` exhibits `h` as `(i * m - j) • g`, and every exponent in
`1, …, order` is of that shape, so the search succeeds whenever a discrete logarithm exists.

Only `3 * m` of the `m * m` exponent pairs are ever asked for, so the algorithm performs only
`O(√order)` element-producing queries, which is what `GroupCosts.groupOps` records. The model has
no unit cost table lookup though — elements can only be compared through `eq` — so the number of
equality tests stays quadratic in `m`.

## Main definitions

- `nsmulSuccProg`: Computing a positive multiple of a group element by repeated addition.
- `babySteps`: The baby step table, as a list of `(exponent, element)` pairs.
- `tableLookup`: Linear search of the baby step table for a given element.
- `giantSteps`: The giant step loop.
- `bsgs`: Baby-step giant-step discrete logarithm as a generic group algorithm.

## Main results

- `bsgs_eval`: whenever `h` has a positive discrete logarithm bounded by the order the algorithm
  was given, the exponent it returns is a discrete logarithm of `h`.
- `bsgs_eval_nsmul`: **run in any finite group at its own order, baby-step giant-step solves the
  discrete logarithm.** This is the correctness hypothesis of the lower bound in
  `Algolean.LowerBounds.DiscreteLog`, so that bound applies to this algorithm too.
- `bsgs_cost_le`: the search performs at most `3 * m` element-producing queries and at most
  `m * m` equality tests.
- `bsgs_groupOps_le`: in particular the number of element-producing queries is `O(√order)`.

Like every `GroupAlg`, `bsgs` mentions no particular group; see `Algolean.Models.GenericGroup`.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog

variable {V G : Type}

/-- `nsmulSuccProg g k` computes the multiple `(k + 1) • g` using `k` group operations. -/
def nsmulSuccProg (g : V) : ℕ → GroupProg V V
  | 0 => pure g
  | k + 1 => do
    let acc ← nsmulSuccProg g k
    GroupProg.add acc g

/--
The baby steps of the search: tabulate the `k` elements `acc, acc + g, …, acc + (k - 1) • g`
together with the exponents `j, j + 1, …, j + k - 1` that index them.
-/
def babySteps (g : V) : V → ℕ → ℕ → GroupProg V (List (ℕ × V))
  | _, _, 0 => pure []
  | acc, j, k + 1 => do
    let acc' ← GroupProg.add acc g
    let rest ← babySteps g acc' (j + 1) k
    pure ((j, acc) :: rest)

/-- Linear search of a table for `target`, returning the exponent stored alongside the first
matching element. -/
def tableLookup (target : V) : List (ℕ × V) → GroupProg V (Option ℕ)
  | [] => pure none
  | (j, b) :: rest => do
    let matched ← GroupProg.eq b target
    if matched then pure (some j) else tableLookup target rest

/--
The giant steps of the search. `acc` is the current multiple `(i * m) • g` of the giant step
`gamma = m • g`, and `remaining` counts the giant steps left to take. Each step looks `acc` up in
the baby step table `tbl`; a hit at exponent `j` means `(i * m) • g = h + j • g`, so `i * m - j`
is a discrete logarithm of `h`.
-/
def giantSteps (tbl : List (ℕ × V)) (gamma : V) (m : ℕ) : V → ℕ → ℕ → GroupProg V ℕ
  | _, _, 0 => pure 0
  | acc, i, remaining + 1 => do
    match ← tableLookup acc tbl with
    | some j => pure (i * m - j)
    | none => do
      let acc' ← GroupProg.add acc gamma
      giantSteps tbl gamma m acc' (i + 1) remaining

/--
Baby-step giant-step discrete logarithm as a generic group algorithm. Given the order of the
group, it returns the exponent of `h` in base `g` provided there is one in `1, …, order`; if the
search is exhausted without a hit it returns `0`. The generator is the first input and the target
the second.
-/
def bsgs : GroupAlg 2 ℕ := fun _ order inp => do
  let tbl ← babySteps (inp 0) (inp 1) 0 (Nat.sqrt order + 1)
  let gamma ← nsmulSuccProg (inp 0) (Nat.sqrt order)
  giantSteps tbl gamma (Nat.sqrt order + 1) gamma 1 (Nat.sqrt order + 1)

/-!
## Cost

The cost of a program is a property of its query tree, so these bounds hold in every group.
-/

section Cost

variable [AddCommGroup G] [DecidableEq G]

@[simp] lemma nsmulSuccProg_cost (g : G) :
    ∀ k : ℕ, GroupProg.cost (nsmulSuccProg g k) = ⟨k, 0, 0⟩
  | 0 => rfl
  | k + 1 => by
    simp only [nsmulSuccProg, GroupProg.cost_bind, GroupProg.cost_add, nsmulSuccProg_cost g k]
    ext <;> simp

@[simp] lemma babySteps_cost (g : G) : ∀ (k : ℕ) (acc : G) (j : ℕ),
    GroupProg.cost (babySteps g acc j k) = ⟨k, 0, 0⟩ := by
  intro k
  induction k with
  | zero => intro acc j; rfl
  | succ k ih =>
    intro acc j
    simp only [babySteps, GroupProg.cost_bind, GroupProg.cost_add, GroupProg.cost_pure, ih,
      add_zero]
    ext
    all_goals simp only [GroupCosts.add_adds, GroupCosts.add_negs, GroupCosts.add_eqs]
    all_goals omega

lemma babySteps_length (g : G) : ∀ (k : ℕ) (acc : G) (j : ℕ),
    (GroupProg.eval (babySteps g acc j k)).length = k := by
  intro k
  induction k with
  | zero => intro acc j; rfl
  | succ k ih =>
    intro acc j
    simp only [babySteps, GroupProg.eval_bind, GroupProg.eval_add, GroupProg.eval_pure,
      List.length_cons, ih]

lemma tableLookup_cost_le (target : G) : ∀ tbl : List (ℕ × G),
    GroupProg.cost (tableLookup target tbl) ≤ ⟨0, 0, tbl.length⟩
  | [] => by simp [tableLookup]
  | (j, b) :: rest => by
    simp only [tableLookup, GroupProg.cost_bind, GroupProg.cost_eq, GroupProg.eval_eq,
      decide_eq_true_eq]
    by_cases hb : b = target
    · rw [if_pos hb]; simp
    · rw [if_neg hb]
      calc (⟨0, 0, 1⟩ : GroupCosts) + GroupProg.cost (tableLookup target rest)
          ≤ ⟨0, 0, 1⟩ + ⟨0, 0, rest.length⟩ := by
            gcongr
            exact tableLookup_cost_le target rest
        _ = ⟨0, 0, ((j, b) :: rest).length⟩ := by ext <;> simp [Nat.add_comm]

lemma giantSteps_cost_le (tbl : List (ℕ × G)) (gamma : G) (m : ℕ) :
    ∀ (remaining : ℕ) (acc : G) (i : ℕ),
      GroupProg.cost (giantSteps tbl gamma m acc i remaining) ≤
        ⟨remaining, 0, remaining * tbl.length⟩ := by
  intro remaining
  induction remaining with
  | zero => intro acc i; simp [giantSteps]
  | succ remaining ih =>
    intro acc i
    have hmul : (remaining + 1) * tbl.length = remaining * tbl.length + tbl.length :=
      Nat.succ_mul remaining tbl.length
    simp only [giantSteps, GroupProg.cost_bind]
    have hlook := GroupCosts.le_mk_iff.mp (tableLookup_cost_le acc tbl)
    rcases hl : GroupProg.eval (tableLookup acc tbl) with _ | j
    · have hrec := GroupCosts.le_mk_iff.mp (ih (acc + gamma) (i + 1))
      simp only [GroupProg.cost_bind, GroupProg.cost_add, GroupProg.eval_add]
      simp only [GroupCosts.le_mk_iff, GroupCosts.add_adds, GroupCosts.add_negs,
        GroupCosts.add_eqs] at *
      omega
    · simp only [GroupProg.cost_pure, add_zero]
      simp only [GroupCosts.le_mk_iff] at *
      omega

/--
`bsgs` performs at most `3 * m` element-producing queries and at most `m * m` equality tests,
where `m = Nat.sqrt order + 1`.
-/
theorem bsgs_cost_le (inp : Fin 2 → G) (order : ℕ) :
    GroupProg.cost (bsgs G order inp) ≤
      ⟨3 * (Nat.sqrt order + 1), 0, (Nat.sqrt order + 1) * (Nat.sqrt order + 1)⟩ := by
  simp only [bsgs, GroupProg.cost_bind, babySteps_cost, nsmulSuccProg_cost]
  set m := Nat.sqrt order + 1 with hm
  have hgiant := GroupCosts.le_iff.mp (giantSteps_cost_le
    (GroupProg.eval (babySteps (inp 0) (inp 1) 0 m))
    (GroupProg.eval (nsmulSuccProg (inp 0) (Nat.sqrt order))) m m
    (GroupProg.eval (nsmulSuccProg (inp 0) (Nat.sqrt order))) 1)
  rw [babySteps_length] at hgiant
  simp only [GroupCosts.le_iff, GroupCosts.add_adds, GroupCosts.add_negs,
    GroupCosts.add_eqs] at *
  omega

/-- **`bsgs` asks for only `O(√order)` group elements.** -/
theorem bsgs_groupOps_le (inp : Fin 2 → G) (order : ℕ) :
    GroupProg.groupOps (bsgs G order inp) ≤ 3 * (Nat.sqrt order + 1) :=
  GroupCosts.groupOps_le_groupOps (bsgs_cost_le inp order)

end Cost

/-!
## Correctness
-/

section Correctness

variable [AddCommGroup G] [DecidableEq G]

/-- `nsmulSuccProg g k` returns `(k + 1) • g`. -/
@[simp, grind =] lemma nsmulSuccProg_eval (g : G) : ∀ k : ℕ,
    GroupProg.eval (nsmulSuccProg g k) = (k + 1) • g
  | 0 => by simp [nsmulSuccProg]
  | k + 1 => by
    simp only [nsmulSuccProg, GroupProg.eval_bind, GroupProg.eval_add, nsmulSuccProg_eval g k]
    exact (succ_nsmul g (k + 1)).symm

/--
**Correctness of the baby steps.** The table is exactly the `k` exponents `j, …, j + k - 1` paired
with the corresponding multiples.
-/
@[simp, grind =] lemma babySteps_eval (g : G) : ∀ (k : ℕ) (acc : G) (j : ℕ),
    GroupProg.eval (babySteps g acc j k) =
      (List.range k).map fun t => (j + t, acc + t • g) := by
  intro k
  induction k with
  | zero => intro acc j; rfl
  | succ k ih =>
    intro acc j
    have hstep : ∀ t : ℕ, (j + 1 + t, acc + g + t • g) = (j + (t + 1), acc + (t + 1) • g) := by
      intro t
      congr 1
      · omega
      · exact add_add_nsmul g acc t
    simp [babySteps, ih, List.range_succ_eq_map, Function.comp_def, hstep]

/-- Soundness of the table lookup: a returned exponent really does index the target. -/
lemma tableLookup_sound (target : G) : ∀ (tbl : List (ℕ × G)) (j : ℕ),
    GroupProg.eval (tableLookup target tbl) = some j → (j, target) ∈ tbl
  | [], j, hj => by simp [tableLookup] at hj
  | (i, b) :: rest, j, hj => by
    simp only [tableLookup, GroupProg.eval_bind, GroupProg.eval_eq, decide_eq_true_eq] at hj
    by_cases hb : b = target
    · rw [if_pos hb] at hj
      simp only [GroupProg.eval_pure, Option.some.injEq] at hj
      exact hj ▸ hb ▸ List.mem_cons_self ..
    · rw [if_neg hb] at hj
      exact List.mem_cons_of_mem _ (tableLookup_sound target rest j hj)

/-- Completeness of the table lookup: the search succeeds if the target occurs in the table. -/
lemma tableLookup_complete (target : G) : ∀ (tbl : List (ℕ × G)) (j : ℕ), (j, target) ∈ tbl →
    (GroupProg.eval (tableLookup target tbl)).isSome
  | [], j, hmem => by simp at hmem
  | (i, b) :: rest, j, hmem => by
    simp only [tableLookup, GroupProg.eval_bind, GroupProg.eval_eq, decide_eq_true_eq]
    by_cases hb : b = target
    · rw [if_pos hb]; rfl
    · rw [if_neg hb]
      refine tableLookup_complete target rest j ?_
      rcases List.mem_cons.mp hmem with hp | hp
      · simp only [Prod.mk.injEq] at hp
        exact absurd hp.2.symm hb
      · exact hp

/--
**Correctness of the giant step loop.** Provided one of the giant steps it is about to take is
recorded in the baby step table, the exponent it returns is a discrete logarithm of `h`.
-/
lemma giantSteps_eval (g h : G) (tbl : List (ℕ × G)) (gamma : G) (m : ℕ) (hgamma : gamma = m • g)
    (hsound : ∀ p ∈ tbl, p.1 < m ∧ p.2 = h + p.1 • g) (hcomplete : ∀ j < m, (j, h + j • g) ∈ tbl) :
    ∀ (remaining : ℕ) (acc : G) (i : ℕ), acc = (i * m) • g → 1 ≤ i →
      (∃ i' j, i ≤ i' ∧ i' < i + remaining ∧ j < m ∧ (i' * m) • g = h + j • g) →
      GroupProg.eval (giantSteps tbl gamma m acc i remaining) • g = h := by
  subst hgamma
  intro remaining
  induction remaining with
  | zero => rintro acc i - - ⟨i', j, hle, hlt, -, -⟩; omega
  | succ remaining ih =>
    rintro acc i rfl hi ⟨i', j, hle, hlt, hjm, hmatch⟩
    simp only [giantSteps, GroupProg.eval_bind]
    rcases hl : GroupProg.eval (tableLookup ((i * m) • g) tbl) with _ | j'
    · have hne : i ≠ i' := by
        rintro rfl
        have hsome := tableLookup_complete ((i * m) • g) tbl j (hmatch ▸ hcomplete j hjm)
        rw [hl] at hsome
        simp at hsome
      have hstep : (i * m) • g + m • g = ((i + 1) * m) • g := by
        rw [← add_nsmul]; congr 1; ring
      simp only [GroupProg.eval_bind, GroupProg.eval_add, hstep]
      exact ih _ (i + 1) rfl (by omega) ⟨i', j, by omega, by omega, hjm, hmatch⟩
    · have hmem := tableLookup_sound ((i * m) • g) tbl j' hl
      obtain ⟨hj'm, hbd⟩ := hsound _ hmem
      simp only at hj'm hbd
      have hjle : j' ≤ i * m := le_trans hj'm.le (Nat.le_mul_of_pos_left m hi)
      have hcancel : (i * m - j') • g + j' • g = h + j' • g := by
        rw [← add_nsmul, Nat.sub_add_cancel hjle, hbd]
      simpa using add_right_cancel hcancel

/--
**Correctness of baby-step giant-step.** Whenever `h` has a positive discrete logarithm bounded by
the order the algorithm was given, the exponent returned by `bsgs` is a discrete logarithm of `h`.
-/
theorem bsgs_eval (g h : G) {order x : ℕ} (hx0 : 0 < x) (hx : x ≤ order) (hxg : x • g = h) :
    GroupProg.eval (bsgs G order (dlogInputs g h)) • g = h := by
  have hmm : order < (Nat.sqrt order + 1) * (Nat.sqrt order + 1) := by
    have := Nat.lt_succ_sqrt order
    simpa [Nat.mul_comm] using this
  obtain ⟨q, s, hqs, hs'⟩ : ∃ q s, (Nat.sqrt order + 1) * q + s = x - 1 ∧ s < Nat.sqrt order + 1 :=
    ⟨(x - 1) / (Nat.sqrt order + 1), (x - 1) % (Nat.sqrt order + 1), Nat.div_add_mod _ _,
      Nat.mod_lt _ (by omega)⟩
  have hqlt : q < Nat.sqrt order + 1 :=
    lt_of_mul_lt_mul_left (a := Nat.sqrt order + 1) (by omega) (Nat.zero_le _)
  have hqm : (q + 1) * (Nat.sqrt order + 1) =
      (Nat.sqrt order + 1) * q + (Nat.sqrt order + 1) := by ring
  simp only [bsgs, GroupProg.eval_bind, dlogInputs_zero, dlogInputs_one, babySteps_eval,
    nsmulSuccProg_eval]
  refine giantSteps_eval g h _ _ (Nat.sqrt order + 1) rfl (fun p hp => ?_) (fun t ht => ?_)
    (Nat.sqrt order + 1) _ 1 (by rw [one_mul]) le_rfl
    ⟨q + 1, (q + 1) * (Nat.sqrt order + 1) - x, by omega, by omega, by omega, ?_⟩
  · simp only [List.mem_map, List.mem_range] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact ⟨by omega, by simp⟩
  · simp only [List.mem_map, List.mem_range]
    exact ⟨t, ht, by simp⟩
  · rw [← hxg, ← add_nsmul]
    congr 1
    omega

/--
**Baby-step giant-step solves the discrete logarithm in every finite group.** Run at the order of
the group it is in, on the base `g` and the target `x • g`, the exponent it returns is a discrete
logarithm of the target. This is the hypothesis under which the lower bound of
`Algolean.LowerBounds.DiscreteLog` speaks, so that bound applies to `bsgs` as well.
-/
theorem bsgs_eval_nsmul [Fintype G] (g : G) (x : ℕ) :
    GroupProg.eval (bsgs G (Fintype.card G) (dlogInputs g (x • g))) • g = x • g := by
  obtain ⟨k, hk0, hkle, hk⟩ := exists_pos_le_card_nsmul_eq g x
  exact bsgs_eval g (x • g) hk0 hkle hk

end Correctness

end Algorithms

end Algolean
