/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Models.GenericGroup
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic

/-!
# Brute force discrete logarithm in a generic group

In this file we state and prove the correctness and complexity of the generic brute force
discrete logarithm algorithm in the model of `Algolean.Models.GenericGroup`. Given a generator
`g`, a target `h` and the order of the group, the algorithm walks through the multiples
`1 • g, 2 • g, …, order • g` of `g`, comparing each one against `h`, and returns the first
exponent that matches.

The algorithm is a `GroupAlg 2 ℕ`, so it is polymorphic in the type of group elements and the
group appears only in the statements below, through the instances that `GroupProg.eval` and
`GroupProg.cost` are read against; see `Algolean.Models.GenericGroup` for what that quantification
buys.

## Main definitions

- `dlogInputs`: The inputs of a discrete-logarithm instance, the base point and the target.
- `bruteForceDLogAux`: The main loop of the algorithm, searching from a given accumulator.
- `bruteForceDLog`: Brute force discrete logarithm as a generic group algorithm.

## Main results

- `bruteForceDLog_eval`: the algorithm returns `k` whenever `k` is the least positive exponent
  with `k • g = h`, provided the order it was given is at least `k`.
- `bruteForceDLog_eval_nsmul`: **run in any finite group at its own order, brute force solves the
  discrete logarithm.** This is the form the lower bound of `Algolean.LowerBounds.DiscreteLog`
  asks for, and it is what keeps that bound from being vacuous.
- `bruteForceDLog_eval_zmod`: in *any* group of prime order `p`, on *any* base `g ≠ 0`, the
  exponent read back in `ZMod p` is the secret itself and not merely some exponent that hits the
  same element — the discrete logarithm is unique there, and brute force finds that one.
- `bruteForceDLog_cost_le`: the algorithm always performs at most `order` additions and `order`
  equality tests.
-/

@[expose] public section

namespace Algolean

namespace Algorithms

open Cslib Prog

variable {V G : Type}

/--
The inputs of a discrete-logarithm instance: the base point and the target. The discrete
logarithm algorithms of `Algolean.Algorithms` are run on inputs of this shape.
-/
def dlogInputs (g h : V) : Fin 2 → V := ![g, h]

/-- Absorbing one step of a discrete logarithm search into the exponent. -/
lemma add_add_nsmul [AddCommGroup G] (g acc : G) (i : ℕ) :
    acc + g + i • g = acc + (i + 1) • g := by
  rw [succ_nsmul, ← add_assoc, add_right_comm]

/--
The main loop of the brute force discrete logarithm search. `acc` is the current multiple of the
generator, `exp` is its exponent, and `remaining` counts the candidates left to try. If no match
is found before the candidates run out, the loop gives up and returns the exponent at which it
stopped.
-/
def bruteForceDLogAux (g h acc : V) (exp : ℕ) : ℕ → GroupProg V ℕ
  | 0 => pure exp
  | remaining + 1 => do
    let matched : ULift Bool ← GroupQuery.eq acc h
    if matched.down then
      pure exp
    else do
      let acc' : V ← GroupQuery.add acc g
      bruteForceDLogAux g h acc' (exp + 1) remaining

/--
Brute force discrete logarithm as a generic group algorithm: given the order of the group, search
for the least `x` in `1, …, order` with `x • g = h`. The generator is the first input and the
target the second.
-/
def bruteForceDLog : GroupAlg 2 ℕ :=
  fun _ order inp => bruteForceDLogAux (inp 0) (inp 1) (inp 0) 1 order

section Correctness

variable [AddCommGroup G] [DecidableEq G]

/--
Correctness of the main loop: `k` is the number of steps still needed, so the loop stops `k` steps
later and returns `exp + k`.
-/
lemma bruteForceDLogAux_eval (g h : G) {k : ℕ} :
    ∀ (acc : G) (exp remaining : ℕ), (∀ i < k, acc + i • g ≠ h) → acc + k • g = h →
      k < remaining →
      GroupProg.eval (bruteForceDLogAux g h acc exp remaining) = exp + k := by
  induction k with
  | zero =>
    rintro acc exp (_ | remaining) - hk hlt
    · lia
    · have hacc : acc = h := by simpa using hk
      simp [bruteForceDLogAux, groupModel, hacc]
  | succ k ih =>
    rintro acc exp (_ | remaining) hmin hk hlt
    · lia
    · have hne : acc ≠ h := by simpa using hmin 0 (by lia)
      have hmin' : ∀ i < k, acc + g + i • g ≠ h := by
        intro i hi
        rw [add_add_nsmul]
        exact hmin (i + 1) (by lia)
      have hk' : acc + g + k • g = h := by rw [add_add_nsmul]; exact hk
      simp only [bruteForceDLogAux, Prog.eval_bind, Prog.eval_lift, groupModel_evalQuery,
        GroupQuery.answer, decide_eq_true_eq, hne, if_false]
      calc
        _ = exp + 1 + k := ih (acc + g) (exp + 1) remaining hmin' hk' (by lia)
        _ = exp + (k + 1) := by lia

/--
The brute force search returns `k` whenever `k` is the least positive exponent whose multiple of
`g` equals `h`, and the order it was given is at least `k`.
-/
theorem bruteForceDLog_eval (g h : G) {k order : ℕ} (hmin : ∀ i, 0 < i → i < k → i • g ≠ h)
    (hk : k • g = h) (hk0 : 0 < k) (hle : k ≤ order) :
    GroupProg.eval (bruteForceDLog G order (dlogInputs g h)) = k := by
  have hmin' : ∀ i < k - 1, g + i • g ≠ h := by
    intro i hi
    rw [add_comm, ← succ_nsmul]
    exact hmin (i + 1) (by lia) (by lia)
  have hk' : g + (k - 1) • g = h := by
    rw [add_comm, ← succ_nsmul, Nat.sub_add_cancel hk0]
    exact hk
  change GroupProg.eval (bruteForceDLogAux g h g 1 order) = k
  rw [bruteForceDLogAux_eval g h g 1 order hmin' hk' (by lia)]
  lia

/-- The main loop performs at most one addition and one equality test per remaining candidate. -/
lemma bruteForceDLogAux_cost_le (g h : G) :
    ∀ (remaining : ℕ) (acc : G) (exp : ℕ),
      GroupProg.cost (bruteForceDLogAux g h acc exp remaining) ≤ ⟨remaining, 0, remaining⟩ := by
  intro remaining
  induction remaining with
  | zero => intro acc exp; simp [bruteForceDLogAux]
  | succ remaining ih =>
    intro acc exp
    simp only [bruteForceDLogAux, Prog.time_bind, Prog.time_lift, groupModel_cost,
      GroupQuery.charge, Prog.eval_lift, groupModel_evalQuery, GroupQuery.answer,
      decide_eq_true_eq]
    by_cases hb : acc = h
    · rw [if_pos hb]
      simp
    · rw [if_neg hb]
      simp only [Prog.time_bind, Prog.time_lift, groupModel_cost, GroupQuery.charge,
        Prog.eval_lift, groupModel_evalQuery, GroupQuery.answer]
      calc (⟨0, 0, 1⟩ : GroupCosts) + (⟨1, 0, 0⟩ + GroupProg.cost
            (bruteForceDLogAux g h (acc + g) (exp + 1) remaining))
          ≤ ⟨0, 0, 1⟩ + (⟨1, 0, 0⟩ + ⟨remaining, 0, remaining⟩) := by
            gcongr
            exact ih (acc + g) (exp + 1)
        _ = ⟨remaining + 1, 0, remaining + 1⟩ := by ext <;> simp <;> lia

/-- The brute force search performs at most one addition and one equality test per candidate
exponent. -/
theorem bruteForceDLog_cost_le (g h : G) (order : ℕ) :
    GroupProg.cost (bruteForceDLog G order (dlogInputs g h)) ≤ ⟨order, 0, order⟩ :=
  bruteForceDLogAux_cost_le g h order g 1

end Correctness

/-!
## In a finite group

The order of the group is what bounds the search, so brute force is correct exactly when the order
it is handed is honest. In a finite group every multiple of `g` is a multiple with a *positive*
exponent bounded by the order of the group, which is what the search needs, and this is the form
in which the lower bound of `Algolean.LowerBounds.DiscreteLog` asks for correctness.
-/

section Finite

variable [Fintype G] [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- **Every multiple of `g` is a positive multiple of `g` with a small exponent.** Reducing
modulo the order of `g` lands in `1, …, addOrderOf g`, and Lagrange bounds that by the order of
the group. -/
lemma exists_pos_le_card_nsmul_eq (g : G) (x : ℕ) :
    ∃ k, 0 < k ∧ k ≤ Fintype.card G ∧ k • g = x • g := by
  haveI : Nonempty G := ⟨0⟩
  have hpos : 0 < addOrderOf g := addOrderOf_pos g
  have hle : addOrderOf g ≤ Fintype.card G := Nat.le_of_dvd Fintype.card_pos addOrderOf_dvd_card
  rcases Nat.eq_zero_or_pos (x % addOrderOf g) with h0 | hp
  · refine ⟨addOrderOf g, hpos, hle, ?_⟩
    rw [addOrderOf_nsmul_eq_zero, ← mod_addOrderOf_nsmul, h0, zero_nsmul]
  · exact ⟨x % addOrderOf g, hp, le_trans (Nat.mod_lt _ hpos).le hle, mod_addOrderOf_nsmul g x⟩

/--
**Brute force solves the discrete logarithm in every finite group.** Run at the order of the group
it is in, on the base `g` and the target `x • g`, the exponent it returns is a discrete logarithm
of the target — whatever the group, whatever the base, and whatever the secret.
-/
theorem bruteForceDLog_eval_nsmul (g : G) (x : ℕ) :
    GroupProg.eval (bruteForceDLog G (Fintype.card G) (dlogInputs g (x • g))) • g = x • g := by
  classical
  obtain ⟨k, hk0, hkle, hk⟩ := exists_pos_le_card_nsmul_eq g x
  have hex : ∃ k, 0 < k ∧ k • g = x • g := ⟨k, hk0, hk⟩
  obtain ⟨hm0, hmk⟩ : 0 < Nat.find hex ∧ Nat.find hex • g = x • g := Nat.find_spec hex
  have hmin : ∀ i, 0 < i → i < Nat.find hex → i • g ≠ x • g := fun i hi0 him hi =>
    Nat.find_min hex him ⟨hi0, hi⟩
  have hmle : Nat.find hex ≤ Fintype.card G := le_trans (Nat.find_le ⟨hk0, hk⟩) hkle
  rw [bruteForceDLog_eval g (x • g) hmin hmk hm0 hmle]
  exact hmk

end Finite

/-!
## In a group of prime order

`bruteForceDLog_eval_nsmul` pins the answer down only up to the base: it says the exponent that
comes back is *a* discrete logarithm of the target, not that it is the exponent the target was
built from. Once the base generates, the two coincide, because the exponents hitting a given
element are then a single residue class modulo the order of the group. Reading the answer back in
`ZMod p` therefore returns the secret that was handed in — the secret `0` included, on which the
search itself returns `p` rather than `0`.

A group of prime order is the case of interest, since there every base other than `0` generates.
The group is arbitrary: any `G` with `Fintype.card G = p`, and any nonzero `g` in it. Such a `G`
is of course isomorphic to `ZMod p`, where discrete logarithms are no work at all, but that costs
these statements nothing, since `bruteForceDLog` is a `GroupAlg` and never sees the isomorphism.
All it can do with the labels it is handed is add them and compare them, and it is charged for
both, so it pays the same price in every group of order `p`.
-/

section PrimeOrder

variable [Fintype G] [AddCommGroup G] [DecidableEq G] {p : ℕ}

/--
**Brute force returns the exponent it was given, modulo the order, whenever the base generates.**
The hypothesis `addOrderOf g = p` is what removes the slack in `bruteForceDLog_eval_nsmul`: the
exponents `k` with `k • g = x • g` are exactly those congruent to `x` modulo `p`, so an answer
read back in `ZMod p` can only be `x` itself.
-/
theorem bruteForceDLog_eval_natCast (hcard : Fintype.card G = p) {g : G} (hgen : addOrderOf g = p)
    (x : ℕ) :
    GroupProg.eval ((fun n : ℕ => (n : ZMod p)) <$> bruteForceDLog G p (dlogInputs g (x • g)))
      = (x : ZMod p) := by
  have h := bruteForceDLog_eval_nsmul g x
  rw [hcard] at h
  have hmod := nsmul_eq_nsmul_iff_modEq.mp h
  rw [hgen] at hmod
  simp only [Prog.eval_map]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

/--
**Brute force recovers every secret exactly in a group of prime order.** The algorithm is the same
one as before, run on an arbitrary group `G` of prime order `p` and an arbitrary base `g ≠ 0`, and
only its answer is read back in `ZMod p`. The conclusion is an equality of exponents rather than
the equality of group elements of `bruteForceDLog_eval_nsmul`: what comes back is not merely some
discrete logarithm of the target, it is the unique one, the secret `x` itself. This is also what
makes it right on the secret `0`, where the search returns `p`.
-/
theorem bruteForceDLog_eval_zmod (hp : p.Prime) (hcard : Fintype.card G = p) {g : G} (hg : g ≠ 0)
    (x : ZMod p) :
    GroupProg.eval ((fun n : ℕ => (n : ZMod p)) <$> bruteForceDLog G p (dlogInputs g (x.val • g)))
      = x := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hgen : addOrderOf g = p :=
    addOrderOf_eq_prime (by rw [← hcard]; exact card_nsmul_eq_zero) hg
  rw [bruteForceDLog_eval_natCast hcard hgen x.val, ZMod.natCast_val, ZMod.cast_id]

end PrimeOrder

end Algorithms

end Algolean
