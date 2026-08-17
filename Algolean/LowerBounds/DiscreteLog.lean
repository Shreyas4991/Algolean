/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Algorithms.DiscreteLog
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fintype

/-!
# Generic Group Lower Bound for the Discrete Logarithm

An algorithm that can only add, negate and compare group elements needs about `√|G|` group
operations to compute a discrete logarithm. This is Shoup's bound, derandomized: instead of hiding
the group behind a random encoding, we let the algorithm run first and pick the group afterwards.

The bound is not vacuous: brute force solves the discrete logarithm in every finite group
(`solvesDLog_bruteForceDLog`), and so does baby-step giant-step.

## The idea

The algorithm is blindfolded. It never sees a group element, only an opaque *label* for one, and
the only questions it may ask are "add these two labels", "negate this one", and "are these two
the same?". So there is no need to decide what the group is while it runs. We keep a notebook
instead, recording what each label *would* mean in terms of the unknown answer `X`, and we answer
out of the notebook. It opens with two lines: the base `g` means `1`, and the target `X • g` means
`X`.

Asked to add those two labels we look up `1` and `X`, get `1 + X`, find no label carrying that
value, and invent one. Asked to double the new label we record `2 + 2 * X`. Asked whether two
labels are equal we compare the labels themselves. Every value the algorithm can reach has the
shape `a + b * X` with `a` and `b` known to us, so the notebook can always answer.

Only once the run is over do we choose a number for `X`, and shuffle the `p` group elements so
that every label lands on the value its notebook line demands. That shuffle *is* the group: an
ordinary cyclic group of order `p`, with its elements renamed so that each answer we gave was
true. All of the freedom is in the renaming, which is exactly what a generic algorithm cannot
observe.

A single choice of `X` would prove nothing, so we make two. A value of `X` is spoilt only when it
makes two different notebook lines collide, and two distinct lines `a + b * X` and `a' + b' * X`
agree at no more than one point — the one place the order has to be prime. So `n` lines spoil at
most `n²` values of `X`, while each query grows the notebook by at most three lines. An algorithm
that stops well short of `√p` queries therefore leaves two good values `X₁ ≠ X₂` unspoilt.

Each of the two yields a genuine group, on the same labels, in which that very same run was
legitimate — but whose discrete logarithm is `X₁` in one and `X₂` in the other. A number the
algorithm returned would have to be both. So it returned nothing, which is to say it exhausted its
budget of `√p / 5` group operations.

## The pieces

Fix a large prime `p`.

### Labels and forms

`Lbl p` is the type of labels the algorithm handles: a copy of `ZMod p`, still of `p` elements
(`card_Lbl`), but kept opaque. The copy is not decoration. The two types play different roles at
the same time — `ZMod p` keeps its own ring structure, which the forms below compute in, while
`Lbl p` is handed a *different* additive group, transported along the shuffle — and one type can
carry only one `AddCommGroup` instance. Both appear together in `realize`, so they have to be two
types; `lblEquiv` is the only way across.

A *form* `Frm p = ZMod p × ZMod p` says what a label stands for: `(a, b)` means `a + b * X`, read
off by `Frm.ev`. Forms are closed under the operations on offer, which is what `Frm.ev_add` and
`Frm.ev_neg` record. The state `St p` is a list of `(label, form)` pairs searched by `lookLbl` and
`lookFrm`. It starts as `st0 p`, giving the base `g` the form `1` and the target `h` the form `X`.

### Answering one query: `step`

* `eq x y` compares the two labels and changes nothing.
* `add x y` and `neg x` first `ensure` each argument has a form, then return the label already
  carrying the resulting form, or a new label if there is none (`addFrm`).

Unused labels and forms always exist, by pigeonhole: a state of fewer than `p` entries cannot have
used up all `p` labels. That is `exists_fresh`, applied in `freshLbl_spec` and `freshFrm_spec`.

`ensure` is what copes with a label the algorithm produced out of thin air rather than receiving
it from the oracle: that label is simply given a form nothing else uses. Answering `eq` by
comparing labels is honest because the group built below has `Lbl p` itself as its carrier, so
equality of elements *is* equality of labels; `NodupSt` and `Good` are what keep distinct labels,
distinct forms and distinct values in step.

### Running a program: `sim`

`sim P s B` runs `P` against `step` but allows only `B` queries that create a new element. When the
budget runs out it stops, with `Res.out = none`.

The budget is what keeps the state small. Without it a program could follow a branch a real run
never takes and grow the state to size `p`. Book-keeping: `sim_sublist` (the state only grows),
`sim_length` (at most `s.length + 3 * B` entries), `sim_nodup` (labels and forms stay distinct),
and `sim_cost_of_none` (a run that was cut off really did use the whole budget).

### Choosing `X` and building the group

Call `X` *good* for a state if distinct forms in it evaluate to distinct values at `X` (`Good`).
Then `label ↦ form.ev X` is injective on the state, so `exists_perm` extends it to a permutation
`σ` of `ZMod p` (`Equiv.Perm.exists_extending_pair`) — the shuffle. Pulling the group structure of
`ZMod p` back along `σ` (`Equiv.addCommGroup`) makes `Lbl p` a real abelian group, with law
`x + y = σ⁻¹ (σ x + σ y)` and `σ` itself as an isomorphism `E`.

Note how little `σ` is pinned down: it is prescribed on the entries of the state and arbitrary on
the rest of `ZMod p`. That slack is what lets two different values of `X` both be realized over
one and the same run.

In that group every answer we gave was true: `step_answer` for one query, `sim_sound` for the whole
run — so the simulation neither overcounts the cost nor invents an output. `realize` bundles this
with `E g = 1` and `E h = X`, that is `X.val • g = h`, the shape `SolvesDLog` expects.

### Two good values of `X` always exist

Distinct forms with the same slope never agree, and with different slopes they agree at exactly one
point, `collide` (`collide_eq` — the only place `ZMod p` has to be a field). So a state of `n`
entries spoils at most `n²` values of `X`, and `exists_two_good` finds two good ones as soon as
`n² + 2 ≤ p`.

Primality is not merely a convenience of this count. The algorithm is told the order of the group
it runs in, so at a composite order it could split the problem over the prime factors and finish
far below `√|G|`; a `√|G|` bound is only true to begin with at prime order.

### Putting it together

If the run returned some `k`, then correctness inside the realized group forces `(k : ZMod p) = X`
for *every* good `X` (`out_forces`), and two distinct good values contradict each other. So the run
never finishes within budget `B`, and therefore costs at least `B` real group operations.

`sqrt_le_groupOps_of_solvesDLog` picks a prime `p ≥ max N 100` and `B := Nat.sqrt p / 5`: small
enough for `n² + 2 ≤ p` above, large enough that `Nat.sqrt p ≤ 10 * B`.

## Main results

- `SolvesDLog`: the correctness hypothesis, quantified over every finite group.
- `solvesDLog_bruteForceDLog`: brute force satisfies it, so the bound is not vacuous.
- `exists_group_sqrt_le_groupOps`: for every `N` there is a group of order at least `N` and a
  secret in it on which the algorithm spends at least `√|G| / 10` group operations.
- `dlog_generic_lower_bound`: the same statement in the `∃ c > 0` form.

## References

Victor Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, EUROCRYPT 1997.

Ueli Maurer, *Abstract Models of Computation in Cryptography*, IMA 2005.
-/

@[expose] public section

namespace Algolean

namespace LowerBounds

open Algorithms Cslib

/-!
## Solving the discrete logarithm

The correctness hypothesis. It asks the algorithm to return *a* discrete logarithm of `x • g` to
base `g` — not the least one — in every finite group, run at that group's own order.
-/

/--
`SolvesDLog alg` says that `alg`, run in any finite group at that group's order, on the base `g`
and the target `x • g`, returns a discrete logarithm of the target.
-/
def SolvesDLog (alg : GroupAlg 2 ℕ) : Prop :=
  ∀ (G : Type) [Fintype G] [AddCommGroup G] [DecidableEq G] (g : G) (x : ℕ),
    GroupProg.eval (alg G (Fintype.card G) (dlogInputs g (x • g))) • g = x • g

/-- **Brute force solves the discrete logarithm**, so the lower bound below is not vacuous. -/
theorem solvesDLog_bruteForceDLog : SolvesDLog bruteForceDLog :=
  fun _ _ _ _ => bruteForceDLog_eval_nsmul

/-!
## The symbolic simulation

Everything in this section is the proof device: labels carrying linear forms, a simulator that
runs a program against them, and the extraction of a real group from a symbolic run.
-/

namespace Shoup

variable {p : ℕ} {α ι : Type}

/-! ### Labels and linear forms -/

/-- Labels: the carrier of the groups we construct. This is a type synonym for `ZMod p` so that
Lean never picks up the ring structure of `ZMod p` by accident. -/
private def Lbl (p : ℕ) : Type := ZMod p

private instance instDecEqLbl : DecidableEq (Lbl p) := inferInstanceAs (DecidableEq (ZMod p))
private instance instInhabitedLbl : Inhabited (Lbl p) := ⟨(0 : ZMod p)⟩
private instance instFintypeLbl [NeZero p] : Fintype (Lbl p) := inferInstanceAs (Fintype (ZMod p))

private lemma card_Lbl (p : ℕ) [NeZero p] : Fintype.card (Lbl p) = p := ZMod.card p

/-- The equivalence between `Lbl p` and `ZMod p`, the only way across the synonym. -/
private def lblEquiv (p : ℕ) : Lbl p ≃ ZMod p := Equiv.refl _

/-- A linear form `a + b * X` over `ZMod p`, recorded as the pair `(a, b)`. -/
private abbrev Frm (p : ℕ) := ZMod p × ZMod p

/-- Evaluate a linear form at `X`. -/
private def Frm.ev (f : Frm p) (X : ZMod p) : ZMod p := f.1 + f.2 * X

@[simp] private lemma Frm.ev_add (f g : Frm p) (X : ZMod p) : (f + g).ev X = f.ev X + g.ev X := by
  simp only [Frm.ev, Prod.fst_add, Prod.snd_add, add_mul]; ring

@[simp] private lemma Frm.ev_neg (f : Frm p) (X : ZMod p) : (-f).ev X = -f.ev X := by
  simp only [Frm.ev, Prod.fst_neg, Prod.snd_neg, neg_mul]; ring

/-! ### The simulator state -/

/-- The simulator's state: which label carries which form. -/
private abbrev St (p : ℕ) := List (Lbl p × Frm p)

/-- The form attached to a label, if any. -/
private def lookLbl (s : St p) (l : Lbl p) : Option (Frm p) :=
  (s.find? fun e => e.1 = l).map Prod.snd

/-- The label attached to a form, if any. -/
private def lookFrm (s : St p) (f : Frm p) : Option (Lbl p) :=
  (s.find? fun e => e.2 = f).map Prod.fst

private lemma mem_of_lookLbl {s : St p} {l : Lbl p} {f : Frm p} (h : lookLbl s l = some f) :
    (l, f) ∈ s := by
  simp only [lookLbl, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  obtain rfl : e.1 = l := by simpa using List.find?_some he
  simpa using List.mem_of_find?_eq_some he

private lemma mem_of_lookFrm {s : St p} {l : Lbl p} {f : Frm p} (h : lookFrm s f = some l) :
    (l, f) ∈ s := by
  simp only [lookFrm, Option.map_eq_some_iff] at h
  obtain ⟨e, he, rfl⟩ := h
  obtain rfl : e.2 = f := by simpa using List.find?_some he
  simpa using List.mem_of_find?_eq_some he

private lemma lookLbl_eq_none {s : St p} {l : Lbl p} :
    lookLbl s l = none ↔ l ∉ s.map Prod.fst := by
  simp only [lookLbl, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, List.mem_map,
    not_exists, not_and]

private lemma lookFrm_eq_none {s : St p} {f : Frm p} :
    lookFrm s f = none ↔ f ∉ s.map Prod.snd := by
  simp only [lookFrm, Option.map_eq_none_iff, List.find?_eq_none, decide_eq_true_eq, List.mem_map,
    not_exists, not_and]

/-! ### Fresh labels and forms

A state of fewer than `p` entries cannot have used up all `p` labels, nor all `p²` forms. -/

/-- Pigeonhole: a short state misses some value of any `p`-element (or larger) type. -/
private lemma exists_fresh {β : Type} [Fintype β] (hβ : p ≤ Fintype.card β)
    (k : Lbl p × Frm p → β) {s : St p} (hlen : s.length < p) : ∃ b : β, b ∉ s.map k := by
  classical
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (s.map k).toFinset) (t := (Finset.univ : Finset β)) <| by
      have h := List.toFinset_card_le (s.map k)
      rw [List.length_map] at h
      rw [Finset.card_univ]
      omega
  exact ⟨b, fun hm => hb (List.mem_toFinset.2 hm)⟩

/-- A label no entry of `s` uses (junk if there is none). -/
private noncomputable def freshLbl (s : St p) : Lbl p :=
  Classical.epsilon fun l => lookLbl s l = none

/-- A form no entry of `s` uses (junk if there is none). -/
private noncomputable def freshFrm (s : St p) : Frm p :=
  Classical.epsilon fun f => lookFrm s f = none

private lemma freshLbl_spec [NeZero p] {s : St p} (h : s.length < p) :
    lookLbl s (freshLbl s) = none :=
  Classical.epsilon_spec <| by
    obtain ⟨l, hl⟩ := exists_fresh (β := Lbl p) (card_Lbl p).ge Prod.fst h
    exact ⟨l, lookLbl_eq_none.2 hl⟩

private lemma freshFrm_spec [NeZero p] {s : St p} (h : s.length < p) :
    lookFrm s (freshFrm s) = none :=
  Classical.epsilon_spec <| by
    obtain ⟨f, hf⟩ := exists_fresh (β := Frm p)
      (by rw [Fintype.card_prod, ZMod.card]; exact Nat.le_mul_of_pos_left p (NeZero.pos p))
      Prod.snd h
    exact ⟨f, lookFrm_eq_none.2 hf⟩

/-! ### The state transitions -/

/-- Make sure `l` has a form attached: a label the algorithm produced out of thin air is given a
form nothing else uses. -/
private noncomputable def ensure (s : St p) (l : Lbl p) : St p :=
  match lookLbl s l with
  | some _ => s
  | none => (l, freshFrm s) :: s

/-- The label carrying the form `f`, allocating a fresh one if there is none. -/
private noncomputable def addFrm (s : St p) (f : Frm p) : Lbl p × St p :=
  match lookFrm s f with
  | some l => (l, s)
  | none => (freshLbl s, (freshLbl s, f) :: s)

/--
The simulator's answer to one query, together with the state it leaves behind. `eq` is answered by
label equality and changes nothing; `add` and `neg` `ensure` their operands carry forms and then
look up the label of the resulting form.
-/
private noncomputable def step : GroupQuery (Lbl p) ι → St p → ι × St p
  | .add x y, s =>
      addFrm (ensure (ensure s x) y)
        ((lookLbl (ensure (ensure s x) y) x).getD 0 + (lookLbl (ensure (ensure s x) y) y).getD 0)
  | .neg x, s => addFrm (ensure s x) (-(lookLbl (ensure s x) x).getD 0)
  | .eq x y, s => (decide (x = y), s)

private lemma charge_groupOps_le_one (q : GroupQuery (Lbl p) ι) : q.charge.groupOps ≤ 1 := by
  cases q <;> simp [GroupQuery.charge, GroupCosts.groupOps]

/-! ### The state only grows, and slowly -/

private lemma ensure_sublist (s : St p) (l : Lbl p) : s.Sublist (ensure s l) := by
  unfold ensure; split
  · exact .refl _
  · exact List.sublist_cons_self _ _

private lemma addFrm_sublist (s : St p) (f : Frm p) : s.Sublist (addFrm s f).2 := by
  unfold addFrm; split
  · exact .refl _
  · exact List.sublist_cons_self _ _

private lemma ensure_length (s : St p) (l : Lbl p) : (ensure s l).length ≤ s.length + 1 := by
  unfold ensure; split <;> simp

private lemma addFrm_length (s : St p) (f : Frm p) : (addFrm s f).2.length ≤ s.length + 1 := by
  unfold addFrm; split <;> simp

@[simp] private lemma lookLbl_cons_self (l : Lbl p) (f : Frm p) (s : St p) :
    lookLbl ((l, f) :: s) l = some f := by
  simp [lookLbl, List.find?_cons_of_pos]

/-- After `ensure s l`, the label `l` does carry a form. -/
private lemma ensure_lookLbl_self (s : St p) (l : Lbl p) :
    ∃ f, lookLbl (ensure s l) l = some f := by
  unfold ensure; split
  · next f h => exact ⟨f, h⟩
  · exact ⟨_, lookLbl_cons_self _ _ _⟩

/-- `ensure` never disturbs a form already recorded. -/
private lemma lookLbl_ensure {s : St p} {l : Lbl p} {f : Frm p} (l' : Lbl p)
    (h : lookLbl s l = some f) : lookLbl (ensure s l') l = some f := by
  unfold ensure; split
  · exact h
  · next hnone =>
    have hne : l' ≠ l := by rintro rfl; rw [hnone] at h; simp at h
    simp [lookLbl, List.find?_cons_of_neg, hne, ← h]

/-- The label `addFrm` returns does carry the form asked for. -/
private lemma addFrm_mem (s : St p) (f : Frm p) : ((addFrm s f).1, f) ∈ (addFrm s f).2 := by
  unfold addFrm; split
  · next l h => exact mem_of_lookFrm h
  · simp

private lemma step_sublist (q : GroupQuery (Lbl p) ι) (s : St p) : s.Sublist (step q s).2 := by
  cases q with
  | add x y => exact ((ensure_sublist s _).trans (ensure_sublist _ _)).trans (addFrm_sublist _ _)
  | neg x => exact (ensure_sublist s _).trans (addFrm_sublist _ _)
  | eq x y => exact .refl _

/-- Only element-producing queries extend the state, and each by at most three entries. -/
private lemma step_length (q : GroupQuery (Lbl p) ι) (s : St p) :
    (step q s).2.length ≤ s.length + 3 * q.charge.groupOps := by
  cases q with
  | add x y =>
      have h1 := ensure_length s x
      have h2 := ensure_length (ensure s x) y
      refine le_trans (addFrm_length _ _) ?_
      simp only [GroupQuery.groupOps_charge_add]
      omega
  | neg x =>
      have h1 := ensure_length s x
      refine le_trans (addFrm_length _ _) ?_
      simp only [GroupQuery.groupOps_charge_neg]
      omega
  | eq x y => exact Nat.le_add_right _ _

/-! ### The `Nodup` invariant -/

/-- Both the labels and the forms occurring in the state are duplicate-free. -/
private def NodupSt (s : St p) : Prop := (s.map Prod.fst).Nodup ∧ (s.map Prod.snd).Nodup

private lemma nodupSt_cons {s : St p} {l : Lbl p} {f : Frm p} (hl : lookLbl s l = none)
    (hf : lookFrm s f = none) (hs : NodupSt s) : NodupSt ((l, f) :: s) :=
  ⟨List.nodup_cons.2 ⟨lookLbl_eq_none.1 hl, hs.1⟩, List.nodup_cons.2 ⟨lookFrm_eq_none.1 hf, hs.2⟩⟩

private lemma ensure_nodup [NeZero p] {s : St p} (hlen : s.length < p) (hs : NodupSt s)
    (l : Lbl p) : NodupSt (ensure s l) := by
  unfold ensure; split
  · exact hs
  · next h => exact nodupSt_cons h (freshFrm_spec hlen) hs

private lemma addFrm_nodup [NeZero p] {s : St p} (hlen : s.length < p) (hs : NodupSt s)
    (f : Frm p) : NodupSt (addFrm s f).2 := by
  unfold addFrm; split
  · exact hs
  · next h => exact nodupSt_cons (freshLbl_spec hlen) h hs

private lemma step_nodup [NeZero p] (q : GroupQuery (Lbl p) ι) {s : St p}
    (hlen : s.length + 3 * q.charge.groupOps < p) (hs : NodupSt s) : NodupSt (step q s).2 := by
  cases q with
  | add x y =>
      simp only [GroupQuery.groupOps_charge_add] at hlen
      have h1 := ensure_length s x
      have h2 := ensure_length (ensure s x) y
      exact addFrm_nodup (by omega) (ensure_nodup (by omega) (ensure_nodup (by omega) hs x) y) _
  | neg x =>
      simp only [GroupQuery.groupOps_charge_neg] at hlen
      have h1 := ensure_length s x
      exact addFrm_nodup (by omega) (ensure_nodup (by omega) hs x) _
  | eq x y => exact hs

/-! ### The simulator -/

/-- The outcome of a symbolic run. -/
private structure Res (p : ℕ) (α : Type) where
  /-- The value the simulated program returned, or `none` if the budget ran out first. -/
  out : Option α
  /-- The state the simulation stopped in. -/
  st : St p
  /-- The number of element-producing queries the simulation charged. -/
  cost : ℕ

/-- Charge `c` group operations to a result. -/
private def Res.bump (c : ℕ) (r : Res p α) : Res p α := ⟨r.out, r.st, c + r.cost⟩

@[simp] private lemma Res.bump_out (c : ℕ) (r : Res p α) : (Res.bump c r).out = r.out := rfl
@[simp] private lemma Res.bump_st (c : ℕ) (r : Res p α) : (Res.bump c r).st = r.st := rfl
@[simp] private lemma Res.bump_cost (c : ℕ) (r : Res p α) : (Res.bump c r).cost = c + r.cost := rfl

/-- The symbolic run of a program: `step` answers the queries, and `B` bounds the number of
element-producing ones the run may make. -/
private noncomputable def sim : GroupProg (Lbl p) α → St p → ℕ → Res p α
  | .pure a, s, _ => ⟨some a, s, 0⟩
  | .liftBind q cont, s, B =>
      if q.charge.groupOps ≤ B then
        Res.bump q.charge.groupOps (sim (cont (step q s).1) (step q s).2 (B - q.charge.groupOps))
      else ⟨none, s, 0⟩

private lemma sim_pure (a : α) (s : St p) (B : ℕ) :
    sim (.pure a : GroupProg (Lbl p) α) s B = ⟨some a, s, 0⟩ := by
  rw [sim]

private lemma sim_liftBind (q : GroupQuery (Lbl p) ι) (cont : ι → GroupProg (Lbl p) α) (s : St p)
    (B : ℕ) :
    sim (.liftBind q cont) s B =
      if q.charge.groupOps ≤ B then
        Res.bump q.charge.groupOps (sim (cont (step q s).1) (step q s).2 (B - q.charge.groupOps))
      else ⟨none, s, 0⟩ := by
  rw [sim]

private lemma sim_sublist (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    s.Sublist (sim P s B).st := by
  induction P generalizing s B with
  | pure a => exact .refl _
  | liftBind q cont ih =>
      rw [sim_liftBind]
      split
      · exact (step_sublist q s).trans (ih _ _ _)
      · exact .refl _

private lemma sim_length (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) :
    (sim P s B).st.length ≤ s.length + 3 * B := by
  induction P generalizing s B with
  | pure a => exact Nat.le_add_right _ _
  | liftBind q cont ih =>
      rw [sim_liftBind]
      split
      · next hfuel =>
        have h1 := step_length q s
        have h2 := ih (step q s).1 (step q s).2 (B - q.charge.groupOps)
        simp only [Res.bump_st]
        omega
      · exact Nat.le_add_right _ _

private lemma sim_nodup [NeZero p] (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ)
    (hlen : s.length + 3 * B < p) (hs : NodupSt s) : NodupSt (sim P s B).st := by
  induction P generalizing s B with
  | pure a => exact hs
  | liftBind q cont ih =>
      rw [sim_liftBind]
      split
      · next hfuel =>
        have h1 := step_length q s
        exact ih _ _ _ (by omega) (step_nodup q (by omega) hs)
      · exact hs

/-- A run that was cut off spent the whole budget. -/
private lemma sim_cost_of_none (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ)
    (h : (sim P s B).out = none) : (sim P s B).cost = B := by
  induction P generalizing s B with
  | pure a => rw [sim_pure] at h; simp at h
  | liftBind q cont ih =>
      rw [sim_liftBind] at h ⊢
      split at h
      · next hfuel =>
        rw [if_pos hfuel, Res.bump_cost, ih _ _ _ h]
        omega
      · next hfuel =>
        have := charge_groupOps_le_one q
        rw [if_neg hfuel]
        change (0 : ℕ) = B
        omega

/-! ### Soundness of the simulation

If a group structure on `Lbl p` is compatible, via the additive equivalence `E`, with the forms
recorded in the final state `ψ`, then the simulation tracked a real execution: it never
overcounted, and whatever it output is what the real run outputs. -/

/-- The simulator's answer to a query is the answer the realized group gives. For `add` this says
the label handed back really is the sum: `E` is injective and sends it to `(u + v).ev X`, which is
`E x + E y = E (x + y)`. -/
private lemma step_answer [AddCommGroup (Lbl p)] (E : Lbl p ≃+ ZMod p) {X : ZMod p} (ψ : St p)
    (hagree : ∀ l f, (l, f) ∈ ψ → E l = Frm.ev f X)
    (q : GroupQuery (Lbl p) ι) (s : St p) (hsub : (step q s).2.Sublist ψ) :
    (step q s).1 = q.answer := by
  cases q with
  | eq x y => rfl
  | add x y =>
      obtain ⟨u, hu⟩ := ensure_lookLbl_self s x
      obtain ⟨v, hv⟩ := ensure_lookLbl_self (ensure s x) y
      have hu' : lookLbl (ensure (ensure s x) y) x = some u := lookLbl_ensure y hu
      have hstep : step (GroupQuery.add x y) s = addFrm (ensure (ensure s x) y) (u + v) := by
        simp [step, hu', hv]
      rw [hstep] at hsub ⊢
      refine E.injective ?_
      rw [GroupQuery.answer_add, map_add, hagree _ _ (hsub.mem (addFrm_mem _ _)),
        hagree _ _ (hsub.mem ((addFrm_sublist _ _).mem (mem_of_lookLbl hu'))),
        hagree _ _ (hsub.mem ((addFrm_sublist _ _).mem (mem_of_lookLbl hv))), Frm.ev_add]
  | neg x =>
      obtain ⟨u, hu⟩ := ensure_lookLbl_self s x
      have hstep : step (GroupQuery.neg x) s = addFrm (ensure s x) (-u) := by simp [step, hu]
      rw [hstep] at hsub ⊢
      refine E.injective ?_
      rw [GroupQuery.answer_neg, map_neg, hagree _ _ (hsub.mem (addFrm_mem _ _)),
        hagree _ _ (hsub.mem ((addFrm_sublist _ _).mem (mem_of_lookLbl hu))), Frm.ev_neg]

private lemma sim_sound [AddCommGroup (Lbl p)] (E : Lbl p ≃+ ZMod p) {X : ZMod p} (ψ : St p)
    (hagree : ∀ l f, (l, f) ∈ ψ → E l = Frm.ev f X)
    (P : GroupProg (Lbl p) α) (s : St p) (B : ℕ) (hst : (sim P s B).st = ψ) :
    (sim P s B).cost ≤ GroupProg.groupOps P ∧
      ∀ a, (sim P s B).out = some a → GroupProg.eval P = a := by
  induction P generalizing s B with
  | pure a =>
      rw [sim_pure]
      exact ⟨Nat.zero_le _, fun a' h => by simpa using Option.some.inj h⟩
  | liftBind q cont ih =>
      by_cases hfuel : q.charge.groupOps ≤ B
      · rw [sim_liftBind, if_pos hfuel] at hst ⊢
        rw [Res.bump_st] at hst
        have hkey : (step q s).1 = q.answer :=
          step_answer E ψ hagree q s (by rw [← hst]; exact sim_sublist _ _ _)
        obtain ⟨ihc, iho⟩ := ih _ _ _ hst
        rw [hkey] at ihc iho ⊢
        rw [GroupProg.groupOps_liftBind, GroupProg.eval_liftBind]
        exact ⟨by simp only [Res.bump_cost]; omega, iho⟩
      · rw [sim_liftBind, if_neg hfuel]
        exact ⟨Nat.zero_le _, by simp⟩

/-! ### Counting the good specializations -/

/-- `X` is *good* for `ψ` when distinct forms recorded in `ψ` take distinct values at `X`. -/
private def Good (ψ : St p) (X : ZMod p) : Prop :=
  ∀ f ∈ ψ.map Prod.snd, ∀ f' ∈ ψ.map Prod.snd, Frm.ev f X = Frm.ev f' X → f = f'

/-- The unique point at which two forms of different slopes agree. -/
private noncomputable def collide [Fact p.Prime] (f f' : Frm p) : ZMod p :=
  (f'.1 - f.1) / (f.2 - f'.2)

private lemma collide_eq [Fact p.Prime] {f f' : Frm p} {X : ZMod p} (hne : f ≠ f')
    (h : Frm.ev f X = Frm.ev f' X) : X = collide f f' := by
  simp only [Frm.ev] at h
  have hslope : f.2 ≠ f'.2 := fun hs =>
    hne (Prod.ext (by rw [hs] at h; exact add_right_cancel h) hs)
  rw [collide, eq_div_iff (sub_ne_zero.2 hslope)]
  linear_combination h

/-- At most `|ψ|²` values of `X` are bad, so two good ones survive once `|ψ|² + 2 ≤ p`. -/
private lemma exists_two_good [Fact p.Prime] (ψ : St p) (hlen : ψ.length * ψ.length + 2 ≤ p) :
    ∃ X₁ X₂ : ZMod p, X₁ ≠ X₂ ∧ Good ψ X₁ ∧ Good ψ X₂ := by
  classical
  set F := (ψ.map Prod.snd).toFinset with hF
  have hFcard : F.card ≤ ψ.length := by simpa [hF] using List.toFinset_card_le (ψ.map Prod.snd)
  have hbad : (Finset.univ.filter fun X : ZMod p => ¬ Good ψ X).card ≤ ψ.length * ψ.length := by
    have hsub : (Finset.univ.filter fun X : ZMod p => ¬ Good ψ X) ⊆
        (F ×ˢ F).image fun q => collide q.1 q.2 := by
      intro X hX
      have hX2 := (Finset.mem_filter.1 hX).2
      rw [Good] at hX2
      push Not at hX2
      obtain ⟨f, hf, f', hf', hev, hne⟩ := hX2
      exact Finset.mem_image.2 ⟨(f, f'),
        Finset.mem_product.2 ⟨List.mem_toFinset.2 hf, List.mem_toFinset.2 hf'⟩,
        (collide_eq hne hev).symm⟩
    calc _ ≤ ((F ×ˢ F).image fun q => collide q.1 q.2).card := Finset.card_le_card hsub
      _ ≤ (F ×ˢ F).card := Finset.card_image_le
      _ = F.card * F.card := Finset.card_product _ _
      _ ≤ ψ.length * ψ.length := Nat.mul_le_mul hFcard hFcard
  have hsplit : (Finset.univ.filter fun X : ZMod p => Good ψ X).card
      + (Finset.univ.filter fun X : ZMod p => ¬ Good ψ X).card = p := by
    rw [Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
      (p := fun X : ZMod p => Good ψ X), Finset.card_univ, ZMod.card]
  obtain ⟨X₁, h1, X₂, h2, hne⟩ :=
    Finset.one_lt_card.1 (show 1 < (Finset.univ.filter fun X : ZMod p => Good ψ X).card by omega)
  exact ⟨X₁, X₂, hne, (Finset.mem_filter.1 h1).2, (Finset.mem_filter.1 h2).2⟩

/-- From a good `X` we obtain a permutation of `ZMod p` realizing every form of `ψ`: with distinct
labels on one side and distinct values on the other, `label ↦ form.ev X` is a partial injection. -/
private lemma exists_perm [NeZero p] {ψ : St p} (hnd : NodupSt ψ) {X : ZMod p} (hgood : Good ψ X) :
    ∃ σ : Equiv.Perm (ZMod p), ∀ l f, (l, f) ∈ ψ → σ l = Frm.ev f X := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun q : {q : Lbl p × Frm p // q ∈ ψ} => (q.1.1 : ZMod p)) (fun q => Frm.ev q.1.2 X)
    (by rintro ⟨⟨l, f⟩, hm⟩ ⟨⟨l', f'⟩, hm'⟩ h
        exact Subtype.ext (List.inj_on_of_nodup_map hnd.1 hm hm' h))
    (by rintro ⟨⟨l, f⟩, hm⟩ ⟨⟨l', f'⟩, hm'⟩ h
        exact Subtype.ext (List.inj_on_of_nodup_map hnd.2 hm hm'
          (hgood f (List.mem_map_of_mem hm) f' (List.mem_map_of_mem hm') h)))
  exact ⟨σ, fun l f hm => hσ ⟨(l, f), hm⟩⟩

/-! ### The distinguished generator and challenge -/

/-- The label playing the role of the generator. -/
private def lblG (p : ℕ) : Lbl p := (0 : ZMod p)

/-- The label playing the role of the challenge `x • g`. -/
private def lblH (p : ℕ) : Lbl p := (1 : ZMod p)

/-- The initial state: `g` has form `1` and `H` has form `X`. -/
private def st0 (p : ℕ) : St p :=
  [(lblG p, ((1 : ZMod p), (0 : ZMod p))), (lblH p, ((0 : ZMod p), (1 : ZMod p)))]

private lemma st0_length (p : ℕ) : (st0 p).length = 2 := rfl

private lemma mem_st0_G (p : ℕ) : (lblG p, ((1 : ZMod p), (0 : ZMod p))) ∈ st0 p := by simp [st0]

private lemma mem_st0_H (p : ℕ) : (lblH p, ((0 : ZMod p), (1 : ZMod p))) ∈ st0 p := by simp [st0]

private lemma st0_nodup [Fact p.Prime] : NodupSt (st0 p) := by
  have h : lblG p ≠ lblH p := fun hh => (zero_ne_one : (0 : ZMod p) ≠ 1) hh
  exact ⟨by simp [st0, h], by simp [st0, Prod.ext_iff]⟩

/-! ### The two halves of the argument -/

section Main

variable {alg : GroupAlg 2 ℕ} {B : ℕ}

/-- The one program the argument watches: `alg` run on the two fixed labels. -/
private def dlogProg (alg : GroupAlg 2 ℕ) (p : ℕ) : GroupProg (Lbl p) ℕ :=
  alg (Lbl p) p (dlogInputs (lblG p) (lblH p))

/-- Its symbolic run on a budget of `B` group operations. -/
private noncomputable def dlogRun (alg : GroupAlg 2 ℕ) (p B : ℕ) : Res p ℕ :=
  sim (dlogProg alg p) (st0 p) B

/--
**From a symbolic run to a real one.** A good `X` turns the record of the run into an actual group:
`exists_perm` realizes `label ↦ form.ev X` as a permutation of `ZMod p`, and `Equiv.addCommGroup`
transports the group structure of `ZMod p` back along it. In that group the generator label is `1`
and the challenge label is `X`, so `X.val • g = h`; and by `sim_sound` the run we watched is a real
one.
-/
private lemma realize [Fact p.Prime] (hnd : NodupSt (dlogRun alg p B).st) {X : ZMod p}
    (hgood : Good (dlogRun alg p B).st X) {motive : Prop}
    (H : ∀ [AddCommGroup (Lbl p)],
      X.val • lblG p = lblH p →
      (∀ n : ℕ, n • lblG p = lblH p → (n : ZMod p) = X) →
      (dlogRun alg p B).cost ≤ GroupProg.groupOps (dlogProg alg p) →
      (∀ k : ℕ, (dlogRun alg p B).out = some k → GroupProg.eval (dlogProg alg p) = k) →
      motive) :
    motive := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨σ, hσ⟩ := exists_perm hnd hgood
  letI e : Lbl p ≃ ZMod p := (lblEquiv p).trans σ
  letI inst : AddCommGroup (Lbl p) := Equiv.addCommGroup e
  letI E : Lbl p ≃+ ZMod p := ⟨e, fun x y => map_add (Equiv.addEquiv e) x y⟩
  have hsub0 : (st0 p).Sublist (dlogRun alg p B).st := sim_sublist _ _ _
  have hE : ∀ l f, (l, f) ∈ (dlogRun alg p B).st → E l = Frm.ev f X := fun l f hm => hσ l f hm
  have heg : E (lblG p) = 1 := by
    rw [hE _ _ (hsub0.mem (mem_st0_G p))]; simp [Frm.ev]
  have heH : E (lblH p) = X := by
    rw [hE _ _ (hsub0.mem (mem_st0_H p))]; simp [Frm.ev]
  have hn : ∀ n : ℕ, E (n • lblG p) = (n : ZMod p) := fun n => by
    rw [map_nsmul, heg, nsmul_eq_mul, mul_one]
  obtain ⟨hc, ho⟩ := sim_sound E _ hE (dlogProg alg p) (st0 p) B rfl
  exact H (E.injective (by rw [hn, heH]; exact ZMod.natCast_rightInverse X))
    (fun n hne => by rw [← hn n, hne, heH]) hc ho

/-- If the run terminates with output `k`, then `k` is forced to equal every good `X` — which is
impossible once there are two of them. -/
private lemma out_forces [Fact p.Prime] (hcorrect : SolvesDLog alg)
    (hnd : NodupSt (dlogRun alg p B).st) {X : ZMod p} (hgood : Good (dlogRun alg p B).st X)
    {k : ℕ} (hout : (dlogRun alg p B).out = some k) : (k : ZMod p) = X := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine realize hnd hgood ?_
  intro inst hxg hforce _ hev
  refine hforce k ?_
  have hC := hcorrect (Lbl p) (lblG p) X.val
  rw [card_Lbl, hxg] at hC
  rw [← hev k hout]
  exact hC

/-- The final assembly: for every `N` there is a group of order at least `N`, and a secret in it,
on which the algorithm spends at least `√|G| / 10` group operations. -/
private lemma sqrt_le_groupOps_of_solvesDLog (alg : GroupAlg 2 ℕ) (hcorrect : SolvesDLog alg)
    (N : ℕ) :
    ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
      N ≤ Fintype.card G ∧ x < Fintype.card G ∧
        Nat.sqrt (Fintype.card G) ≤
          10 * GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) := by
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (max N 100)
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hpN : N ≤ p := le_trans (le_max_left N 100) hpge
  have hp100 : 100 ≤ p := le_trans (le_max_right N 100) hpge
  have hM : 10 ≤ Nat.sqrt p := Nat.le_sqrt.mpr (by omega)
  have hMsq : Nat.sqrt p * Nat.sqrt p ≤ p := Nat.sqrt_le p
  have h10M : 10 * Nat.sqrt p ≤ p := le_trans (Nat.mul_le_mul_right _ hM) hMsq
  set B := Nat.sqrt p / 5 with hB
  have hnd : NodupSt (dlogRun alg p B).st :=
    sim_nodup _ _ _ (by rw [st0_length]; omega) st0_nodup
  have hlenR : (dlogRun alg p B).st.length + 2 ≤ Nat.sqrt p := by
    have h : (dlogRun alg p B).st.length ≤ (st0 p).length + 3 * B := sim_length _ _ _
    rw [st0_length] at h
    omega
  have hsq : (dlogRun alg p B).st.length * (dlogRun alg p B).st.length + 2 ≤ p := by
    set L := (dlogRun alg p B).st.length
    calc L * L + 2 ≤ (L + 2) * (L + 2) := by nlinarith
      _ ≤ Nat.sqrt p * Nat.sqrt p := Nat.mul_le_mul hlenR hlenR
      _ ≤ p := hMsq
  obtain ⟨X₁, X₂, hne, hg1, hg2⟩ := exists_two_good _ hsq
  by_cases hout : ∃ k, (dlogRun alg p B).out = some k
  · obtain ⟨k, hk⟩ := hout
    exact absurd ((out_forces hcorrect hnd hg1 hk).symm.trans (out_forces hcorrect hnd hg2 hk)) hne
  · have hnone : (dlogRun alg p B).out = none := by
      cases hR : (dlogRun alg p B).out with
      | none => rfl
      | some k => exact absurd ⟨k, hR⟩ hout
    have hcostB : (dlogRun alg p B).cost = B := sim_cost_of_none _ _ _ hnone
    refine realize hnd hg1 ?_
    intro inst hxg _ hcost _
    refine ⟨Lbl p, instFintypeLbl, inst, instDecEqLbl, lblG p, X₁.val, ?_, ?_, ?_⟩
    · rw [card_Lbl]; exact hpN
    · rw [card_Lbl]; exact ZMod.val_lt X₁
    · rw [card_Lbl, hxg]
      change Nat.sqrt p ≤ 10 * GroupProg.groupOps (dlogProg alg p)
      omega

end Main

end Shoup

/-!
## The bound
-/

/--
**The generic group lower bound for the discrete logarithm.** An algorithm that solves the
discrete logarithm in *every* finite group cannot be efficient in all of them: for every `N` there
is a group of order at least `N`, and a secret in it, on which the algorithm spends at least
`√|G| / 10` group operations.

Note the order of the quantifiers. The algorithm is fixed first, and is handed only the carrier
and the order; the group is produced afterwards, by the proof, out of the run it has just watched.
The existential is not slack: the same statement with the group named in advance is false.
-/
theorem exists_group_sqrt_le_groupOps {alg : GroupAlg 2 ℕ} (hcorrect : SolvesDLog alg) (N : ℕ) :
    ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
      N ≤ Fintype.card G ∧ x < Fintype.card G ∧
        Nat.sqrt (Fintype.card G) ≤
          10 * GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) :=
  Shoup.sqrt_le_groupOps_of_solvesDLog alg hcorrect N

/--
**The same bound, in the `Ω(√|G|)` form.** There is a positive constant `c` such that every
correct generic algorithm is, on arbitrarily large groups, forced to spend `c * √|G|` group
operations on some secret.
-/
theorem dlog_generic_lower_bound :
    ∃ c > (0 : ℚ), ∀ alg : GroupAlg 2 ℕ, SolvesDLog alg → ∀ N : ℕ,
      ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
        N ≤ Fintype.card G ∧ x < Fintype.card G ∧
          c * (Nat.sqrt (Fintype.card G) : ℚ) ≤
            (GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) : ℚ) := by
  refine ⟨1 / 10, by norm_num, fun alg hcorrect N => ?_⟩
  obtain ⟨G, instF, instA, instD, g, x, hcard, hx, hcost⟩ :=
    exists_group_sqrt_le_groupOps hcorrect N
  refine ⟨G, instF, instA, instD, g, x, hcard, hx, ?_⟩
  have hq : (Nat.sqrt (Fintype.card G) : ℚ) ≤
      10 * (GroupProg.groupOps (alg G (Fintype.card G) (dlogInputs g (x • g))) : ℚ) := by
    exact_mod_cast hcost
  linarith

end LowerBounds

end Algolean
