/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Algorithms.BabyStepGiantStep
public import Algolean.Algorithms.DiscreteLog
public import Algolean.LowerBounds.DiscreteLog
public meta import Mathlib.Tactic.NormNum.Prime
public meta import Algolean.Algorithms.BabyStepGiantStep
public meta import Algolean.Algorithms.DiscreteLog
public meta import Algolean.Models.GenericGroup

/-!
# Examples of generic group programs
-/

@[expose] public section

namespace AlgoleanTests

open Cslib Algolean Algorithms LowerBounds Prog

section GroupExamples

variable {V G : Type}

/-- Quadrupling an element by repeated doubling: two `add` queries. -/
def quadruple (x : V) : GroupProg V V := do
  let d ← GroupProg.add x x
  GroupProg.add d d

/-- Quadrupling costs two `add` queries and nothing else, in whatever group it is run. -/
example [AddCommGroup G] [DecidableEq G] (x : G) : GroupProg.cost (quadruple x) = ⟨2, 0, 0⟩ := rfl

/-- Quadrupling asks for two group elements. -/
example [AddCommGroup G] [DecidableEq G] (x : G) : GroupProg.groupOps (quadruple x) = 2 := rfl

/-- And it returns four times its input. -/
example (a : ZMod 11) : GroupProg.eval (quadruple a) = (4 : ℕ) • a := by
  change a + a + (a + a) = (4 : ℕ) • a
  module

/-- Brute-force search finds the discrete logarithm of `5` to base `1` in `ZMod 11`. -/
example : GroupProg.eval (bruteForceDLog (ZMod 11) 11 (dlogInputs 1 5)) = 5 := by decide

/-- On the secret `0` the raw search returns the order rather than `0`, since it starts counting
at `1`. -/
example : GroupProg.eval (bruteForceDLog (ZMod 11) 11 (dlogInputs 5 0)) = 11 := by decide

/-- Read back in `ZMod p` that answer is the secret again, and `bruteForceDLog_eval_zmod` says so
for every secret and every base other than `0` in every group of order `p` — here the base `5`,
and not the base `1` that makes discrete logarithms in `ZMod 11` trivial to begin with. -/
example (x : ZMod 11) :
    GroupProg.eval ((fun n : ℕ => (n : ZMod 11)) <$>
      bruteForceDLog (ZMod 11) 11 (dlogInputs 5 (x.val • (5 : ZMod 11)))) = x :=
  bruteForceDLog_eval_zmod (by norm_num) (ZMod.card 11) (by decide) x

-- Baby-step giant-step finds the same discrete logarithm.
/-- info: 5 -/
#guard_msgs in
#eval GroupProg.eval (bsgs (ZMod 11) 11 (dlogInputs 1 5))

-- On its worst secret in `ZMod 101`, baby-step giant-step asks for far fewer group elements than
-- brute force does, which is the `O(√order)` of `bsgs_groupOps_le` against the `order` of
-- `bruteForceDLog_cost_le`.
/-- info: (97, 29, 96) -/
#guard_msgs in
#eval (GroupProg.eval (bsgs (ZMod 101) 101 (dlogInputs 1 97)),
  GroupProg.groupOps (bsgs (ZMod 101) 101 (dlogInputs 1 97)),
  GroupProg.groupOps (bruteForceDLog (ZMod 101) 101 (dlogInputs 1 97)))

-- Baby-step giant-step pays for its small number of `add` queries with a quadratic number of
-- comparisons: the model has no unit cost table lookup.
/-- info: (29, 91) -/
#guard_msgs in
#eval ((GroupProg.cost (bsgs (ZMod 101) 101 (dlogInputs 1 97))).adds,
  (GroupProg.cost (bsgs (ZMod 101) 101 (dlogInputs 1 97))).eqs)

/-- info: (96, 97) -/
#guard_msgs in
#eval ((GroupProg.cost (bruteForceDLog (ZMod 101) 101 (dlogInputs 1 97))).adds,
  (GroupProg.cost (bruteForceDLog (ZMod 101) 101 (dlogInputs 1 97))).eqs)

/-!
## One program, every group

Nothing in `bsgs` mentions a group: it is a `GroupAlg 2 ℕ`, a program uniformly in the type of
group elements, which receives the order as a number. The group enters only through the instances
that `GroupProg.eval` is read against, so the same code runs everywhere.
-/

/-- Baby-step giant-step in `ZMod 13`. -/
example : GroupProg.eval (bsgs (ZMod 13) 13 (dlogInputs 2 8)) • (2 : ZMod 13) = 8 :=
  bsgs_eval 2 8 (x := 4) (by norm_num) (by norm_num) (by decide)

/-- And in the additive group of `Fin 5 → ZMod 3`. -/
example : GroupProg.eval (bsgs (Fin 5 → ZMod 3) 3 (dlogInputs 1 2)) • (1 : Fin 5 → ZMod 3) = 2 :=
  bsgs_eval 1 2 (x := 2) (by norm_num) (by norm_num) (by decide)

/-!
## Correctness via `mvcgen`

The observables above are read off a program by `decide` or by unfolding. For a program with a loop
that does not scale, and it need not be done by hand: `Algolean.QueryModel` wires every query model
into `Std.Do`'s weakest-precondition framework, and `groupModel` is registered as the default
`HasModel (GroupQuery G)`, so the global `WP (Prog (GroupQuery G)) .pure` instance fires and Hoare
triples about a `GroupProg` are available.

Nothing has to be set up here. `GroupProg.add_spec`, `neg_spec` and `eq_spec` in
`Algolean.Models.GenericGroup` are tagged `@[spec]`, so `mvcgen` already knows what the oracle
answers each query with, and `GroupProg.eval_of_triple` reads a triple back as a statement about
`GroupProg.eval`.

Two things are worth keeping apart. This is reasoning about the *value* a program returns: the
`.pure` post-shape does not see cost, which stays with `GroupProg.cost`. And it is reasoning in a
fixed group, since `HasModel (GroupQuery G) GroupCosts` needs the instances — the programs stay
polymorphic in `V`, and the group is chosen when the triple is stated, exactly as with `eval`.
-/
section Mvcgen

open Std.Do

set_option mvcgen.warning false

variable [AddCommGroup G] [DecidableEq G]

/-- Quadrupling, now as a Hoare triple: the two `add` specs compose through the `bind` rule and
`mvcgen` leaves the group identity behind. -/
theorem quadruple_spec (x : G) :
    ⦃⌜True⌝⦄ quadruple x ⦃⇓r => ⌜r = (4 : ℕ) • x⌝⦄ := by
  mvcgen [quadruple]
  module

/-- `GroupProg.eval_of_triple` turns the triple back into a statement about `GroupProg.eval`,
which is the form the rest of this file is written in. -/
example (x : G) : GroupProg.eval (quadruple x) = (4 : ℕ) • x :=
  GroupProg.eval_of_triple (quadruple_spec x)

/-- Test whether `y` is the double of `x`: one `add` and one `eq`. -/
def isDouble (x y : V) : GroupProg V Bool := do
  let d ← GroupProg.add x x
  GroupProg.eq d y

/-- The oracle's answer to the comparison is the comparison in the group. -/
theorem isDouble_spec (x y : G) :
    ⦃⌜True⌝⦄ isDouble x y ⦃⇓r => ⌜r = true ↔ x + x = y⌝⦄ := by
  mvcgen [isDouble]
  simp

/-- The value a triple speaks about is not the cost: `isDouble` spends one `add` and one `eq` in
whatever group it is run, and that is still read off the syntax tree. -/
example (x y : G) : GroupProg.cost (isDouble x y) = ⟨1, 0, 1⟩ := rfl

/-- Repeated doubling: `k` `add` queries, reaching `2 ^ k` times the input. -/
def repeatedDouble (x : V) (k : ℕ) : GroupProg V V := do
  let mut acc := x
  for _ in List.range k do
    acc ← GroupProg.add acc acc
  return acc

/-- The loop is where `mvcgen` earns its keep: one invariant, and the three verification
conditions it generates are goals about `G` with no monad left in them. -/
theorem repeatedDouble_spec (x : G) (k : ℕ) :
    ⦃⌜True⌝⦄ repeatedDouble x k ⦃⇓r => ⌜r = (2 ^ k : ℕ) • x⌝⦄ := by
  mvcgen [repeatedDouble] invariants
    · ⇓⟨xs, acc⟩ => ⌜acc = (2 ^ xs.prefix.length : ℕ) • x⌝
  case vc1.step =>
    subst_vars
    simp only [List.length_append, List.length_cons, List.length_nil, pow_succ]
    module
  case vc2.pre => simp
  case vc3.post.success =>
    subst_vars
    simp

/-- Back to `eval`, and in every group at once: the loop invariant, not evaluation, is what
proves this. -/
theorem repeatedDouble_eval (x : G) (k : ℕ) :
    GroupProg.eval (repeatedDouble x k) = (2 ^ k : ℕ) • x :=
  GroupProg.eval_of_triple (repeatedDouble_spec x k)

/-- Read in a group: five doublings in `ZMod 11`. -/
example (x : ZMod 11) : GroupProg.eval (repeatedDouble x 5) = (32 : ℕ) • x :=
  repeatedDouble_eval x 5

end Mvcgen

/-!
## The lower bound is not vacuous

`Algolean.LowerBounds.exists_group_sqrt_le_groupOps` bounds every algorithm that solves the
discrete logarithm in all groups at once. Both algorithms here do, so there is something to bound.
-/

/-- Brute force meets the hypothesis of the lower bound. -/
example : SolvesDLog bruteForceDLog := solvesDLog_bruteForceDLog

/-- So does baby-step giant-step. -/
example : SolvesDLog bsgs := fun _ _ _ _ => bsgs_eval_nsmul

/-- So there are groups of order at least a million in which brute force is forced to spend at
least `√|G| / 10` group operations. -/
example :
    ∃ (G : Type) (_ : Fintype G) (_ : AddCommGroup G) (_ : DecidableEq G) (g : G) (x : ℕ),
      1000000 ≤ Fintype.card G ∧ x < Fintype.card G ∧
        Nat.sqrt (Fintype.card G) ≤
          10 * GroupProg.groupOps
            (bruteForceDLog G (Fintype.card G) (dlogInputs g (x • g))) :=
  exists_group_sqrt_le_groupOps solvesDLog_bruteForceDLog 1000000

end GroupExamples

end AlgoleanTests
