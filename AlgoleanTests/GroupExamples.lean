/-
Copyright (c) 2026 Franklin Harding. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Franklin Harding
-/

module

public import Algolean.Models.GenericGroup
public meta import Algolean.Models.GenericGroup

/-!
# Examples of generic group programs
-/

@[expose] public section

namespace AlgoleanTests

open Cslib Algolean Algorithms Prog

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
end GroupExamples

end AlgoleanTests
