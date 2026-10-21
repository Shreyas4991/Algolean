/-
Copyright (c) 2025 Tanner Duve (Logical Intelligence). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.FreeWP.Effects
public import Algolean.Models.ReadOnlyVec
public import Std.Tactic.Do

/-!
Examples for WP in `Algolean.FreeWP.WP`: instance resolution,
a `Triple` on a `FreeState` program discharged by `vcgen`, a custom `CounterF` effect with
its own logical handler, sum/failure/demonic effects, arbitrary relational operation specifications,
and — connecting the WP framework to this repository's query model — Hoare triples about
query-model programs `Prog Q α` against a handler derived from a `Model Q Cost` (illustrated on
`ReadOnlyVec`).
-/

@[expose] public section

set_option experimental.vcgen true

namespace AlgoleanTests.FreeMonadWP

open Cslib Cslib.FreeM Lean.Order Std.WP

example : WP (FreeState Nat Unit) Unit (Nat → Prop) EStack⟨⟩ := inferInstance
example : WPMonad (FreeState Nat) (Nat → Prop) EStack⟨⟩ := inferInstance
example : WP (FreeReader Nat Unit) Unit (Nat → Prop) EStack⟨⟩ := inferInstance
example : HasHandler (StateF Nat) (Nat → Prop) EStack⟨⟩ := inferInstance

/-- Increment the natural-number state by 1. -/
def incr : FreeState Nat Unit := do
  let n ← MonadStateOf.get
  MonadStateOf.set (n + 1)

example : wp incr = wp (FreeState.toStateM incr) :=
  StateF.wp_FreeState_eq_wp_toStateM incr

/-- Starting in state `n`, `incr` ends in state `n + 1`. `vcgen` picks up the `@[spec]` lemmas
for `MonadStateOf.get`/`set` on `FreeState` and discharges the resulting arithmetic VC. -/
example (n : Nat) :
    ⦃ fun s => s = n ⦄ (incr : FreeState Nat Unit) ⦃ fun _ s' => s' = n + 1 ⦄ := by
  vcgen [incr]
  subst_vars
  rfl

/-- A counter effect with two operations. -/
inductive CounterF : Type → Type where
  /-- Increment the counter by one. -/
  | tick : CounterF Unit
  /-- Read the counter's value. -/
  | read : CounterF Nat

/-- Counter programs built from `CounterF`. -/
abbrev FreeCounter := FreeM CounterF

namespace CounterF

/-- Effect handler for `CounterF` into `StateM Nat`, used to seed both the executable
semantics and the logical handler. -/
def interp : ∀ ι : Type, CounterF ι → StateM Nat ι
  | _, .tick => modify (· + 1)
  | _, .read => MonadStateOf.get

/-- Logical handler for `CounterF` induced by `interp` and `Std.WP`'s `WP (StateM Nat)`
instance. -/
def handler : LHandler CounterF (Nat → Prop) EStack⟨⟩ :=
  LHandler.ofInterp CounterF.interp

instance : HasHandler CounterF (Nat → Prop) EStack⟨⟩ where
  handler := CounterF.handler

/-- Interpret counter programs as `StateM Nat` programs. -/
abbrev toStateM {α : Type} (comp : FreeCounter α) : StateM Nat α :=
  comp.liftM (fun {ι} => CounterF.interp ι)

/-- Adequacy theorem specialized to `CounterF`. -/
theorem wp_FreeCounter_eq_wp_toStateM {α : Type} (comp : FreeCounter α) :
    wp comp = wp (CounterF.toStateM comp) := by
  funext Q E s
  induction comp using FreeM.induction generalizing s with
  | pure a => rfl
  | lift_bind op k ih => cases op <;> exact ih _ _

end CounterF

/-- Smart constructor: tick the counter as a `FreeCounter` action. -/
abbrev tick : FreeCounter Unit := lift CounterF.tick

/-- Smart constructor: read the counter as a `FreeCounter` action. -/
abbrev readCounter : FreeCounter Nat := lift CounterF.read

/-- Tick three times, then read out the counter. -/
def threeTicks : FreeCounter Nat := do
  tick; tick; tick
  readCounter

/--
Triple about the counter program: starting at `0`, the final value is `3` and the final state
is `3`. Proven by the same bridge-then-`vcgen` pattern as `incr`.
-/
example :
    ⦃ fun s => s = 0 ⦄ threeTicks ⦃ fun v s => v = 3 ∧ s = 3 ⦄ := by
  vcgen [threeTicks, tick, readCounter, CounterF.handler, CounterF.interp]
  subst_vars
  change (3 : Nat) = 3 ∧ (3 : Nat) = 3
  exact ⟨rfl, rfl⟩

/-- A failure effect with one operation `fail` of empty answer type. -/
inductive FailF : Type → Type where
  /-- Abort the computation. -/
  | fail : FailF PEmpty.{1}

/-- Logical handler for `FailF`: `fail` has precondition `False`, so it is only provable in
unreachable branches. -/
noncomputable def FailF.handler {Pred EPred : Type} [Assertion Pred] [Assertion EPred] :
    LHandler FailF Pred EPred where
  trans _ := ⟨fun _ _ => Lean.Order.bot⟩
  monotone _ := fun _ _ _ _ _ _ => PartialOrder.rel_refl

/-- A combined state + failure signature, sequencing `StateF Nat` with `FailF`. -/
abbrev StateFail := fun α => StateF Nat α ⊕ FailF α

/-- Handler for the combined signature: the sum of the component handlers — the paper's
`H₁ ⊕ H₂` composition. -/
noncomputable instance : HasHandler StateFail (Nat → Prop) EStack⟨⟩ where
  handler := StateF.handler.sum FailF.handler

/-- Smart constructor for state-read in the combined signature. -/
abbrev sfGet : FreeM StateFail Nat := lift (Sum.inl StateF.get)

/-- Smart constructor for state-write in the combined signature. -/
abbrev sfSet (n : Nat) : FreeM StateFail PUnit := lift (Sum.inl (StateF.set n))

/-- Smart constructor for failure in the combined signature, eliminated to any return type via
`PEmpty.elim`. -/
abbrev sfFail {α : Type} : FreeM StateFail α :=
  lift (Sum.inr FailF.fail) >>= PEmpty.elim

/-- Hoare spec for the sum-lifted state-read. -/
@[spec]
theorem Spec.sfGet {Q : Nat → Nat → Prop} :
    Triple sfGet (fun s => Q s s) Q () :=
  ⟨fun _ h => h⟩

/-- Hoare spec for the sum-lifted state-write. -/
@[spec]
theorem Spec.sfSet (n : Nat) {Q : PUnit → Nat → Prop} :
    Triple (sfSet n) (fun _ => Q ⟨⟩ n) Q () :=
  ⟨fun _ h => h⟩

/-- Hoare spec for sum-lifted failure: requires `False` to verify. -/
@[spec]
theorem Spec.sfFail {α : Type} {Q : α → Nat → Prop} :
    Triple (sfFail : FreeM StateFail α) (fun _ => False) Q () :=
  ⟨fun _ h => h.elim⟩

/-- A non-branching program in the combined signature: read the state, then write
`state + 1`. Shows that the sum handler composes the StateF and FailF specs cleanly. -/
def getAndBump : FreeM StateFail Unit := do
  let n ← sfGet
  sfSet (n + 1)

/-- `getAndBump` advances the state by 1, proven through the sum handler. -/
example (n : Nat) :
    ⦃ fun s => s = n ⦄ (getAndBump : FreeM StateFail Unit)
      ⦃ fun _ s => s = n + 1 ⦄ := by
  vcgen [getAndBump]
  subst_vars
  rfl

/-- Increment the state if it's strictly below `limit`, otherwise fail. Branches on the state's
value and uses `sfFail` in the else branch. -/
def bumpUnder (limit : Nat) : FreeM StateFail Unit := do
  let n ← sfGet
  if n < limit then sfSet (n + 1) else sfFail

/-- Starting in a state below `limit`, `bumpUnder` increments without failing — the failure
branch is unreachable because the precondition rules it out. -/
example (limit n : Nat) (hlt : n < limit) :
    ⦃ fun s => s = n ⦄ (bumpUnder limit : FreeM StateFail Unit)
      ⦃ fun _ s => s = n + 1 ⦄ := by
  unfold bumpUnder
  vcgen <;> aesop

/-- Demonic non-determinism: a single operation `choice α` that abstractly returns an arbitrary
`a : α`. Verification must consider all possible values of `a`. -/
inductive DemonicF : Type → Type 1 where
  /-- Choose an element of `α`. -/
  | choice (α : Type) : DemonicF α

/-- Relational specification for demonic choice: it is always enabled and every output is
permitted. The generated weakest precondition must therefore establish the continuation
postcondition for every possible output. -/
def DemonicF.spec : OperationSpec DemonicF where
  pre _ := True
  post _ _ := True

/-- Logical handler for demonic choice, generated from its relational operation specification. -/
def DemonicF.handler : LHandler DemonicF Prop EStack⟨⟩ :=
  DemonicF.spec.toHandler

instance : HasHandler DemonicF Prop EStack⟨⟩ where
  handler := DemonicF.handler

/-- Smart constructor for demonic choice over `α`. -/
abbrev demonic (α : Type) : FreeM DemonicF α := lift (DemonicF.choice α)

/-- Triple for `demonic α`: the precondition must imply the postcondition for *every* `a : α`. -/
@[spec]
theorem Spec.demonic {α : Type} {Q : α → Prop} :
    Triple (demonic α) (∀ a : α, Q a) Q () :=
  ⟨fun h => ⟨True.intro, fun a _ => h a⟩⟩

/-- A demonic Bool: the precondition must hold for both `true` and `false`. -/
example {Q : Bool → Prop} :
    Triple (demonic Bool) (Q true ∧ Q false) Q () :=
  ⟨fun ⟨ht, hf⟩ => ⟨True.intro, fun
    | true, _ => ht
    | false, _ => hf⟩⟩

/-! ### Arbitrarily specified operations -/

/-- An abstract Boolean operation used to reproduce the `pick` example from
*Dijkstra Monads for All*. -/
inductive PickF : Type → Type where
  /-- Pick a Boolean. -/
  | pick : PickF Bool

/-- `pick` is always enabled and is specified to return only `true`. -/
def PickF.spec : OperationSpec PickF where
  pre _ := True
  post
    | .pick, b => b = true

/-- Logical handler generated independently of any executable interpretation of `pick`. -/
def PickF.handler : LHandler PickF Prop EStack⟨⟩ :=
  PickF.spec.toHandler

instance : HasHandler PickF Prop EStack⟨⟩ where
  handler := PickF.handler

/-- Smart constructor for the abstract `pick` operation. -/
abbrev pick : FreeM PickF Bool := lift PickF.pick

/-- The generated operation WP simplifies to the `true` case of the continuation postcondition. -/
example (Q : Bool → Prop) :
    (wpH PickF.handler pick).apply Q () = Q true := by
  rw [wpH_lift]
  simp [PickF.handler, PickF.spec]

/-- Consequently, `pick` has precisely the paper's Hoare specification. -/
example {Q : Bool → Prop} :
    Triple pick (Q true) Q () :=
  ⟨fun h => ⟨True.intro, fun _ hEq => hEq ▸ h⟩⟩

/-! ### Query-model programs

The repository's query model defines `Prog Q α := FreeM Q α`, and `Algolean.QueryModel` wires every
query model into this WP framework: `Model.handler` reads a logical handler off a model's
`evalQuery` at `Prop` assertions, a `HasModel` instance registers a query type's default model,
and the generic `Spec.query` discharges single queries under `vcgen`. So Hoare triples about the
*result value* a query program computes are available with no per-example setup.

We illustrate with `ReadOnlyVec`, whose `HasModel (ReadOnlyVec α) ℕ` instance (via
`ReadOnlyVec.natCost`, in `Algolean.Models.ReadOnlyVec`) makes the global
`WP (Prog (ReadOnlyVec α) Unit) Unit Prop EStack⟨⟩` instance fire automatically. -/

open Algolean Algolean.Algorithms

/-- The WP framework is available on query programs with no local setup — the handler instance is
generated from the registered model. -/
example {α : Type} : WP (Prog (ReadOnlyVec α) Unit) Unit Prop EStack⟨⟩ := inferInstance

/-- Adequacy, specialized to `ReadOnlyVec` from the generic `Model.wp_eq_wp_interp`: the WP of a
program agrees with the WP of its `Id`-interpretation under `natCost`, i.e. with what the program
actually `eval`uates to. -/
example {α β : Type} (P : Prog (ReadOnlyVec α) β) :
    WP.wpTrans P = WP.wpTrans (P.liftM (fun {_} q => (ReadOnlyVec.natCost.evalQuery q : Id _))) :=
  ReadOnlyVec.natCost.wp_eq_wp_interp P

/-- Read indices `i` then `j` of a vector and return the pair of values. Queries lift into `Prog`
automatically through the `CoeOut` coercion, so no explicit `lift` is needed. -/
def readTwo {α : Type} {n : Nat} (a : Vector α n) (i j : Fin n) :
    Prog (ReadOnlyVec α) (α × α) := do
  let x ← ReadOnlyVec.read a i
  let y ← ReadOnlyVec.read a j
  pure (x, y)

/-- Functional correctness of `readTwo`: it returns exactly `(a[i], a[j])`. The two `read`
specs compose through the `bind` rule, and `vcgen` discharges the program. -/
example {α : Type} {n : Nat} (a : Vector α n) (i j : Fin n) :
    ⦃ True ⦄ (readTwo a i j) ⦃ fun r => r = (a[i], a[j]) ⦄ := by
  vcgen [readTwo]
  rfl

/-- A read program whose result depends on the data: read index `i`, and if the value equals
`x`, the answer is `true`. The triple shows the verifier sees the concrete element `a[i]`. -/
example {n : Nat} (a : Vector Nat n) (i : Fin n) (x : Nat) :
    ⦃ True ⦄
      (do let v ← ReadOnlyVec.read a i; pure (v == x) : Prog (ReadOnlyVec Nat) Bool)
    ⦃ fun r => r = (a[i] == x) ⦄ := by
  vcgen
  rfl

end AlgoleanTests.FreeMonadWP
