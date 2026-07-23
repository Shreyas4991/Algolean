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
a `Triple` on a `FreeState` program discharged by `mvcgen`, a custom `CounterF` effect with
its own logical handler, sum/failure/demonic effects, arbitrary relational operation specifications,
and — connecting the WP framework to this repository's query model — Hoare triples about
query-model programs `Prog Q α` against a handler derived from a `Model Q Cost` (illustrated on
`ReadOnlyVec`).
-/

@[expose] public section

set_option mvcgen.warning false

namespace AlgoleanTests.FreeMonadWP

open Cslib Cslib.FreeM Std.Do

example : WP (FreeState Nat) (.arg Nat .pure) := inferInstance
example : WPMonad (FreeState Nat) (.arg Nat .pure) := inferInstance
example : WP (FreeReader Nat) (.arg Nat .pure) := inferInstance
example : HasHandler (StateF Nat) (.arg Nat .pure) := inferInstance

/-- Increment the natural-number state by 1. -/
def incr : FreeState Nat Unit := do
  let n ← MonadStateOf.get
  MonadStateOf.set (n + 1)

example : wp incr = wp (FreeState.toStateM incr) :=
  StateF.wp_FreeState_eq_wp_toStateM incr

/-- Starting in state `n`, `incr` ends in state `n + 1`. `mvcgen` picks up the `@[spec]` lemmas
for `MonadStateOf.get`/`set` on `FreeState` and discharges the resulting arithmetic VC. -/
example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ (incr : FreeState Nat Unit) ⦃⇓ _ s' => ⌜s' = n + 1⌝⦄ := by
  mvcgen
  intro s heq
  subst heq
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

/-- Logical handler for `CounterF` induced by `interp` and `Std.Do`'s `WP (StateM Nat)`
instance. -/
def handler : LHandler CounterF (.arg Nat .pure) :=
  LHandler.ofInterp CounterF.interp

instance : HasHandler CounterF (.arg Nat .pure) where
  handler := CounterF.handler

/-- Interpret counter programs as `StateM Nat` programs. -/
abbrev toStateM {α : Type} (comp : FreeCounter α) : StateM Nat α :=
  comp.liftM (fun {ι} => CounterF.interp ι)

/-- Adequacy theorem specialized to `CounterF`. -/
theorem wp_FreeCounter_eq_wp_toStateM {α : Type} (comp : FreeCounter α) :
    wp comp = wp (CounterF.toStateM comp) :=
  wpH_ofInterp_eq_wp_liftM (m := StateM Nat) CounterF.interp comp

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
is `3`. Proven by the same bridge-then-`mvcgen` pattern as `incr`.
-/
example :
    ⦃fun s => ⌜s = 0⌝⦄ threeTicks ⦃⇓ v s => ⌜v = 3 ∧ s = 3⌝⦄ := by
  mvcgen
  intro s seq0
  subst seq0
  exact ⟨rfl, rfl⟩

/-- A failure effect with one operation `fail` of empty answer type. -/
inductive FailF : Type → Type where
  /-- Abort the computation. -/
  | fail : FailF PEmpty.{1}

/-- Logical handler for `FailF`: `fail` has precondition `⌜False⌝`, so it is only provable in
unreachable branches. -/
def FailF.handler {ps : PostShape} : LHandler FailF ps :=
  fun op => match op with
    | .fail => PredTrans.const spred(⌜False⌝)

/-- A combined state + failure signature, sequencing `StateF Nat` with `FailF`. -/
abbrev StateFail := fun α => StateF Nat α ⊕ FailF α

/-- Handler for the combined signature: the sum of the component handlers — the paper's
`H₁ ⊕ H₂` composition. -/
instance : HasHandler StateFail (.arg Nat .pure) where
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
theorem Spec.sfGet {Q : PostCond Nat (.arg Nat .pure)} :
    Triple sfGet (spred(fun s => Q.1 s s)) Q := by
  mvcgen

/-- Hoare spec for the sum-lifted state-write. -/
@[spec]
theorem Spec.sfSet (n : Nat) {Q : PostCond PUnit (.arg Nat .pure)} :
    Triple (sfSet n) (spred(fun _ => Q.1 ⟨⟩ n)) Q := by
  mvcgen

/-- Hoare spec for sum-lifted failure: requires `False` to verify. -/
@[spec]
theorem Spec.sfFail {α : Type} {Q : PostCond α (.arg Nat .pure)} :
    Triple (sfFail : FreeM StateFail α) (spred(⌜False⌝)) Q := by
  mvcgen

/-- A non-branching program in the combined signature: read the state, then write
`state + 1`. Shows that the sum handler composes the StateF and FailF specs cleanly. -/
def getAndBump : FreeM StateFail Unit := do
  let n ← sfGet
  sfSet (n + 1)

/-- `getAndBump` advances the state by 1, proven through the sum handler. -/
example (n : Nat) :
    ⦃fun s => ⌜s = n⌝⦄ (getAndBump : FreeM StateFail Unit)
      ⦃⇓ _ s => ⌜s = n + 1⌝⦄ := by
  mvcgen
  intro s a
  subst a
  rfl

/-- Increment the state if it's strictly below `limit`, otherwise fail. Branches on the state's
value and uses `sfFail` in the else branch. -/
def bumpUnder (limit : Nat) : FreeM StateFail Unit := do
  let n ← sfGet
  if n < limit then sfSet (n + 1) else sfFail

/-- Starting in a state below `limit`, `bumpUnder` increments without failing — the failure
branch is unreachable because the precondition rules it out. -/
example (limit n : Nat) (hlt : n < limit) :
    ⦃fun s => ⌜s = n⌝⦄ (bumpUnder limit : FreeM StateFail Unit)
      ⦃⇓ _ s => ⌜s = n + 1⌝⦄ := by
  unfold bumpUnder
  mvcgen <;> aesop

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
def DemonicF.handler : LHandler DemonicF .pure :=
  DemonicF.spec.toHandler

instance : HasHandler DemonicF .pure where
  handler := DemonicF.handler

/-- Smart constructor for demonic choice over `α`. -/
abbrev demonic (α : Type) : FreeM DemonicF α := lift (DemonicF.choice α)

/-- Triple for `demonic α`: the precondition must imply the postcondition for *every* `a : α`. -/
@[spec]
theorem Spec.demonic {α : Type} {Q : PostCond α .pure} :
    Triple (demonic α) (SPred.forall (fun a : α => Q.1 a)) Q :=
  fun h => ⟨True.intro, fun a _ => h a⟩

/-- A demonic Bool: the precondition must hold for both `true` and `false`. -/
example {Q : PostCond Bool .pure} :
    Triple (demonic Bool) (SPred.and (Q.1 true) (Q.1 false)) Q :=
  fun ⟨ht, hf⟩ => ⟨True.intro, fun
    | true, _ => ht
    | false, _ => hf⟩

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
def PickF.handler : LHandler PickF .pure :=
  PickF.spec.toHandler

instance : HasHandler PickF .pure where
  handler := PickF.handler

/-- Smart constructor for the abstract `pick` operation. -/
abbrev pick : FreeM PickF Bool := lift PickF.pick

/-- The generated operation WP simplifies to the `true` case of the continuation postcondition. -/
example (Q : PostCond Bool .pure) :
    (wpH PickF.handler pick).apply Q = Q.1 true := by
  rw [wpH_lift]
  apply SPred.ext_nil
  simp [PickF.handler, PickF.spec]

/-- Consequently, `pick` has precisely the paper's Hoare specification. -/
example {Q : PostCond Bool .pure} :
    Triple pick (Q.1 true) Q :=
  fun h => ⟨True.intro, fun _ hEq => hEq ▸ h⟩

/-! ### Query-model programs

The repository's query model defines `Prog Q α := FreeM Q α`, and `Algolean.QueryModel` wires every
query model into this WP framework: `Model.handler` reads a logical handler off a model's
`evalQuery` at the pure post-shape, a `HasModel` instance registers a query type's default model,
and the generic `Spec.query` discharges single queries under `mvcgen`. So Hoare triples about the
*result value* a query program computes are available with no per-example setup.

We illustrate with `ReadOnlyVec`, whose `HasModel (ReadOnlyVec α) ℕ` instance (via
`ReadOnlyVec.natCost`, in `Algolean.Models.ReadOnlyVec`) makes the global
`WP (Prog (ReadOnlyVec α)) .pure` instance fire automatically. -/

open Algolean Algolean.Algorithms

/-- The WP framework is available on query programs with no local setup — the handler instance is
generated from the registered model. -/
example {α : Type} : WP (Prog (ReadOnlyVec α)) .pure := inferInstance

/-- Adequacy, specialized to `ReadOnlyVec` from the generic `Model.wp_eq_wp_interp`: the WP of a
program agrees with the WP of its `Id`-interpretation under `natCost`, i.e. with what the program
actually `eval`uates to. -/
example {α β : Type} (P : Prog (ReadOnlyVec α) β) :
    wp P = wp (P.liftM (fun {_} q => (ReadOnlyVec.natCost.evalQuery q : Id _))) :=
  ReadOnlyVec.natCost.wp_eq_wp_interp P

/-- Read indices `i` then `j` of a vector and return the pair of values. Queries lift into `Prog`
automatically through the `CoeOut` coercion, so no explicit `lift` is needed. -/
def readTwo {α : Type} {n : Nat} (a : Vector α n) (i j : Fin n) :
    Prog (ReadOnlyVec α) (α × α) := do
  let x ← ReadOnlyVec.read a i
  let y ← ReadOnlyVec.read a j
  pure (x, y)

/-- Functional correctness of `readTwo`: it returns exactly `(a[i], a[j])`. The two `read`
specs compose through the `bind` rule, and `mvcgen` discharges the program. -/
example {α : Type} {n : Nat} (a : Vector α n) (i j : Fin n) :
    ⦃⌜True⌝⦄ (readTwo a i j) ⦃⇓ r => ⌜r = (a[i], a[j])⌝⦄ := by
  mvcgen

/-- A read program whose result depends on the data: read index `i`, and if the value equals
`x`, the answer is `true`. The triple shows the verifier sees the concrete element `a[i]`. -/
example {n : Nat} (a : Vector Nat n) (i : Fin n) (x : Nat) :
    ⦃⌜True⌝⦄
      (do let v ← ReadOnlyVec.read a i; pure (v == x) : Prog (ReadOnlyVec Nat) Bool)
    ⦃⇓ r => ⌜r = (a[i] == x)⌝⦄ := by
  mvcgen

end AlgoleanTests.FreeMonadWP
