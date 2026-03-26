/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Basic
public import Cslib.Computability.Machines.SingleTapeTuring.Basic

@[expose] public section

/-!
# Query Type for Single Tape Turing Machines

We define a query type for single tape turing machines to allow
users to write such turing machines using lean's monadic syntax,
and integrate with the `Prog` framework.

--
## Definitions

- `Dir` : A type for directions in which a TM can move.
-/

namespace Algolean

namespace Algorithms

open Cslib Prog Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] [DecidableEq Symbol]

/--
The directions in which one can take move on the Turing Machine's tape.
-/
inductive Dir where
  | Left
  | Right
  | Stop

/--
A query type of possible operating steps in a Turing machine.
-/
inductive TMQuery : (tm : SingleTapeTM Symbol) → Type → Type where
  /-- Read a symbol under the TM head on the tape -/
  | readTape {tm} (inpCfg : tm.Cfg) : TMQuery tm (Option Symbol)
  /-- Read the state of the TM -/
  | readState {tm} (inpCfg : tm.Cfg) : TMQuery tm (Option tm.State)
  /-- Write a symbol under the TM head on the tape -/
  | write {tm} (inpCfg : tm.Cfg) (s : Option Symbol) : TMQuery tm tm.Cfg
  /-- Update the TM's state -/
  | update {tm} (inpCfg : tm.Cfg) (st : tm.State): TMQuery tm tm.Cfg
  /-- Move the TM one step in the specified direction or stay in place -/
  | move {tm} (inpCfg : tm.Cfg) (dir : Dir) : TMQuery tm tm.Cfg

/--
The Turing machine cost structure.
-/
@[ext, grind]
structure TMCost where
  /-- `steps` counts the number of moves in the TM -/
  steps : ℕ
  /--
  `writeCells` is the number of cells that were previously unwritten. Thus input cells are excluded.
  This unfortunately also includes output cells, an issue we hope to address in multi tape TMs
  -/
  writeCells : ℕ


/-- Equivalence between `TMCost` and a product type. -/
def TMCost.equivProd : TMCost ≃ (ℕ × ℕ) where
  toFun tmOps := (tmOps.steps, tmOps.writeCells)
  invFun pair := ⟨pair.1, pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace TMCost

@[simps, grind]
instance : Zero TMCost := ⟨0, 0⟩

@[simps]
instance : LE TMCost where
  le soc₁ soc₂ := soc₁.steps ≤ soc₂.steps ∧ soc₁.writeCells ≤ soc₂.writeCells

instance : LT TMCost where
  lt soc₁ soc₂ := soc₁ ≤ soc₂ ∧ ¬soc₂ ≤ soc₁

@[grind]
instance : PartialOrder TMCost :=
  fast_instance% TMCost.equivProd.injective.partialOrder _ .rfl .rfl

@[simps]
instance : Add TMCost where
  add soc₁ soc₂ := ⟨soc₁.steps + soc₂.steps, soc₁.writeCells + soc₂.writeCells⟩

@[simps]
instance : SMul ℕ TMCost where
  smul n soc := ⟨n • soc.steps, n • soc.writeCells⟩

instance : AddCommMonoid TMCost :=
  fast_instance%
    TMCost.equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance : CovariantClass TMCost TMCost (· + ·) (· ≤ ·) where
  elim a _ _ h := ⟨Nat.add_le_add_left h.1 a.steps, Nat.add_le_add_left h.2 a.writeCells⟩

end TMCost

/--
A model of `TMQuery` that uses `TMCost` as the cost type for operations.
Space complexity in this single tape TM is counted as the number of unread cells
written to during the TM's operation.
-/
@[simps, grind]
def TMModel (tm : SingleTapeTM Symbol) :
    Model (TMQuery tm) TMCost where
  evalQuery
    | .readTape cfg => cfg.BiTape.head
    | .readState cfg => cfg.state
    | .write cfg s => {BiTape := cfg.BiTape.write s, state := cfg.state}
    | .move cfg dir =>
        match dir with
        | .Left => {BiTape := cfg.BiTape.move_left, state := cfg.state}
        | .Right => {BiTape := cfg.BiTape.move_left, state := cfg.state}
        | .Stop => cfg
    | .update cfg st => {BiTape := cfg.BiTape, state := st}
  cost
    | .readTape _ => ⟨0, 0⟩
    | .readState _ => ⟨0, 0⟩
    | .write cfg _ =>
        match cfg.BiTape.head with
        | .some _ => ⟨0, 0⟩
        | .none => ⟨0, 1⟩
    | .move _ _ => ⟨1, 0⟩
    | .update _ _ => ⟨0, 0⟩

/-! ## Complexity Classes -/

open SingleTapeTM Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- A language over alphabet `Symbol`. -/
abbrev Language (Symbol : Type) := List Symbol → Prop

/-- The decision problem for language `L` on input `x`, viewed as a
`QueryProblem` over `TMQuery tm`. The spec ignores the model
(there is only one meaningful model per TM). -/
def TMDecisionProblem (L : Language Symbol) (x : List Symbol)
    (tm : SingleTapeTM Symbol) : QueryProblem (TMQuery tm) TMCost Bool where
  spec _ b := (b = true ↔ L x)

/-- A language is in P if there exists a TM, a uniform family of
programs, and a polynomial such that each program correctly decides
`L` on input `x` within `p(|x|)` steps under `TMModel tm`. -/
def P (L : Language Symbol) : Prop :=
  ∃ (tm : SingleTapeTM Symbol)
    (prog : List Symbol → Prog (TMQuery tm) Bool)
    (p : Polynomial ℕ),
    ∀ x, ((prog x).eval (TMModel tm) = true ↔ L x) ∧
      ((prog x).time (TMModel tm)).steps ≤ p.eval x.length

/-- A language is in NP if there exists a TM, a uniform verifier
taking input and certificate separately, and polynomials `p` (time
bound) and `q` (certificate bound) such that: the verifier runs in
poly time on all valid-length certificates, and `L x` iff there
exists a short certificate that the verifier accepts. -/
def NP (L : Language Symbol) : Prop :=
  ∃ (tm : SingleTapeTM Symbol)
    (V : List Symbol → List Symbol → Prog (TMQuery tm) Bool)
    (p q : Polynomial ℕ),
    (∀ x c, c.length ≤ q.eval x.length →
      ((V x c).time (TMModel tm)).steps ≤ p.eval x.length) ∧
    ∀ x, L x ↔ ∃ c : List Symbol, c.length ≤ q.eval x.length ∧
      (V x c).eval (TMModel tm) = true

/-- P is closed under composition via bind. If `P₁` runs within
`p₁(|x|)` steps and `P₂` runs within `p₂(|x|)` steps on the
result of `P₁`, then `P₁ >>= P₂` runs within
`(p₁ + p₂)(|x|)` steps. -/
theorem P.bind
    {tm : SingleTapeTM Symbol}
    {P₁ : List Symbol → Prog (TMQuery tm) α}
    {P₂ : α → List Symbol → Prog (TMQuery tm) β}
    {spec₁ : List Symbol → α → Prop}
    {spec₂ : α → List Symbol → β → Prop}
    {p₁ p₂ : Polynomial ℕ}
    (h₁ : ∀ x, spec₁ x ((P₁ x).eval (TMModel tm)) ∧
      ((P₁ x).time (TMModel tm)).steps ≤ p₁.eval x.length)
    (h₂ : ∀ x a, spec₁ x a →
      spec₂ a x ((P₂ a x).eval (TMModel tm)) ∧
        ((P₂ a x).time (TMModel tm)).steps ≤ p₂.eval x.length) :
    ∀ x, spec₂ ((P₁ x).eval (TMModel tm)) x
        (Prog.eval ((P₁ x).bind (P₂ · x)) (TMModel tm)) ∧
      (Prog.time ((P₁ x).bind (P₂ · x)) (TMModel tm)).steps
        ≤ (p₁ + p₂).eval x.length := by
  intro x
  obtain ⟨hspec₁, htime₁⟩ := h₁ x
  obtain ⟨hspec₂, htime₂⟩ := h₂ x _ hspec₁
  simp only [Prog.eval_bind, Prog.time_bind, eval_add]
  exact ⟨hspec₂, Nat.add_le_add htime₁ htime₂⟩

/-- P ⊆ NP: every language in P is in NP (with trivial certificates).
The verifier ignores the certificate and runs the decider. -/
theorem NP.ofP {L : Language Symbol} (hP : P L) : NP L := by
  obtain ⟨tm, P, p, hP⟩ := hP
  refine ⟨tm, fun x _ => P x, p, 0, ?_, ?_⟩
  · intro x _ _
    exact (hP x).2
  · intro x
    constructor
    · intro hLx
      exact ⟨[], by simp, (hP x).1.mpr hLx⟩
    · intro ⟨_, _, hVc⟩
      exact (hP x).1.mp hVc

end Algorithms

end Algolean
