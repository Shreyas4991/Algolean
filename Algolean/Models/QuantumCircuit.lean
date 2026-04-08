/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.QuantumOracle

@[expose] public section

/-!
# Quantum Circuits

Tree-structured quantum circuits with sequential and parallel composition,
integrated with the `Prog` query framework. Each circuit operation is an
atomic query in the `Prog` monad; parallel composition computes depth via
`max` inside the query type, following the same pattern as `FanInTwoCircuit`.

## Main definitions

- `QuantumCircuit n`: query type with gates, sequential and parallel composition
- `CircuitCost`: cost structure tracking depth, gate count, and oracle queries
- `quantumCircuitModel`: model for `Prog (QuantumCircuit n)` with `CircuitCost`
- `CircuitFamily`, `BQPpoly`, `EQPpoly`, `QNCpoly`: nonuniform complexity classes

## Design

`QuantumCircuit` is a self-recursive query type (like `FanInTwoCircuit`).
Each constructor is an atomic query in `Prog`; sub-circuits inside `par`
carry their own cost computed via `max` for depth. `Prog.time` sums
per-query costs, giving correct total depth: sequential sums, parallel maxes.

`seq` exists at the query level so that multi-gate sub-circuits can appear
inside `par` branches. Top-level sequencing uses `Prog.bind` (do-notation).
-/

namespace Algolean

namespace Algorithms

open Complex Cslib Polynomial

/-- Quantum circuit query type. Leaves are single gates (via `QuantumQuery`);
`seq` composes circuits sequentially on the same register; `par` is the tensor
product of circuits on disjoint registers. Each constructor is an atomic query
in `Prog`, so `Prog.time` sums per-query costs. Depth uses `max` at `par`
nodes (like `FanInTwoCircuit`). -/
inductive QuantumCircuit : ℕ → Type → Type where
  /-- A single quantum gate. -/
  | gate {n : ℕ} (q : QuantumQuery n (QState n → QState n)) :
      QuantumCircuit n (QState n → QState n)
  /-- Sequential composition on the same register. -/
  | seq {n : ℕ} (c₁ c₂ : QuantumCircuit n (QState n → QState n)) :
      QuantumCircuit n (QState n → QState n)
  /-- Parallel composition via tensor product on disjoint registers. -/
  | par {m k : ℕ} (c₁ : QuantumCircuit m (QState m → QState m))
      (c₂ : QuantumCircuit k (QState k → QState k)) :
      QuantumCircuit (m + k) (QState (m + k) → QState (m + k))

namespace QuantumCircuit

/-- Evaluate a circuit as a state transformation.
The oracle is a family indexed by qubit count; `extendOracle` lifts a
single oracle to such a family (identity at other sizes).
For `par`, evaluation is the tensor product of the subcircuit evaluations. -/
noncomputable def eval (oracle : (m : ℕ) → QState m → QState m) :
    QuantumCircuit n ι → ι
  | .gate q => Algorithms.evalGate (oracle _) q
  | .seq c₁ c₂ => fun s => eval oracle c₂ (eval oracle c₁ s)
  | .par c₁ c₂ => tensorGate (eval oracle c₁) (eval oracle c₂)

/-- Circuit depth. Sequential adds; parallel takes max. -/
@[simp]
def depthOf : QuantumCircuit n ι → ℕ
  | .gate _ => 1
  | .seq c₁ c₂ => depthOf c₁ + depthOf c₂
  | .par c₁ c₂ => max (depthOf c₁) (depthOf c₂)

/-- Total gate count. -/
@[simp]
def size : QuantumCircuit n ι → ℕ
  | .gate _ => 1
  | .seq c₁ c₂ => size c₁ + size c₂
  | .par c₁ c₂ => size c₁ + size c₂

/-- Number of oracle queries. -/
@[simp]
def oracleCount : QuantumCircuit n ι → ℕ
  | .gate .oracle => 1
  | .gate _ => 0
  | .seq c₁ c₂ => oracleCount c₁ + oracleCount c₂
  | .par c₁ c₂ => oracleCount c₁ + oracleCount c₂

/-- Apply a single quantum gate in a circuit program. -/
def apply (q : QuantumQuery n (QState n → QState n)) (s : QState n) :
    Prog (QuantumCircuit n) (QState n) :=
  FreeM.liftBind (.gate q) fun f => pure (f s)

/-- Apply a parallel composition in a circuit program. -/
def applyPar (c₁ : QuantumCircuit m (QState m → QState m))
    (c₂ : QuantumCircuit k (QState k → QState k))
    (s : QState (m + k)) :
    Prog (QuantumCircuit (m + k)) (QState (m + k)) :=
  FreeM.liftBind (.par c₁ c₂) fun f => pure (f s)

end QuantumCircuit

/-! ### Circuit cost model -/

/-- Cost structure for quantum circuits, tracking circuit depth, gate count,
and oracle queries separately. -/
@[ext]
structure CircuitCost where
  /-- Circuit depth (longest path from input to output). -/
  depth : ℕ
  /-- Total number of gates. -/
  gates : ℕ
  /-- Number of oracle queries. -/
  oracleQueries : ℕ
  deriving DecidableEq

namespace CircuitCost

/-- Equivalence between `CircuitCost` and a product type. -/
def equivProd : CircuitCost ≃ ℕ × ℕ × ℕ where
  toFun c := (c.depth, c.gates, c.oracleQueries)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by obtain ⟨a, b, c⟩ := p; rfl

instance : Zero CircuitCost := ⟨⟨0, 0, 0⟩⟩

instance : Add CircuitCost where
  add c₁ c₂ := ⟨c₁.depth + c₂.depth, c₁.gates + c₂.gates,
    c₁.oracleQueries + c₂.oracleQueries⟩

instance : SMul ℕ CircuitCost where
  smul n c := ⟨n * c.depth, n * c.gates, n * c.oracleQueries⟩

instance : AddCommMonoid CircuitCost :=
  equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance : LE CircuitCost where
  le c₁ c₂ := c₁.depth ≤ c₂.depth ∧ c₁.gates ≤ c₂.gates ∧
    c₁.oracleQueries ≤ c₂.oracleQueries

instance : Preorder CircuitCost where
  le_refl a := ⟨le_refl _, le_refl _, le_refl _⟩
  le_trans a b c h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₁.2.1 h₂.2.1,
    le_trans h₁.2.2 h₂.2.2⟩

end CircuitCost

/-! ### Model -/

/-- Quantum circuit cost model. Evaluation delegates to `QuantumCircuit.eval`;
cost uses the structural `depthOf`, `size`, and `oracleCount`. -/
noncomputable def quantumCircuitModel (n : ℕ)
    (oracle : (m : ℕ) → QState m → QState m) :
    Model (QuantumCircuit n) CircuitCost where
  evalQuery q := q.eval oracle
  cost q := ⟨q.depthOf, q.size, q.oracleCount⟩

/-! ### Circuit families -/

/-- A quantum circuit family: for each input size `n`, a `Prog` that
transforms an initial quantum state through a sequence of circuit
operations (gates and parallel blocks). -/
structure CircuitFamily where
  /-- The circuit for input size `n`, as a state-transforming program. -/
  circuit : (n : ℕ) → QState n → Prog (QuantumCircuit n) (QState n)

/-- The output state of a circuit family on input size `n` with
oracle function `f`. -/
noncomputable def CircuitFamily.output (fam : CircuitFamily)
    (n : ℕ) (f : (Fin n → Fin 2) → Bool) : QState n :=
  (fam.circuit n (QState.initial n)).eval
    (quantumCircuitModel n (extendOracle (gateOracle f)))

/-- A language over `n`-qubit inputs. -/
abbrev BoolLanguage := (n : ℕ) → ((Fin n → Fin 2) → Bool) → Prop

/-- A circuit family decides a language with bounded error. -/
def CircuitFamily.DecidesBounded (fam : CircuitFamily)
    (L : BoolLanguage) : Prop :=
  ∀ n (f : (Fin n → Fin 2) → Bool)
    (hn : (fam.output n f).IsNormalized),
    (L n f → measureDistribution (fam.output n f) hn
      0 ≥ ENNReal.ofReal (2 / 3)) ∧
    (¬L n f → measureDistribution (fam.output n f) hn
      0 ≤ ENNReal.ofReal (1 / 3))

/-- A circuit family decides a language with zero error. -/
def CircuitFamily.DecidesExact (fam : CircuitFamily)
    (L : BoolLanguage) : Prop :=
  ∀ n (f : (Fin n → Fin 2) → Bool)
    (hn : (fam.output n f).IsNormalized),
    (L n f → measureDistribution (fam.output n f) hn
      0 = 1) ∧
    (¬L n f → measureDistribution (fam.output n f) hn
      0 = 0)

/-! ### Complexity classes -/

open Polynomial

/-- **BQP/poly**: polynomial-size circuit family with bounded error. -/
def BQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    ∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n (QState.initial n)).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates ≤ p.eval n

/-- **EQP/poly**: polynomial-size circuit family with zero error. -/
def EQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesExact L ∧
    ∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n (QState.initial n)).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates ≤ p.eval n

/-- **QNC^k/poly**: polynomial size, O(log^k n) depth, bounded error. -/
def QNCpoly (L : BoolLanguage) (k : ℕ) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    (∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n (QState.initial n)).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates
          ≤ p.eval n) ∧
    (∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n (QState.initial n)).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).depth
          ≤ (Nat.log 2 n) ^ k)

/-! ### Containments -/

/-- EQP/poly ⊆ BQP/poly -/
theorem EQPpoly.toBQPpoly {L : BoolLanguage} (h : EQPpoly L) :
    BQPpoly L := by
  obtain ⟨fam, p, hExact, hSize⟩ := h
  exact ⟨fam, p, fun n f hn => ⟨
    fun hL => by rw [(hExact n f hn).1 hL]; norm_num,
    fun hL => by rw [(hExact n f hn).2 hL]; norm_num⟩, hSize⟩

/-- QNC^k/poly ⊆ BQP/poly -/
theorem QNCpoly.toBQPpoly {L : BoolLanguage} {k : ℕ}
    (h : QNCpoly L k) : BQPpoly L := by
  obtain ⟨fam, p, hDecides, hSize, _⟩ := h
  exact ⟨fam, p, hDecides, hSize⟩

end Algorithms

end Algolean
