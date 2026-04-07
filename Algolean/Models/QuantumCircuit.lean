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
following the same pattern as `Circuit α` for classical circuits. Each
constructor pins the return type to `QState n → QState n`, so the `Model`
interface works directly.

## Main definitions

- `QuantumCircuit n`: tree of quantum gates with `seq` and `par`
- `QuantumCircuit.circEval`: evaluate as a state transformation
- `QuantumCircuit.depthOf`: circuit depth (`+` for `seq`, `max` for `par`)
- `QuantumCircuit.size`: total gate count
- `quantumCircuitModel`: `Model (QuantumCircuit n) CircuitCost`
- `BQPpoly`, `EQPpoly`, `QNCpoly`: nonuniform quantum complexity classes
-/

namespace Algolean

namespace Algorithms

open Complex Prog Cslib Polynomial

/-- Quantum circuit over `n` qubits. Leaves are single gates (via
`QuantumQuery`); internal nodes are sequential or parallel composition.
Every constructor pins `ι = QState n → QState n`. -/
inductive QuantumCircuit (n : ℕ) : Type → Type where
  /-- A single gate. -/
  | gate (q : QuantumQuery n (QState n → QState n)) :
      QuantumCircuit n (QState n → QState n)
  /-- Sequential composition: apply `c₁` then `c₂`. -/
  | seq (c₁ c₂ : QuantumCircuit n (QState n → QState n)) :
      QuantumCircuit n (QState n → QState n)
  /-- Parallel composition: `c₁` and `c₂` act on disjoint qubits.
  Same evaluation as `seq` (function composition), but depth uses `max`. -/
  | par (c₁ c₂ : QuantumCircuit n (QState n → QState n)) :
      QuantumCircuit n (QState n → QState n)

namespace QuantumCircuit

/-- Evaluate a circuit as a state transformation given an oracle unitary.
For `seq c₁ c₂`, the output state of `c₁` is fed as input to `c₂`.
For `par c₁ c₂`, both act on disjoint qubits, so they compose
(and commute); depth uses `max` rather than `+`. -/
noncomputable def circEval (oracle : QState n → QState n) :
    QuantumCircuit n (QState n → QState n) → QState n → QState n
  | .gate q => Algorithms.evalGate oracle q
  | .seq c₁ c₂ => fun s => circEval oracle c₂ (circEval oracle c₁ s)
  | .par c₁ c₂ => circEval oracle c₂ ∘ circEval oracle c₁

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

end QuantumCircuit

/-! ### Circuit cost model -/

/-- Cost structure for quantum circuits, tracking gate count, circuit depth,
and oracle queries separately. -/
@[ext]
structure CircuitCost where
  /-- Total number of gates (excluding oracle). -/
  gates : ℕ
  /-- Circuit depth (longest path from input to output). -/
  depth : ℕ
  /-- Number of oracle queries. -/
  oracleQueries : ℕ
  deriving DecidableEq

namespace CircuitCost

/-- Equivalence between `CircuitCost` and a product type. -/
def equivProd : CircuitCost ≃ ℕ × ℕ × ℕ where
  toFun c := (c.gates, c.depth, c.oracleQueries)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by obtain ⟨a, b, c⟩ := p; rfl

instance : Zero CircuitCost := ⟨0, 0, 0⟩

instance : Add CircuitCost where
  add c₁ c₂ := ⟨c₁.gates + c₂.gates, c₁.depth + c₂.depth,
    c₁.oracleQueries + c₂.oracleQueries⟩

instance : SMul ℕ CircuitCost where
  smul n c := ⟨n * c.gates, n * c.depth, n * c.oracleQueries⟩

instance : AddCommMonoid CircuitCost :=
  equivProd.injective.addCommMonoid _ rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance : LE CircuitCost where
  le c₁ c₂ := c₁.gates ≤ c₂.gates ∧ c₁.depth ≤ c₂.depth ∧
    c₁.oracleQueries ≤ c₂.oracleQueries

instance : Preorder CircuitCost where
  le_refl a := ⟨le_refl _, le_refl _, le_refl _⟩
  le_trans a b c h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₁.2.1 h₂.2.1,
    le_trans h₁.2.2 h₂.2.2⟩

end CircuitCost

/-! ### Model -/

/-- Quantum circuit model parameterized by an oracle unitary. -/
noncomputable def quantumCircuitModel (n : ℕ) (oracle : QState n → QState n) :
    Model (QuantumCircuit n) CircuitCost where
  evalQuery
    | .gate q => evalGate oracle q
    | .seq c₁ c₂ =>
        fun s => QuantumCircuit.circEval oracle c₂ (QuantumCircuit.circEval oracle c₁ s)
    | .par c₁ c₂ => QuantumCircuit.circEval oracle c₂ ∘ QuantumCircuit.circEval oracle c₁
  cost c := ⟨c.size, c.depthOf, c.oracleCount⟩

/-! ### Prog integration -/

/-- Apply a circuit to a state, threading through `Prog`. -/
def applyCircuit (c : QuantumCircuit n (QState n → QState n))
    (s : QState n) : Prog (QuantumCircuit n) (QState n) :=
  FreeM.liftBind c fun f => pure (f s)

/-! ### Circuit families -/

/-- A quantum circuit family: for each input size `n`, a circuit. -/
structure CircuitFamily where
  /-- The circuit for input size `n`. -/
  circuit : (n : ℕ) → QuantumCircuit n (QState n → QState n)

/-- The output state of a circuit family given an oracle unitary. -/
noncomputable def CircuitFamily.output (fam : CircuitFamily)
    (n : ℕ) (oracle : QState n → QState n) : QState n :=
  fam.circuit n |>.circEval oracle (QState.initial n)

/-- A language over `n`-qubit inputs. -/
abbrev BoolLanguage := (n : ℕ) → ((Fin n → Fin 2) → Bool) → Prop

/-- A circuit family decides a language with bounded error,
using the phase kickback oracle `O_f`. -/
def CircuitFamily.DecidesBounded (fam : CircuitFamily)
    (L : BoolLanguage) : Prop :=
  ∀ n (f : (Fin n → Fin 2) → Bool)
    (hn : (fam.output n (gateOracle f)).IsNormalized),
    (L n f → measureDistribution (fam.output n (gateOracle f)) hn
      0 ≥ ENNReal.ofReal (2 / 3)) ∧
    (¬L n f → measureDistribution (fam.output n (gateOracle f)) hn
      0 ≤ ENNReal.ofReal (1 / 3))

/-- A circuit family decides a language with zero error,
using the phase kickback oracle `O_f`. -/
def CircuitFamily.DecidesExact (fam : CircuitFamily)
    (L : BoolLanguage) : Prop :=
  ∀ n (f : (Fin n → Fin 2) → Bool)
    (hn : (fam.output n (gateOracle f)).IsNormalized),
    (L n f → measureDistribution (fam.output n (gateOracle f)) hn
      0 = 1) ∧
    (¬L n f → measureDistribution (fam.output n (gateOracle f)) hn
      0 = 0)

/-! ### Complexity classes -/

open Polynomial

/-- **BQP/poly**: polynomial-size circuit family with bounded error. -/
def BQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    ∀ n, (fam.circuit n).size ≤ p.eval n

/-- **EQP/poly**: polynomial-size circuit family with zero error. -/
def EQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesExact L ∧
    ∀ n, (fam.circuit n).size ≤ p.eval n

/-- **QNC^k/poly**: polynomial size, O(log^k n) depth, bounded error. -/
def QNCpoly (L : BoolLanguage) (k : ℕ) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    (∀ n, (fam.circuit n).size ≤ p.eval n) ∧
    (∀ n, (fam.circuit n).depthOf ≤ (Nat.log 2 n) ^ k)

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
