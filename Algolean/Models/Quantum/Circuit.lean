/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Oracle
public import Algolean.Models.Quantum.Indexing
public import QuantumInfo.Finite.CPTPMap
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

/-!
# Quantum Circuits

Tree-structured quantum circuits (gate / sequential / parallel composition)
with a denotational interpretation into `CPTPMap`. Each circuit node is an
atomic query in `Prog`; cost is counted structurally as depth (max on
parallel), gate count, and oracle queries.

## Main definitions

- `QuantumCircuit n`: syntactic circuit tree. The output-type index is
  `CPTPMap (Fin n → Fin 2) (Fin n → Fin 2)`.
- `QuantumCircuit.toCPTP`: denotational semantics — each tree node maps to
  its channel via `CPTPMap.ofUnitary`, `∘ₘ`, and `⊗ᶜᵖ` composed with
  `finFunSplitEquiv`.
- `CircuitCost`, `quantumCircuitModel`: cost structure and Model instance.
- `CircuitFamily`, `BQPpoly`, `EQPpoly`, `QNCpoly`: non-uniform complexity
  classes.

## Design

`QuantumCircuit n` is a self-recursive inductive tree. Queries at the Prog
level are single tree nodes (`.gate`, `.seq`, `.par`), so `Prog.time` sums
per-query costs and `depth` uses `max` for parallel composition.

The denotational interpretation `toCPTP` is what the `Model`'s `evalQuery`
produces. There is no separate operational `eval` — `CPTPMap d d` *is* the
semantic object.
-/

namespace Algolean

namespace Algorithms

open Complex Cslib Polynomial

/-! ### Syntax -/

/-- Quantum circuit syntax tree. Leaves (`.gate`) wrap a single `QuantumQuery`;
`.seq` composes circuits sequentially on the same register; `.par` is
tensor product on disjoint registers. -/
inductive QuantumCircuit : ℕ → Type → Type where
  /-- Single gate leaf. -/
  | gate {n : ℕ} (q : QuantumQuery n (𝐔[Fin n → Fin 2])) :
      QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))
  /-- Sequential composition on the same register. -/
  | seq {n : ℕ} (c₁ c₂ : QuantumCircuit n
      (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))) :
      QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))
  /-- Parallel composition via tensor on disjoint registers. -/
  | par {m k : ℕ}
      (c₁ : QuantumCircuit m (CPTPMap (Fin m → Fin 2) (Fin m → Fin 2)))
      (c₂ : QuantumCircuit k (CPTPMap (Fin k → Fin 2) (Fin k → Fin 2))) :
      QuantumCircuit (m + k)
        (CPTPMap (Fin (m + k) → Fin 2) (Fin (m + k) → Fin 2))

namespace QuantumCircuit

/-! ### Cost observations -/

/-- Circuit depth: sequential sums, parallel takes max. -/
@[simp]
def depthOf : {n : ℕ} → {ι : Type} → QuantumCircuit n ι → ℕ
  | _, _, .gate _ => 1
  | _, _, .seq c₁ c₂ => depthOf c₁ + depthOf c₂
  | _, _, .par c₁ c₂ => max (depthOf c₁) (depthOf c₂)

/-- Total gate count. -/
@[simp]
def size : {n : ℕ} → {ι : Type} → QuantumCircuit n ι → ℕ
  | _, _, .gate _ => 1
  | _, _, .seq c₁ c₂ => size c₁ + size c₂
  | _, _, .par c₁ c₂ => size c₁ + size c₂

/-- Number of oracle queries. -/
@[simp]
def oracleCount : {n : ℕ} → {ι : Type} → QuantumCircuit n ι → ℕ
  | _, _, .gate .oracle => 1
  | _, _, .gate _ => 0
  | _, _, .seq c₁ c₂ => oracleCount c₁ + oracleCount c₂
  | _, _, .par c₁ c₂ => oracleCount c₁ + oracleCount c₂

/-! ### Denotational semantics -/

/-- Interpret a circuit tree into its `CPTPMap` semantics. The three
clauses mirror the three syntactic constructors:
- `.gate q` → `CPTPMap.ofUnitary (unitaryOf ...)`
- `.seq c₁ c₂` → `toCPTP c₂ ∘ₘ toCPTP c₁`
- `.par c₁ c₂` → tensor via `⊗ᶜᵖ`, conjugated through `finFunSplitEquiv`. -/
noncomputable def toCPTP (oracle : OracleFamily) :
    {n : ℕ} → {ι : Type} → QuantumCircuit n ι → ι
  | _, _, .gate q => CPTPMap.ofUnitary (unitaryOf (oracle _) q)
  | _, _, .seq c₁ c₂ => (toCPTP oracle c₂).compose (toCPTP oracle c₁)
  | _, _, @QuantumCircuit.par m k c₁ c₂ =>
      let e := finFunSplitEquiv m k (Fin 2)
      CPTPMap.ofEquiv e.symm
        |>.compose ((toCPTP oracle c₁).prod (toCPTP oracle c₂))
        |>.compose (CPTPMap.ofEquiv e)

end QuantumCircuit

/-! ### Cost structure -/

/-- Cost tuple for quantum circuits: depth, gate count, and oracle queries
tracked separately. -/
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

/-- Equivalence with the product type. -/
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

/-- Cost model for `QuantumCircuit`. `evalQuery` is the denotational
semantics `toCPTP`; `cost` records the structural depth, size, and
oracle count. -/
noncomputable def quantumCircuitModel (n : ℕ) (oracle : OracleFamily) :
    Model (QuantumCircuit n) CircuitCost where
  evalQuery q := q.toCPTP oracle
  cost q := ⟨q.depthOf, q.size, q.oracleCount⟩

/-! ### Circuit families -/

/-- A quantum circuit family: for each input size `n`, a `Prog` whose
evaluation produces a `CPTPMap` — the denotational circuit acting on
the full `n`-qubit register. -/
structure CircuitFamily where
  /-- The circuit for input size `n`, as a `Prog` producing its denotation. -/
  circuit : (n : ℕ) →
    Prog (QuantumCircuit n) (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))

/-- Initial density matrix: pure `|0...0⟩⟨0...0|`. -/
noncomputable def initialMState (n : ℕ) : MState (Fin n → Fin 2) :=
  MState.pure (Ket.basis 0)

/-- The output state of a circuit family on input size `n` under a
Boolean-function oracle `f`. The circuit is evaluated to its channel
via `quantumCircuitModel`, then applied to the initial all-zeros state. -/
noncomputable def CircuitFamily.output (fam : CircuitFamily)
    (n : ℕ) (f : (Fin n → Fin 2) → Bool) : MState (Fin n → Fin 2) :=
  let channel := (fam.circuit n).eval
    (quantumCircuitModel n (extendOracle (gateOracle f)))
  channel (initialMState n)

/-- A Boolean language: a predicate on bitstring inputs of each size. -/
abbrev BoolLanguage := (n : ℕ) → ((Fin n → Fin 2) → Bool) → Prop

/-- Measurement of the first qubit of the output state: probability that
qubit 0 yields outcome `v`. -/
noncomputable def measureFirstQubit {n : ℕ} (ρ : MState (Fin n → Fin 2))
    (v : Fin 2) (h : 0 < n) : ℝ :=
  (((measureQubitPOVM ⟨0, h⟩).measure ρ) v : ℝ)

/-- A family decides `L` with bounded error (BPP-style 2/3 threshold),
measuring the first qubit of the output state. -/
def CircuitFamily.DecidesBounded (fam : CircuitFamily) (L : BoolLanguage) : Prop :=
  ∀ n (hn : 0 < n) (f : (Fin n → Fin 2) → Bool),
    (L n f →
      measureFirstQubit (fam.output n f) 1 hn ≥ 2 / 3) ∧
    (¬ L n f →
      measureFirstQubit (fam.output n f) 1 hn ≤ 1 / 3)

/-- A family decides `L` exactly. -/
def CircuitFamily.DecidesExact (fam : CircuitFamily) (L : BoolLanguage) : Prop :=
  ∀ n (hn : 0 < n) (f : (Fin n → Fin 2) → Bool),
    (L n f → measureFirstQubit (fam.output n f) 1 hn = 1) ∧
    (¬ L n f → measureFirstQubit (fam.output n f) 1 hn = 0)

/-! ### Non-uniform complexity classes -/

/-- **BQP/poly**: polynomial-size circuit family with bounded error. -/
def BQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    ∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates ≤ p.eval n

/-- **EQP/poly**: polynomial-size circuit family with zero error. -/
def EQPpoly (L : BoolLanguage) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesExact L ∧
    ∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates ≤ p.eval n

/-- **QNC^k/poly**: polynomial size, `O(log^k n)` depth, bounded error. -/
def QNCpoly (L : BoolLanguage) (k : ℕ) : Prop :=
  ∃ (fam : CircuitFamily) (p : Polynomial ℕ),
    fam.DecidesBounded L ∧
    (∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).gates
          ≤ p.eval n) ∧
    (∀ n (f : (Fin n → Fin 2) → Bool),
      ((fam.circuit n).time
        (quantumCircuitModel n (extendOracle (gateOracle f)))).depth
          ≤ (Nat.log 2 n) ^ k)

/-! ### Containments -/

/-- EQP/poly ⊆ BQP/poly. -/
theorem EQPpoly.toBQPpoly {L : BoolLanguage} (h : EQPpoly L) : BQPpoly L := by
  obtain ⟨fam, p, hExact, hSize⟩ := h
  refine ⟨fam, p, ?_, hSize⟩
  intro n hn f
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · rw [(hExact n hn f).1 hL]; norm_num
  · rw [(hExact n hn f).2 hL]; norm_num

/-- QNC^k/poly ⊆ BQP/poly. -/
theorem QNCpoly.toBQPpoly {L : BoolLanguage} {k : ℕ}
    (h : QNCpoly L k) : BQPpoly L := by
  obtain ⟨fam, p, hDecides, hSize, _⟩ := h
  exact ⟨fam, p, hDecides, hSize⟩

end Algorithms

end Algolean
