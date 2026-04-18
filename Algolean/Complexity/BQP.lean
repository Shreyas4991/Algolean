/-
Copyright (c) 2026 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/

module

public import Algolean.Models.Quantum.Circuit
public import Algolean.Models.SingleTapeTM

@[expose] public section

/-!
# Uniform quantum complexity classes

`BQP`, `EQP`, and uniform `QNC^k` — the standard TM-uniform quantum
complexity classes. Each is a cross-model statement: a classical
`Prog (TMQuery tm)` generator produces the circuit description for each
input size, bounded in `TMCost.steps` by a polynomial, and the generated
`QuantumCircuit` decides `L` with the class's error discipline.

## Design

Two layers of `Prog`, both measured by `Prog.time` against their own
`Model`, combined through the `UniformFamily` abstraction from
`Complexity/Basic.lean`:

- **Classical layer**: `UniformFamily (TMQuery tm)` with
  `fam.Uniform (TMModel tm)` the poly-time generator bound.
- **Quantum layer**: the generated `QuantumCircuit n`, interpreted via
  `QuantumCircuit.toCPTP`, applied to the initial `|0...0⟩` state, with
  the first-qubit measurement distribution satisfying the class spec.

The TM's tape alphabet is fixed to `Bool` — uniformity doesn't need a
polymorphic alphabet and this avoids existential quantification over
typeclass instances. Non-uniform `BQP/poly` is `BQPpoly` in `Circuit.lean`.
-/

namespace Algolean
namespace Algorithms

open Cslib Polynomial Turing

/-- The correctness spec for a generated quantum circuit: poly-size and
decides `L` with bounded error on the first-qubit measurement. -/
def BQPSpec (L : BoolLanguage) (p_size : Polynomial ℕ) (n : ℕ)
    (c : QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))) : Prop :=
  c.size ≤ p_size.eval n ∧
  ∀ (hn : 0 < n) (f : (Fin n → Fin 2) → Bool),
    let ρ := c.toCPTP (extendOracle (gateOracle f)) (initialMState n)
    (L n f → measureFirstQubit ρ 1 hn ≥ 2 / 3) ∧
    (¬ L n f → measureFirstQubit ρ 1 hn ≤ 1 / 3)

/-- The correctness spec for exact (zero-error) quantum decision. -/
def EQPSpec (L : BoolLanguage) (p_size : Polynomial ℕ) (n : ℕ)
    (c : QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))) : Prop :=
  c.size ≤ p_size.eval n ∧
  ∀ (hn : 0 < n) (f : (Fin n → Fin 2) → Bool),
    let ρ := c.toCPTP (extendOracle (gateOracle f)) (initialMState n)
    (L n f → measureFirstQubit ρ 1 hn = 1) ∧
    (¬ L n f → measureFirstQubit ρ 1 hn = 0)

/-- The correctness spec for `QNC^k`: poly-size, polylog-depth, bounded error. -/
def QNCSpec (L : BoolLanguage) (p_size : Polynomial ℕ) (k n : ℕ)
    (c : QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))) : Prop :=
  c.size ≤ p_size.eval n ∧
  c.depthOf ≤ (Nat.log 2 n) ^ k ∧
  ∀ (hn : 0 < n) (f : (Fin n → Fin 2) → Bool),
    let ρ := c.toCPTP (extendOracle (gateOracle f)) (initialMState n)
    (L n f → measureFirstQubit ρ 1 hn ≥ 2 / 3) ∧
    (¬ L n f → measureFirstQubit ρ 1 hn ≤ 1 / 3)

/-- **BQP** — uniform bounded-error quantum polynomial time. A classical
single-tape TM generates a poly-size quantum circuit family deciding `L`
with error ≤ 1/3, and the generator runs in polynomial time. -/
def BQP (L : BoolLanguage) : Prop :=
  ∃ (tm : SingleTapeTM Bool)
    (fam : UniformFamily (TMQuery tm)
      (fun n => QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))))
    (p_gen p_size : Polynomial ℕ),
    fam.Uniform (TMModel tm) (fun n => ⟨p_gen.eval n, p_gen.eval n⟩) ∧
    fam.SatisfiesSpec (TMModel tm) (BQPSpec L p_size)

/-- **EQP** — uniform exact quantum polynomial time. -/
def EQP (L : BoolLanguage) : Prop :=
  ∃ (tm : SingleTapeTM Bool)
    (fam : UniformFamily (TMQuery tm)
      (fun n => QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))))
    (p_gen p_size : Polynomial ℕ),
    fam.Uniform (TMModel tm) (fun n => ⟨p_gen.eval n, p_gen.eval n⟩) ∧
    fam.SatisfiesSpec (TMModel tm) (EQPSpec L p_size)

/-- **QNC^k** — uniform polylogarithmic-depth bounded-error quantum circuits. -/
def QNC (L : BoolLanguage) (k : ℕ) : Prop :=
  ∃ (tm : SingleTapeTM Bool)
    (fam : UniformFamily (TMQuery tm)
      (fun n => QuantumCircuit n (CPTPMap (Fin n → Fin 2) (Fin n → Fin 2))))
    (p_gen p_size : Polynomial ℕ),
    fam.Uniform (TMModel tm) (fun n => ⟨p_gen.eval n, p_gen.eval n⟩) ∧
    fam.SatisfiesSpec (TMModel tm) (QNCSpec L p_size k)

/-! ### Containments -/

/-- EQP ⊆ BQP. -/
theorem EQP.toBQP {L : BoolLanguage} (h : EQP L) : BQP L := by
  obtain ⟨tm, fam, p_gen, p_size, hU, hS⟩ := h
  refine ⟨tm, fam, p_gen, p_size, hU, ?_⟩
  intro n
  obtain ⟨hSize, hExact⟩ := hS n
  refine ⟨hSize, fun hn f => ?_⟩
  obtain ⟨hYes, hNo⟩ := hExact hn f
  refine ⟨fun hL => ?_, fun hL => ?_⟩
  · rw [hYes hL]; norm_num
  · rw [hNo hL]; norm_num

/-- QNC^k ⊆ BQP. -/
theorem QNC.toBQP {L : BoolLanguage} {k : ℕ} (h : QNC L k) : BQP L := by
  obtain ⟨tm, fam, p_gen, p_size, hU, hS⟩ := h
  refine ⟨tm, fam, p_gen, p_size, hU, ?_⟩
  intro n
  obtain ⟨hSize, _, hDecides⟩ := hS n
  exact ⟨hSize, hDecides⟩

end Algorithms
end Algolean
