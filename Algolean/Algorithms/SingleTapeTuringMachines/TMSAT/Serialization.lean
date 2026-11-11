/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Serialization
public import Algolean.Problems.TMSAT.Serialization

/-!
# Writing TMSAT instances in polynomial time

The machine writes a fixed verifier description, the encoded input, and the certificate and
time bounds. Each bound is a fixed polynomial evaluated at the input length. The bound is
written as that many copies of a fixed word. The complete result is exactly the word produced
by `encodingOver`.

The verifier and both polynomials are chosen once for the whole reduction. One finite machine
handles every input length and uses the same alphabet for its input and output.

For input length `n`, the machine uses at most `C * (n + m(n) + t(n) + 1)^2` head moves.
The constant `C` depends only on the verifier, the two polynomials, and the fixed alphabet.
The record's `computesWithin` field proves this bound and correctness on every input. Its
total space bound adds the initial input space `max 1 n` to the time bound.
-/

public section

namespace Algolean.Algorithms.SingleTapeTuringMachines

open Cslib.Turing Polynomial Problems.TMSAT
open PolynomialWriter

variable {Γ : Type} [Inhabited Γ] [Fintype Γ] [Nontrivial Γ]

private noncomputable def boundsFields (m t : Polynomial Nat) :
    List (List Γ × Polynomial Nat) :=
  [(Serialization.unary, m), (Serialization.separator, 1), (Serialization.unary, t)]

/--
This constant depends only on the fixed verifier, the two bound polynomials, and the alphabet.
It is the coefficient of the quadratic time bound for writing the instance.
-/
noncomputable def tmsatSerializerTimeFactor
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (m t : Polynomial Nat) : Nat := by
  classical
  exact serializerTimeFactor Serialization.symbolCode (Serialization.header verifier)
    Serialization.ending (boundsFields m t) *
      ((Serialization.unary (Γ := Γ)).length + (Serialization.separator (Γ := Γ)).length + 2) ^ 2

private theorem tmsat_bound [DecidableEq Γ]
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (m t : Polynomial Nat) (n : Nat) :
    (serializerComputer Serialization.symbolCode Serialization.symbolCode_ne_nil
      (Serialization.header verifier) Serialization.ending (boundsFields m t)).poly.eval n ≤
      tmsatSerializerTimeFactor verifier m t * (n + m.eval n + t.eval n + 1) ^ 2 := by
  let U := (Serialization.unary (Γ := Γ)).length
  let V := (Serialization.separator (Γ := Γ)).length
  let D := U + V + 2
  have hwork : (fieldsWork (boundsFields (Γ := Γ) m t)).eval n =
      (U + 1) * m.eval n + (V + 1) + (U + 1) * t.eval n := by
    simp [boundsFields, fieldsWork, U, V, Nat.add_assoc]
  have hsize : n + (fieldsWork (boundsFields (Γ := Γ) m t)).eval n + 1 ≤
      D * (n + m.eval n + t.eval n + 1) := by
    have hn := Nat.mul_le_mul_right n (show 1 ≤ D by dsimp [D]; lia)
    have hm := Nat.mul_le_mul_right (m.eval n) (show U + 1 ≤ D by dsimp [D]; lia)
    have ht := Nat.mul_le_mul_right (t.eval n) (show U + 1 ≤ D by dsimp [D]; lia)
    have hd : V + 2 ≤ D := by dsimp [D]; lia
    rw [hwork]
    simp only [Nat.mul_add, Nat.mul_one] at *
    lia
  rw [serializerComputer_poly]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  have h := Nat.mul_le_mul_left
    (serializerTimeFactor Serialization.symbolCode (Serialization.header verifier)
      Serialization.ending (boundsFields m t)) (Nat.pow_le_pow_left hsize 2)
  simpa only [tmsatSerializerTimeFactor, D, U, V, mul_pow, Nat.mul_assoc] using h

/--
This constructs a machine with a quadratic time bound in the input length plus the certificate
and time bounds being written. The verifier and both polynomials are fixed when constructing
the machine. It reads the input from its tape, computes both bounds from the input length,
and writes exactly the word that `encodingOver` assigns to the instance.
-/
noncomputable def tmsatSerializer (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (m t : Polynomial Nat) :
    TMQuery.PolyTimeComputable (fun input =>
      encodingOver.encode (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
        Instance Γ)) := by
  classical
  let computer := serializerComputer Serialization.symbolCode Serialization.symbolCode_ne_nil
    (Serialization.header verifier) Serialization.ending (boundsFields m t)
  let coefficient := tmsatSerializerTimeFactor verifier m t
  have hbound (n : Nat) : computer.poly.eval n ≤
      coefficient * (n + m.eval n + t.eval n + 1) ^ 2 := tmsat_bound verifier m t n
  letI := computer.symbolDecidableEq
  letI := computer.stateDecidableEq
  refine {
    tm := computer.tm
    program := computer.program
    timeBound := fun n => coefficient * (n + m.eval n + t.eval n + 1) ^ 2
    poly := C coefficient * (X + m + t + 1) ^ 2
    bounds := by intro n; simp
    computesWithin := ?_ }
  apply (computer.computesWithin_poly.mono hbound
    (fun n => Nat.add_le_add_left (hbound n) (max 1 n))).consequence
  intro input cfg htape
  have hword : Serialization.header verifier ++ input.flatMap Serialization.symbolCode ++
      Serialization.ending ++ fieldsWord (boundsFields m t) input.length =
        encodingOver.encode
          (⟨verifier, input, m.eval input.length, t.eval input.length⟩ : Instance Γ) := by
    rw [Serialization.encode_instance]
    simp [boundsFields, fieldsWord, List.append_assoc]
  change cfg.BiTape = BiTape.mk₁ _ at htape ⊢
  simpa only [hword] using htape

private theorem tmsatSerializer_poly_impl
    (verifier : SingleTapeTM.Description (TapeSymbol Γ)) (m t : Polynomial Nat) :
    (tmsatSerializer verifier m t).poly =
      C (tmsatSerializerTimeFactor verifier m t) * (X + m + t + 1) ^ 2 := rfl

/-- This is the polynomial stored with the machine that writes the instance. -/
theorem tmsatSerializer_poly (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (m t : Polynomial Nat) :
    (tmsatSerializer verifier m t).poly =
      C (tmsatSerializerTimeFactor verifier m t) * (X + m + t + 1) ^ 2 :=
  tmsatSerializer_poly_impl verifier m t

/--
If both bound polynomials have degree at most `d`, with `d ≥ 1`, the stored time polynomial
has degree at most `2 * d`. The maximum with one accounts for the original input length.
-/
theorem tmsatSerializer_natDegree_le (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (m t : Polynomial Nat) :
    (tmsatSerializer verifier m t).poly.natDegree ≤
      2 * max 1 (max m.natDegree t.natDegree) := by
  let d := max 1 (max m.natDegree t.natDegree)
  have hx : (X : Polynomial Nat).natDegree ≤ d := by simp [d]
  have hm : m.natDegree ≤ d := (le_max_left _ _).trans (le_max_right _ _)
  have ht : t.natDegree ≤ d := (le_max_right _ _).trans (le_max_right _ _)
  have hone : (1 : Polynomial Nat).natDegree ≤ d := by simp
  have hsum := natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hx hm) ht) hone
  rw [tmsatSerializer_poly]
  refine natDegree_mul_le.trans ?_
  simp only [natDegree_C, zero_add]
  exact natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hsum)

/--
Writing the instance takes at most `C * (n + m(n) + t(n) + 1)^2` head moves. Here `n` is the input
length, and `C` is fixed by the verifier, the two polynomials, and the alphabet. The same finite
program runs for every input length.
-/
theorem tmsatSerializer_time_bound (verifier : SingleTapeTM.Description (TapeSymbol Γ))
    (m t : Polynomial Nat) (input : List Γ) :
    let computer := tmsatSerializer verifier m t
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    TMQuery.OutputsWithinTime computer.program input
      (encodingOver.encode (⟨verifier, input, m.eval input.length, t.eval input.length⟩ :
        Instance Γ))
      (tmsatSerializerTimeFactor verifier m t *
        (input.length + m.eval input.length + t.eval input.length + 1) ^ 2) := by
  let computer := tmsatSerializer verifier m t
  let := computer.symbolDecidableEq
  let := computer.stateDecidableEq
  apply (computer.outputsFunInTime input).mono
  apply (computer.bounds input.length).trans
  rw [tmsatSerializer_poly]
  simp

end Algolean.Algorithms.SingleTapeTuringMachines
