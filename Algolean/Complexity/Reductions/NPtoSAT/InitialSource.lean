/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.Computation.Initial

/-!
# Identifying the verifier's initial tape symbols

* `blank_left` and `blank_right` identify the blank cells on either side of the input and
  certificate. Each side contains as many blank cells as the transition bound.
* `input` and `separator` identify the original input symbols and the following separator.
* `certificate` and `certificate_index_lt` identify the certificate positions after the separator.

These facts let the reduction choose the initial clause for each simulated tape cell.
-/

open Cslib.Turing.SingleTapeTM
open BoundedVerification

public section

namespace Algolean.Algorithms.NPToSAT.InitialSource

open Cslib.Turing NPToSAT.Computation

variable {Γ : Type}

/-- Every simulated tape position before the input contains a blank. -/
theorem blank_left (problem : BoundedVerification Γ) (position : Fin (width problem))
    (hleft : position.val < problem.time) : initialSource problem position = .inl none := by
  simp [initialSource, hleft]

/-- Every simulated tape position in the right blank interval contains a blank. -/
theorem blank_right (problem : BoundedVerification Γ) (position : Fin (width problem)) (rest : Nat)
    (hposition : position.val + rest + 1 = width problem) (hright : rest < problem.time) :
    initialSource problem position = .inl none := by
  rcases position with ⟨position, hbound⟩
  simp only [width] at hposition
  unfold initialSource
  split_ifs <;> first | rfl | (exfalso; lia)

/--
A symbol in the original input determines the corresponding cell of the verifier's initial tape.
-/
theorem input (problem : BoundedVerification Γ) (position : Fin (width problem)) (symbol : Γ)
    (hleft : problem.time ≤ position.val)
    (hlookup : problem.input[position.val - problem.time]? = some symbol) :
    initialSource problem position = .inl (some (.inl symbol)) := by
  obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hlookup
  simp only [initialSource, dite_eq_right (by lia : ¬position.val < problem.time),
    dite_eq_left (by lia : position.val < problem.time + problem.input.length)]
  simp only [hvalue]

/-- The cell immediately after the original input contains the certificate separator. -/
theorem separator (problem : BoundedVerification Γ) (position : Fin (width problem))
    (hposition : position.val = problem.time + problem.input.length) :
    initialSource problem position = .inl (some (.inr 0)) := by
  simp [initialSource, hposition]

/-- The cells after the separator correspond to the certificate positions. -/
theorem certificate (problem : BoundedVerification Γ) (position : Fin (width problem))
    (index : Fin problem.certificateLength)
    (hposition : position.val = problem.time + problem.input.length + 1 + index.val) :
    initialSource problem position = .inr index := by
  unfold initialSource
  split_ifs
  all_goals
    try (exfalso; lia)
  congr 1
  apply Fin.ext
  simp only
  lia

/-- A position between the separator and the right blank interval has a valid certificate index. -/
theorem certificate_index_lt (problem : BoundedVerification Γ) (position : Fin (width problem))
    (rest : Nat) (hposition : position.val + rest + 1 = width problem)
    (hright : problem.time ≤ rest)
    (hremaining : 0 < position.val - problem.time - problem.input.length) :
    position.val - problem.time - problem.input.length - 1 < problem.certificateLength := by
  rcases position with ⟨position, hbound⟩
  simp only [width] at hposition
  lia

end Algolean.Algorithms.NPToSAT.InitialSource
