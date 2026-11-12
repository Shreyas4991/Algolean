/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPToTMSAT.Initial

/-!
# Reading the initial tape from the original input

These lemmas identify the initial symbol at each recorded position. The two outer intervals
are blank. Between them lie the original input, one separating symbol, and the certificate.
The direct reduction uses the original input word to choose which initial clause to write.
-/

public section

namespace Algolean.Algorithms.NPToSAT.InitialSource

open Cslib.Turing Problems.TMSAT NPToTMSAT

variable {Γ : Type}

/-- Every recorded position before the input contains a blank. -/
theorem blank_left (problem : Instance Γ) (position : Fin (width problem))
    (hleft : position.val < problem.time) : initialSource problem position = .inl none := by
  simp [initialSource, hleft]

/-- Every recorded position in the right blank interval contains a blank. -/
theorem blank_right (problem : Instance Γ) (position : Fin (width problem)) (rest : Nat)
    (hposition : position.val + rest + 1 = width problem) (hright : rest < problem.time) :
    initialSource problem position = .inl none := by
  rcases position with ⟨position, hbound⟩
  simp only [width] at hposition
  unfold initialSource
  split_ifs <;> first | rfl | (exfalso; lia)

/-- Looking up a symbol in the original input determines the corresponding initial tape cell. -/
theorem input (problem : Instance Γ) (position : Fin (width problem)) (symbol : Γ)
    (hleft : problem.time ≤ position.val)
    (hlookup : problem.input[position.val - problem.time]? = some symbol) :
    initialSource problem position = .inl (some (.inl symbol)) := by
  obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hlookup
  simp only [initialSource, dite_eq_right (by lia : ¬position.val < problem.time),
    dite_eq_left (by lia : position.val < problem.time + problem.input.length)]
  simp only [hvalue]

/-- The cell immediately after the original input contains the certificate separator. -/
theorem separator (problem : Instance Γ) (position : Fin (width problem))
    (hposition : position.val = problem.time + problem.input.length) :
    initialSource problem position = .inl (some (.inr 0)) := by
  simp [initialSource, hposition]

/-- The cells after the separator refer to their corresponding certificate positions. -/
theorem certificate (problem : Instance Γ) (position : Fin (width problem))
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

/-- An interior position beyond the input and separator has a valid certificate index. -/
theorem certificate_index_lt (problem : Instance Γ) (position : Fin (width problem))
    (rest : Nat) (hposition : position.val + rest + 1 = width problem)
    (hright : problem.time ≤ rest)
    (hremaining : 0 < position.val - problem.time - problem.input.length) :
    position.val - problem.time - problem.input.length - 1 < problem.certificateLength := by
  rcases position with ⟨position, hbound⟩
  simp only [width] at hposition
  lia

end Algolean.Algorithms.NPToSAT.InitialSource
