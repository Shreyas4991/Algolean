/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.MachineComposition

/-!
# Solving one problem by converting its input

This file describes Karp reductions. A reduction converts an input for one yes/no problem into
an input for another problem with the same answer. A fixed tape program must perform the
conversion in time bounded by a polynomial in the input length.

A solver for the second problem then gives a solver for the first: convert the input and run the
solver once. The conversion preserves both yes and no answers. For example, flipping every bit
converts the question "Does this word contain a true bit?" into "Does it contain a false bit?"

## Main definitions and results

* [KarpReduction](##Algolean.Algorithms.KarpReduction) stores the conversion, its program, and
  its correctness proof.
* [KarpReducible](##Algolean.Algorithms.KarpReducible) states that such a reduction exists.
* [KarpReduction.trans](##Algolean.Algorithms.KarpReduction.trans) runs two conversions in
  sequence.
* [KarpReduction.complement](##Algolean.Algorithms.KarpReduction.complement) reverses the
  answers to both problems.
* [KarpReduction.preservesP](##Algolean.Algorithms.KarpReduction.preservesP) transfers a solver
  with a polynomial time bound to the first problem.
-/

@[expose] public section

namespace Algolean.Algorithms

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/--
A Karp reduction converts inputs for the source problem into inputs for the target problem,
preserving yes and no answers. One fixed program performs the conversion with a polynomial time
bound.
-/
structure KarpReduction (source target : Language Symbol) where
  /-- This function specifies the input that the conversion program must produce. -/
  transform : List Symbol → List Symbol
  /-- This program produces the specified converted input with a polynomial time bound. -/
  computer : TMQuery.PolyTimeComputable transform
  /-- The source answer is yes exactly when the target answer on the converted input is yes. -/
  correct : ∀ input, input ∈ source ↔ transform input ∈ target

/-- A [KarpReduction](##Algolean.Algorithms.KarpReduction) exists between the two problems. -/
def KarpReducible (source target : Language Symbol) : Prop := Nonempty (KarpReduction source target)

namespace KarpReduction

variable {A B C : Language Symbol}

/-- Every problem reduces to itself by leaving its input unchanged. -/
noncomputable def refl (A : Language Symbol) : KarpReduction A A where
  transform := id
  computer := TMQuery.PolyTimeComputable.id
  correct _ := Iff.rfl

/--
The first conversion is followed by the second conversion. Their composition preserves answers
and has a polynomial time bound.
-/
noncomputable def trans (first : KarpReduction A B) (second : KarpReduction B C) :
    KarpReduction A C where
  transform := second.transform ∘ first.transform
  computer := first.computer.comp second.computer
  correct input := (first.correct input).trans (second.correct (first.transform input))

/-- The same conversion gives a reduction when yes and no are reversed for both problems. -/
def complement (reduction : KarpReduction A B) :
    KarpReduction Aᶜ Bᶜ where
  transform := reduction.transform
  computer := reduction.computer
  correct input := not_congr (reduction.correct input)

/--
If the target problem belongs to [P](##Algolean.Algorithms.P), then the source problem does too.
Its solver converts the input and then runs the target solver.
-/
theorem preservesP [Nontrivial Symbol] (reduction : KarpReduction A B) (target : B ∈ P) :
    A ∈ P := by
  obtain ⟨f, yes, ⟨machine⟩, h⟩ := target
  exact ⟨f ∘ reduction.transform, yes, ⟨reduction.computer.comp machine⟩,
    fun input => (h (reduction.transform input)).trans (reduction.correct input).symm⟩

end KarpReduction

/-- Every problem has a Karp reduction to itself. -/
theorem KarpReducible.refl (A : Language Symbol) : KarpReducible A A := ⟨KarpReduction.refl A⟩

/--
If the first problem reduces to the second and the second reduces to the third, then the first
reduces to the third.
-/
theorem KarpReducible.trans {A B C : Language Symbol}
    (first : KarpReducible A B) (second : KarpReducible B C) : KarpReducible A C := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨first.trans second⟩

end Algolean.Algorithms
