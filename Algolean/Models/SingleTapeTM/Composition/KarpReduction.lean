/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Computability

/-!
# Karp reductions

Suppose `source` and `target` are two yes/no problems about lists of symbols. In Lean,
`source input` means that the source problem's answer on `input` is yes. The set of inputs
with a yes answer is called a *language*.

A Karp reduction converts an input for `source` into an input for `target` with the same answer.
Yes must stay yes, and no must stay no. If we have a program that answers `target` questions,
we can answer a `source` question by first converting its input, then using that program once.
The conversion itself works without asking for the target problem's answer.

For example, let the source question be "Does this Boolean word contain a true bit?" and the
target question be "Does it contain a false bit?" Flipping every bit gives a suitable
conversion: the original word contains a true bit exactly when the new word contains a false bit.

The conversion must have a *polynomial time bound*: a formula such as `n² + 3n + 1` limits its
time on inputs of length `n`. Here, each tape-head move instruction costs one time step.
One fixed machine program must perform the conversion for every input. `transform` describes
the desired output; `computer` supplies the program and its time bound; `correct` proves that
the conversion preserves the answer.
-/

@[expose] public section

namespace Algolean.Algorithms

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- Convert inputs for `source` into inputs for `target`, preserving yes/no answers and using
a fixed machine program with a polynomial time bound. This is called a Karp reduction. -/
structure KarpReduction (source target : Language Symbol) where
  /-- The desired converted input. The machine below must actually produce this list. -/
  transform : List Symbol → List Symbol
  /-- The machine program that produces `transform input`, with a polynomial time bound. -/
  computer : TMQuery.PolyTimeComputable transform
  /-- The original question has answer yes exactly when the converted question has answer yes. -/
  correct : ∀ input, source input ↔ target (transform input)

/-- There is a Karp reduction from `source` to `target`.
`KarpReduction` stores the conversion, machine, and proofs; this states that such data exists. -/
def KarpReducible (source target : Language Symbol) : Prop := Nonempty (KarpReduction source target)

namespace KarpReduction

variable {A B C : Language Symbol}

/-- Reduce a problem to itself by keeping its input unchanged. -/
noncomputable def refl (A : Language Symbol) : KarpReduction A A where
  transform := id
  computer := TMQuery.PolyTimeComputable.id
  correct _ := Iff.rfl

/-- Chain two conversions: first convert an `A` input to a `B` input, then convert that to a
`C` input. The result preserves the answer and still has a polynomial time bound. -/
noncomputable def trans (first : KarpReduction A B) (second : KarpReduction B C) :
    KarpReduction A C where
  transform := second.transform ∘ first.transform
  computer := first.computer.comp second.computer
  correct input := (first.correct input).trans (second.correct (first.transform input))

/-- Reverse yes and no for both problems. The same input conversion still preserves answers. -/
def complement (reduction : KarpReduction A B) :
    KarpReduction (fun input => ¬ A input) (fun input => ¬ B input) where
  transform := reduction.transform
  computer := reduction.computer
  correct input := not_congr (reduction.correct input)

/-- If a machine can answer `B` within a polynomial time bound, a Karp reduction from `A` to `B`
gives such a machine for `A`: convert the input, then run the machine for `B`.
Here `P A` means that `A` has a machine answering every input within a polynomial time bound. -/
theorem preservesP (reduction : KarpReduction A B) (target : P B) : P A := by
  obtain ⟨f, yes, ⟨machine⟩, h⟩ := target
  exact ⟨f ∘ reduction.transform, yes, ⟨reduction.computer.comp machine⟩,
    fun input => (h (reduction.transform input)).trans (reduction.correct input).symm⟩

end KarpReduction

/-- Every problem has a Karp reduction to itself. -/
theorem KarpReducible.refl (A : Language Symbol) : KarpReducible A A := ⟨KarpReduction.refl A⟩

/-- A Karp reduction from `A` to `B` followed by one from `B` to `C` gives one from `A` to `C`. -/
theorem KarpReducible.trans {A B C : Language Symbol}
    (first : KarpReducible A B) (second : KarpReducible B C) : KarpReducible A C := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨first.trans second⟩

end Algolean.Algorithms
