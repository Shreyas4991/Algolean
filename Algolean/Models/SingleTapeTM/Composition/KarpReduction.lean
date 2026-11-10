/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.MachineComposition
public import Algolean.Problems.Encoding

/-!
# Solving one problem by converting its input

This file describes Karp reductions. A reduction converts an input for one yes/no problem into
an input for another problem with the same answer. A fixed tape program must perform the
conversion in time bounded by a polynomial in the input length.

A solver for the second problem then gives a solver for the first: convert the input and run the
solver once. The source and target may use different alphabets. Fixed injective symbol maps
represent both on the shared tape alphabet. Words outside the source representation must also
give no answers
when converted. Keeping the symbol maps as identities recovers reductions over one alphabet.
The embeddings into the finite tape alphabet imply that the source and target alphabets are
finite too. No numeric coding of their symbols is required.

The quantitative results bound execution by the stored polynomial `p`, output length by
`1 + n + p(n)`, and a subsequent computation with polynomial `q` by
`p(n) + q(1 + n + p(n))`. All these bounds use the shared tape alphabet. `preservesP_onTape`
applies to the represented languages; `preservesP` retains the usual same-alphabet statement.

The conversion preserves both yes and no answers. For example, flipping every bit
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

variable {Input Output Middle Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

open Problems

/--
A Karp reduction converts inputs for the source problem into inputs for the target problem,
preserving yes and no answers. One fixed program performs the conversion with a polynomial time
bound. The symbol maps identify the input and output languages on the same fixed tape alphabet.
The program also preserves answers on words outside either symbol image. Identity symbol maps
are the defaults when both languages already use the tape alphabet.
-/
structure KarpReduction (source : Language Input) (target : Language Output)
    (inputSymbol : Input ↪ Symbol := by exact Function.Embedding.refl _)
    (outputSymbol : Output ↪ Symbol := by exact Function.Embedding.refl _) where
  /-- This function specifies the input that the conversion program must produce. -/
  transform : List Symbol → List Symbol
  /-- This program produces the specified converted input with a polynomial time bound. -/
  computer : TMQuery.PolyTimeComputable transform
  /-- The conversion preserves membership of the two languages represented on the shared tape. -/
  correct : ∀ input, input ∈ symbolLanguage inputSymbol source ↔
    transform input ∈ symbolLanguage outputSymbol target

/-- A [KarpReduction](##Algolean.Algorithms.KarpReduction) exists between the two problems. -/
def KarpReducible (source : Language Input) (target : Language Output)
    (inputSymbol : Input ↪ Symbol := by exact Function.Embedding.refl _)
    (outputSymbol : Output ↪ Symbol := by exact Function.Embedding.refl _) : Prop :=
  Nonempty (KarpReduction source target inputSymbol outputSymbol)

namespace KarpReduction

variable {A : Language Input} {B : Language Middle} {C : Language Output}
variable {inputSymbol : Input ↪ Symbol} {middleSymbol : Middle ↪ Symbol}
variable {outputSymbol : Output ↪ Symbol}

/-- Every problem reduces to itself by leaving its input unchanged. -/
noncomputable def refl (A : Language Input)
    (symbols : Input ↪ Symbol := by exact Function.Embedding.refl _) :
    KarpReduction A A symbols symbols where
  transform := id
  computer := TMQuery.PolyTimeComputable.id
  correct _ := Iff.rfl

/--
The first conversion is followed by the second conversion. Their composition preserves answers
and has a polynomial time bound.
-/
noncomputable def trans (first : KarpReduction A B inputSymbol middleSymbol)
    (second : KarpReduction B C middleSymbol outputSymbol) :
    KarpReduction A C inputSymbol outputSymbol where
  transform := second.transform ∘ first.transform
  computer := first.computer.comp second.computer
  correct input := (first.correct input).trans (second.correct (first.transform input))

/-- On a source word, the reduction preserves its original answer after changing its symbols. -/
theorem correct_input (reduction : KarpReduction A B inputSymbol middleSymbol)
    (input : List Input) :
    input ∈ A ↔ reduction.transform (input.map inputSymbol) ∈ symbolLanguage middleSymbol B := by
  simpa using reduction.correct (input.map inputSymbol)

/--
The same program reverses the answers of both represented languages on the shared tape alphabet.
The complements include words outside the original symbol images.
-/
def complementOnTape (reduction : KarpReduction A B inputSymbol middleSymbol) :
    KarpReduction (symbolLanguage inputSymbol A)ᶜ (symbolLanguage middleSymbol B)ᶜ where
  transform := reduction.transform
  computer := reduction.computer
  correct input := by simpa using not_congr (reduction.correct input)

/-- A reduction over one alphabet also reduces the complements of its two languages. -/
def complement {source target : Language Symbol} (reduction : KarpReduction source target) :
    KarpReduction sourceᶜ targetᶜ where
  transform := reduction.transform
  computer := reduction.computer
  correct input := by simpa using not_congr (reduction.correct input)

/-- The source alphabet is finite because it embeds into the finite tape alphabet. -/
theorem finite_input (_reduction : KarpReduction A B inputSymbol middleSymbol) : Finite Input :=
  Finite.of_injective inputSymbol inputSymbol.injective

/-- The target alphabet is finite because it embeds into the finite tape alphabet. -/
theorem finite_output (_reduction : KarpReduction A B inputSymbol middleSymbol) : Finite Middle :=
  Finite.of_injective middleSymbol middleSymbol.injective

/--
The reduction's fixed program finishes on every shared tape word within its stored polynomial
bound. The existence of sufficient interpreter fuel is part of `OutputsWithinTime`.
-/
theorem time_bound (reduction : KarpReduction A B inputSymbol middleSymbol)
    (input : List Symbol) :
    let computer := reduction.computer
    let := computer.symbolDecidableEq
    let := computer.stateDecidableEq
    TMQuery.OutputsWithinTime computer.program input (reduction.transform input)
      (computer.poly.eval input.length) := by
  let := reduction.computer.symbolDecidableEq
  let := reduction.computer.stateDecidableEq
  exact (reduction.computer.outputsFunInTime input).mono (reduction.computer.bounds input.length)

/--
A reduction cannot write an arbitrarily long target word for free. Its output length is at most
one plus the input length plus its polynomial move bound. The extra cell permits writing on an
empty tape without moving the head.
-/
theorem output_length_le (reduction : KarpReduction A B inputSymbol middleSymbol)
    (input : List Symbol) :
    (reduction.transform input).length ≤
      1 + input.length + reduction.computer.poly.eval input.length := by
  let := reduction.computer.symbolDecidableEq
  let := reduction.computer.stateDecidableEq
  exact (reduction.time_bound input).output_length_le

/--
Running a polynomial-time computation after the reduction still gives a polynomial-time
computation on the shared tape alphabet. This concerns arbitrary word-valued functions, as well
as language deciders.
-/
theorem preservesPolyTimeComputable (reduction : KarpReduction A B inputSymbol middleSymbol)
    {f : List Symbol → List Symbol} (h : Nonempty (TMQuery.PolyTimeComputable f)) :
    Nonempty (TMQuery.PolyTimeComputable (f ∘ reduction.transform)) := by
  obtain ⟨computer⟩ := h
  exact ⟨reduction.computer.comp computer⟩

/--
If the reduction has polynomial bound `p` and a subsequent computation has bound `q`, their
combined program finishes within `p(n) + q(1 + n + p(n))` moves. The argument to `q` accounts for
the reduction's output length. The two programs use the same fixed tape alphabet.
-/
theorem composition_time_bound (reduction : KarpReduction A B inputSymbol middleSymbol)
    {f : List Symbol → List Symbol} (target : TMQuery.PolyTimeComputable f)
    (input : List Symbol) :
    let p := reduction.computer.poly
    let q := target.poly
    let combined := reduction.computer.comp target
    let := combined.symbolDecidableEq
    let := combined.stateDecidableEq
    TMQuery.OutputsWithinTime combined.program input (f (reduction.transform input))
      ((p + q.comp (1 + Polynomial.X + p)).eval input.length) := by
  let combined := reduction.computer.comp target
  let := combined.symbolDecidableEq
  let := combined.stateDecidableEq
  exact (combined.outputsFunInTime input).mono (combined.bounds input.length)

/--
If the represented target language belongs to `P` on the shared alphabet, the represented source
language does too. Its solver converts the input and then runs the target solver. With identity
symbol maps this is the usual preservation theorem for languages over the same alphabet.
-/
theorem preservesP_onTape [Nontrivial Symbol]
    (reduction : KarpReduction A B inputSymbol middleSymbol)
    (target : symbolLanguage middleSymbol B ∈ P) : symbolLanguage inputSymbol A ∈ P := by
  obtain ⟨f, yes, ⟨machine⟩, h⟩ := target
  exact ⟨f ∘ reduction.transform, yes, ⟨reduction.computer.comp machine⟩,
    fun input => (h (reduction.transform input)).trans (reduction.correct input).symm⟩

/--
For languages over the same alphabet, a polynomial-time target solver gives a polynomial-time
source solver. This statement concerns the original languages without changing their alphabets.
-/
theorem preservesP [Nontrivial Symbol] {source target : Language Symbol}
    (reduction : KarpReduction source target) (h : target ∈ P) : source ∈ P := by
  simpa using reduction.preservesP_onTape (by simpa using h)

end KarpReduction

/-- Every problem has a Karp reduction to itself. -/
theorem KarpReducible.refl (A : Language Input)
    (symbols : Input ↪ Symbol := by exact Function.Embedding.refl _) :
    KarpReducible A A symbols symbols := ⟨KarpReduction.refl A symbols⟩

/--
If the first problem reduces to the second and the second reduces to the third, then the first
reduces to the third.
-/
theorem KarpReducible.trans {A : Language Input} {B : Language Middle} {C : Language Output}
    {inputSymbol : Input ↪ Symbol} {middleSymbol : Middle ↪ Symbol}
    {outputSymbol : Output ↪ Symbol}
    (first : KarpReducible A B inputSymbol middleSymbol)
    (second : KarpReducible B C middleSymbol outputSymbol) :
    KarpReducible A C inputSymbol outputSymbol := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  exact ⟨first.trans second⟩

end Algolean.Algorithms
