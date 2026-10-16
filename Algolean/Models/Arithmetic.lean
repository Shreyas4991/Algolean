/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Algolean.QueryModel

/-!
# Query type for multiplications

In this module we define queries and models for arithmetic operations. We consider two kinds
of queries and associated models. In the first one (`unitArithmeticQuery`) we can add and multiply
arbitrary natural numbers in constant time as in the arithmetic model of computation. The other
(`boundedArithmeticQuery`) only allows to add or multiply numbers that are bounded by some natural
as the maximum value of a word.
-/

@[expose] public section

namespace Algolean.Algorithms

open Prog

/--
A query type for adding or multiplying arbitray natural numbers
-/
inductive unitArithmeticQuery : Type → Type
| add (x y : ℕ) : unitArithmeticQuery ℕ
| mul (x y : ℕ) : unitArithmeticQuery ℕ

/--
A model that adds and multiplies arbitray natural numbers for a constant cost.
-/
@[simps]
def unitArithmeticModel : Model (unitArithmeticQuery) ℕ where
  evalQuery
  | .add x y => x + y
  | .mul x y => x * y
  cost _ := 1

/--
A query type that allows to add and multiply two natural numbers that both smaller than some limit.
-/
inductive boundedArithmeticQuery (lim : ℕ) : Type → Type
| add (x y : ℕ) (h₁ : x < lim) (h₂ : y < lim) : boundedArithmeticQuery lim ℕ
| mul (x y : ℕ) (h₁ : x < lim) (h₂ : y < lim) : boundedArithmeticQuery lim ℕ

/--
A model that adds and multiplies natural numbers that are bounded by lim for a constant cost.
-/
@[simps]
def boundedArithmeticModel (lim : ℕ) : Model (boundedArithmeticQuery lim) ℕ where
  evalQuery
  | .mul x y _ _ => x * y
  | .add x y _ _ => x + y
  cost _ := 1

end Algolean.Algorithms
