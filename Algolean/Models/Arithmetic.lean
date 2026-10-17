/-
Copyright (c) 2026 Johannes Tantow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Tantow
-/
module

public import Algolean.QueryModel

/-!
# Query type for multiplications

In this module we define a query and model for arithmetic algorithms.
The only allowed operation are multiplications of two numbers that are
smaller than some limit, which could be the maximum representable as word.
These operations are counted as constant time operations.
-/

@[expose] public section

namespace Algolean.Algorithms

open Prog

/--
A query type that allows to multiply two numbers x and y if they are smaller than some bound lime.
-/
inductive mulQuery (lim : ℕ) : Type → Type
| mul (x y : ℕ) (h₁ : x < lim) (h₂ : y < lim) : mulQuery lim ℕ

/--
A model that counts multiplication of bounded length numbers.
-/
@[simps]
def mulModel (lim : ℕ) : Model (mulQuery lim) ℕ where
  evalQuery
  | .mul x y _ _ => x * y
  cost _ := 1

end Algolean.Algorithms
