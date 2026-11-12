/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Complexity.Reductions.NPtoSAT.InitialSource
public import Algolean.Complexity.Reductions.NPtoSAT.HeadWriting

/-!
# Encoding the initial clauses

* `word` encodes the clauses for one cell of the verifier's initial tape. An input symbol,
  separator, or blank is fixed directly. A certificate cell is linked to the corresponding
  certificate choice by one implication for each possible symbol.
* `word_eq_selected` identifies those clauses from the position selected on the tape.
* `initialClauses_word` joins the initial head clause and the initial cell clauses in order.
-/

open Cslib.Turing.SingleTapeTM

public section

namespace Algolean.Algorithms.NPToSAT.InitialSource

open Cslib Cslib.Turing Problems Problems.SAT Computability SingleTapeTuringMachines
open NPToSAT.Computation NPToSAT.Computation.HeadChoices NPToSAT.Computation.LiteralWriting

variable {Γ : Type} [Fintype Γ] [Encodable Γ]

/-- This encodes the clauses describing one cell of the verifier's initial tape. -/
@[expose] noncomputable def word (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (position : Fin (NPToSAT.Computation.width problem)) : List Γ :=
  (formulaPrefix (CNF.rename
    (show CNF (Variable problem) from match initialSource problem position with
    | .inl symbol => [[.pos (.tape 0 position symbol)]]
    | .inr index => (Finset.univ : Finset Γ).toList.map fun symbol =>
        Clause.implies [.certificate index symbol] (.tape 0 position (some (.inl symbol))))
      Variable.name)).flatMap code

/-- The selected position at time zero gives the stated fixed-symbol or certificate clauses. -/
theorem word_eq_selected (code : CodeSymbol → List Γ) (problem : BoundedVerification Γ)
    (position : Fin (NPToSAT.Computation.width problem)) (choice : ActiveChoices)
    (htime : choice.time.1 = 0) (hposition : choice.firstPosition.1 = position.val) :
    word code problem position =
      match initialSource problem position with
      | .inl symbol => tapeLiteralWord code choice true false false symbol ++
          code (.inr 3) ++ code (.inr 4)
      | .inr index => (Finset.univ : Finset Γ).toList.flatMap fun symbol =>
          (literalPrefix (.neg (Variable.name (.certificate index symbol)))).flatMap code ++
            tapeLiteralWord code choice true false false (some (.inl symbol)) ++
              code (.inr 3) ++ code (.inr 4) := by
  cases hsource : initialSource problem position
  all_goals
    simp [word, hsource, formulaPrefix_rename, literalPrefix, Clause.implies, Clause.forbid,
      Literal.rename, tapeLiteralWord, tapeName, Variable.name, Naming.bits, htime, hposition,
      List.flatMap_append, List.flatMap_map, List.flatMap_assoc, List.append_assoc]

/--
The encoded initial formula is the head clause followed by the cell clauses in position order.
-/
theorem initialClauses_word (code : CodeSymbol → List Γ)
    (problem : BoundedVerification Γ) :
    (formulaPrefix ((initialClauses problem).rename Variable.name)).flatMap code =
      HeadWriting.word code (Encodable.encode (some problem.verifier.initial)) problem.time ++
        (List.finRange (NPToSAT.Computation.width problem)).flatMap (word code problem) := by
  simp only [initialClauses_eq, CNF.rename, List.map_append, formulaPrefix_append,
    List.flatMap_append]
  congr 1
  · simp [formulaPrefix, certificateEncoding_encode_eq_flatMap, literalPrefix, Clause.rename,
      Literal.rename, HeadWriting.word, Variable.name, unaryNumberBits, BooleanTapeEncoding.pair,
      List.flatMap_append, List.flatMap_map, List.flatMap_replicate, List.append_assoc]
  · simp only [formulaPrefix, List.map_flatMap, List.flatMap_assoc, List.flatMap_append]
    congr 1
    funext position
    simp [word, formulaPrefix, CNF.rename, List.flatMap_assoc]
    rfl

end Algolean.Algorithms.NPToSAT.InitialSource
