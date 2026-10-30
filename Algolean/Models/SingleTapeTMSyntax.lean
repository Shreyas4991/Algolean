/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM

/-!
# Notation for single-tape TM programs

Enable with `open scoped TMQuery`. A `do [TMQuery tm]` block fixes the machine for its instructions.

* `tape ←ₜ symbol` writes a fixed `Option Symbol`, with `none` representing blank.
* `state ←ₜ label` updates the control state.
* `moveₜ direction` moves left, right, or stays in place.
* `tape =ₜ symbol` and `state =ₜ label` are machine conditions; `notₜ` negates one.
* `ifₜ condition then ... else ...` and `whileₜ condition do ...` select and repeat fixed bodies.

Conditions remain syntax, and every instruction returns `Unit`. The notation adds no queries.
Instruction notation and control-flow unexpanders also display programs in this syntax.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

/-- Write the symbol under the tape head. -/
scoped notation:10 (name := tmWrite) "tape" " ←ₜ " symbol => TMQuery.write symbol

/-- Set the control-state label. -/
scoped notation:10 (name := tmUpdate) "state" " ←ₜ " label => TMQuery.update label

/-- Move the tape head in a fixed direction. -/
scoped notation (name := tmMove) "moveₜ " direction:max => TMQuery.move direction

/-- Test the head symbol without returning it to Lean. -/
scoped notation:50 "tape" " =ₜ " symbol => TMCondition.tapeIs symbol

/-- Test an optional control-state label without returning it to Lean. -/
scoped notation:50 "state" " =ₜ " label => TMCondition.stateIs label

/-- Negate a machine condition. -/
scoped prefix:40 "notₜ " => TMCondition.not

/-- A machine-controlled branch with indented program bodies. -/
scoped syntax "ifₜ " term " then " doSeq ppDedent(ppLine) "else " doSeq : doElem

scoped macro_rules
  | `(doElem| ifₜ $condition then $yes else $no) =>
    `(doElem| TMQuery.branch $condition (do $yes) (do $no))

/-- A machine-controlled loop with an indented program body. -/
scoped macro "whileₜ " condition:term:max " do " body:doSeq : doElem =>
  `(doElem| TMQuery.whileLoop $condition (do $body))

/-- Specify the query type once for every instruction in a program block. -/
scoped syntax (name := tmBlock) "do " "[" term "]" doSeq : term

open Lean in
private meta partial def annotateInstructions (queryType : Term)
    (stx : Syntax) : MacroM Syntax := do
  if stx.isOfKind ``tmBlock then
    return stx
  let stx ← match stx with
    | .node info kind args => do
      let args ← args.mapM (annotateInstructions queryType)
      pure (.node info kind args)
    | other => pure other
  if [``tmWrite, ``tmUpdate, ``tmMove].contains stx.getKind then
    let instruction : Term := ⟨stx⟩
    return ← `(($instruction : $queryType Unit))
  return stx

macro_rules (kind := tmBlock)
  | `(do [$queryType:term] $body:doSeq) => do
    let body : Lean.TSyntax ``Lean.Parser.Term.doSeq := ⟨← annotateInstructions queryType body⟩
    `((do $body : Prog $queryType Unit))

open Lean PrettyPrinter

private meta def unexpandBody (body : Term) : UnexpandM (TSyntax ``Lean.Parser.Term.doSeq) :=
  match body with
  | `(do $body) => pure body
  | _ => `(doSeq| $body:term)

/-- Display a machine branch using its indented notation. -/
@[scoped app_unexpander TMQuery.branch]
meta def unexpandBranch : Unexpander
  | `($_ $condition $yes $no) => do
    let yes ← unexpandBody yes
    let no ← unexpandBody no
    `(do ifₜ $condition then $yes else $no)
  | _ => throw ()

/-- Display a machine loop using its indented notation. -/
@[scoped app_unexpander TMQuery.whileLoop]
meta def unexpandWhile : Unexpander
  | `($_ $condition $body) => do
    let body ← unexpandBody body
    `(do whileₜ $condition do $body)
  | _ => throw ()

end Algolean.Algorithms.TMQuery
