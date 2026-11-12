/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-!
# Notation for Word-RAM programs

Use `open scoped WordRAM Prog` to enable the notation in this file.
Start a program with `do [WordRAM w k]` to specify its word width and register count
once for the whole block.

## Instructions

The names below refer to registers. In `mem[addr]`, the address is held in register `addr`.

- `dst ←ᵣ x + y`: add two registers and store the result in `dst`.
  Subtraction and bitwise operations use the same form.
- `dst ←ᵣ ~~~src`: flip every bit of `src` and store the result in `dst`.
- `dst ←ᵣ src`: copy a register.
- `dst ←ᵣ imm[value]`: set a register to a constant.
- `dst ←ᵣ mem[addr]`: load a memory cell into a register.
- `mem[addr] ←ᵣ src`: store a register in a memory cell.
- `reset op`: set the selected comparison flag to false.
- `nop`: leave the machine state unchanged and charge one time unit.

Write each word operation as a separate instruction. Parenthesize compound Lean
expressions used as register arguments. Assignment has precedence 10.

## Branches and loops

- `ifₚ condition then ... else ...`: run the selected body.
  Use `flag op` to check an existing flag, or `test op x y` to compare two registers.
- `whileₚ op do ...`: repeat while the selected flag is true.
  The body must update the flag if the loop is to stop.
- `whileₚ op x y do ...`: compare registers before each iteration and stop when
  the comparison is false.
- `repeat [n]`: run an indented body `n` times.

Branch and loop bodies return `Unit`. Comparisons cost one time unit; checking an
existing flag costs no time. The notation expands to the definitions in `WordRAM.lean`
and adds no operations of its own.
-/

@[expose] public section

namespace Algolean.Algorithms.Prog

section ControlFlowNotation

/-- Model-controlled `if` inside a `do` block; enable with `open scoped Prog`. -/
scoped syntax "ifₚ " term " then " doSeq ppDedent(ppLine) "else " doSeq : doElem

scoped macro_rules
  | `(doElem| ifₚ $condition then $yes else $no) =>
    `(doElem| Prog.ifThenElse $condition (do $yes) (do $no))

/-- Repeat an indented `Unit` body a fixed number of times; enable with `open scoped Prog`. -/
scoped macro "repeat " "[" count:term "]" ppLine body:doSeq : doElem =>
  `(doElem| Prog.repeatLoop (fun yes _ => yes) (do $body) $count)

end ControlFlowNotation

end Algolean.Algorithms.Prog

namespace Algolean.Algorithms.WordRAM

/-- Compare the contents of two registers for equality. -/
scoped infix:50 " =ᵣ " => WordRAM.test CmpOp.eq

/-- Compare the contents of two registers as unsigned words. -/
scoped infix:50 " <ᵣ " => WordRAM.test CmpOp.ult

/-- Indented looping syntax over an existing machine comparison flag. -/
scoped macro "whileₚ " op:term:max " do " body:doSeq : doElem =>
  `(doElem| WordRAM.whileLoop $op (do $body))

/-- Indented looping syntax that performs a fresh register comparison each time. -/
scoped macro "whileₚ " op:term:max x:term:max y:term:max " do " body:doSeq : doElem =>
  `(doElem| WordRAM.whileCompare $op $x $y (do $body))

/-- Add two source registers into the destination. -/
scoped notation:10 (name := ramAdd) dst:max " ←ᵣ " x:max " + " y:max =>
  WordRAM.binop BinOp.add dst x y

/-- Subtract the second source register from the first into the destination. -/
scoped notation:10 (name := ramSub) dst:max " ←ᵣ " x:max " - " y:max =>
  WordRAM.binop BinOp.sub dst x y

/-- Bitwise AND of two source registers into the destination. -/
scoped notation:10 (name := ramAnd) dst:max " ←ᵣ " x:max " &&& " y:max =>
  WordRAM.binop BinOp.band dst x y

/-- Bitwise OR of two source registers into the destination. -/
scoped notation:10 (name := ramOr) dst:max " ←ᵣ " x:max " ||| " y:max =>
  WordRAM.binop BinOp.bor dst x y

/-- Bitwise XOR of two source registers into the destination. -/
scoped notation:10 (name := ramXor) dst:max " ←ᵣ " x:max " ^^^ " y:max =>
  WordRAM.binop BinOp.bxor dst x y

/-- Shift left by the word held in the second source register. -/
scoped notation:10 (name := ramShl) dst:max " ←ᵣ " x:max " <<< " y:max =>
  WordRAM.binop BinOp.shl dst x y

/-- Shift right by the word held in the second source register. -/
scoped notation:10 (name := ramShr) dst:max " ←ᵣ " x:max " >>> " y:max =>
  WordRAM.binop BinOp.shr dst x y

/-- Complement the source register into the destination. -/
scoped notation:10 (name := ramNot) dst:max " ←ᵣ " "~~~" src:max =>
  WordRAM.bnot dst src

/-- Copy the source register into the destination. -/
scoped notation:10 (name := ramCopy) dst:max " ←ᵣ " src:max =>
  WordRAM.copy dst src

/-- Set the destination register to an immediate word. -/
scoped notation:10 (name := ramSet) dst:max " ←ᵣ " "imm[" value "]" =>
  WordRAM.set dst value

/-- Load memory at the address held in a register into the destination. -/
scoped notation:10 (name := ramLoad) dst:max " ←ᵣ " "mem[" addr "]" =>
  WordRAM.load dst addr

/-- Store a source register at the address held in another register. -/
scoped notation:10 (name := ramStore) "mem[" addr "]" " ←ᵣ " src:max =>
  WordRAM.store addr src

/-- Do nothing for one time unit. -/
scoped notation (name := ramNop) "nop" => WordRAM.nop

/-- Reset the selected comparison flag to false, leaving other flags unchanged. -/
scoped notation (name := ramReset) "reset " op:max => WordRAM.clearFlag op

/-- Fix word width and register count for all instruction notation inside a `do` block. -/
scoped syntax (name := ramBlock) "do " "[" term "]" doSeq : term

open Lean in
private meta partial def annotateInstructions (queryType : Term)
    (stx : Syntax) : MacroM Syntax := do
  -- A nested quotation supplies its own width and register count.
  if stx.isOfKind ``ramBlock then
    return stx
  let stx ← match stx with
    | .node info kind args => do
      let args ← args.mapM (annotateInstructions queryType)
      pure (.node info kind args)
    | other => pure other
  if [``ramAdd, ``ramSub, ``ramAnd, ``ramOr, ``ramXor, ``ramShl, ``ramShr,
      ``ramNop, ``ramNot, ``ramCopy, ``ramSet, ``ramLoad, ``ramStore,
      ``ramReset].contains stx.getKind then
    let instruction : Term := ⟨stx⟩
    return ← `(($instruction : $queryType Unit))
  return stx

macro_rules (kind := ramBlock)
  | `(do [$queryType:term] $body:doSeq) => do
    let body : Lean.TSyntax ``Lean.Parser.Term.doSeq :=
      ⟨← annotateInstructions queryType body⟩
    `((do $body : Prog $queryType Unit))

end Algolean.Algorithms.WordRAM

