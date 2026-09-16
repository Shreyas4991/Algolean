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

The examples swap two memory cells and sum the even words in an input array.
-/

@[expose] public section

namespace Algolean.Algorithms.Prog

section ControlFlowNotation

/-- Model-controlled `if` inside a `do` block; enable with `open scoped Prog`. -/
scoped syntax "ifₚ " term " then " doSeq " else " doSeq : doElem

scoped macro_rules
  | `(doElem| ifₚ $condition then $yes else $no) =>
    `(doElem| Prog.ifThenElse $condition (do $yes) (do $no))

/-- Repeat an indented `Unit` body a fixed number of times; enable with `open scoped Prog`. -/
scoped macro "repeat " "[" fuel:term "]" ppLine body:doSeq : doElem =>
  `(doElem| Prog.repeatLoop (fun yes _ => yes) (do $body) $fuel)

end ControlFlowNotation

end Algolean.Algorithms.Prog

namespace Algolean.Algorithms.WordRAM

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
      ``ramNot, ``ramCopy, ``ramSet, ``ramLoad, ``ramStore, ``ramReset].contains stx.getKind then
    let instruction : Term := ⟨stx⟩
    return ← `(($instruction : $queryType Unit))
  return stx

macro_rules (kind := ramBlock)
  | `(do [$queryType:term] $body:doSeq) => do
    let body : Lean.TSyntax ``Lean.Parser.Term.doSeq :=
      ⟨← annotateInstructions queryType body⟩
    `((do $body : Prog $queryType Unit))

section Examples

open scoped WordRAM

example (dst x y : Register k) :
    (dst ←ᵣ x + y : WordRAM w k Unit) = .binop .add dst x y := rfl

example (dst src : Register k) :
    (dst ←ᵣ ~~~src : WordRAM w k Unit) = .bnot dst src := rfl

example (dst addr : Register k) :
    (dst ←ᵣ mem[addr] : WordRAM w k Unit) = .load dst addr := rfl

section SillySwapExample

private abbrev swapAddr : Register 3 := 0

private abbrev swapA : Register 3 := 1

private abbrev swapB : Register 3 := 2

/-- Swap memory cells 0 and 1 using one address register and two value registers.
The three arithmetic operations need no additional temporary register.
For the record this example need not be so complicated. We can swap
with a single register. But then I wouldn't get to test drive the notation
for arithmetic for example -/
private def arithmeticSwap (w : Nat) : Prog (WordRAM w 3) Unit := do [WordRAM w 3]
  swapAddr ←ᵣ imm[0]
  swapA ←ᵣ mem[swapAddr]
  swapAddr ←ᵣ imm[1]
  swapB ←ᵣ mem[swapAddr]
  swapA ←ᵣ swapA + swapB
  swapB ←ᵣ swapA - swapB
  swapA ←ᵣ swapA - swapB
  mem[swapAddr] ←ᵣ swapB
  swapAddr ←ᵣ imm[0]
  mem[swapAddr] ←ᵣ swapA

/-- Input cells contain 250 and 17; all other memory cells contain 99. -/
private def swapInputMemory : Memory 8 :=
  fun addr => if addr = 0 then 250 else if addr = 1 then 17 else 99

/-- Start with the input memory, zeroed registers, and cleared flags. -/
private def swapInitialState : RAMState 8 3 where
  Memory := swapInputMemory
  Registers := fun _ => 0

/-- The two input cells are swapped, with the results also remaining in the value registers. -/
private def swapFinalState : RAMState 8 3 where
  Memory := fun addr => if addr = 0 then 17 else if addr = 1 then 250 else 99
  Registers := fun r => if r = swapAddr then 0 else if r = swapA then 17 else 250

-- The addition wraps around: 250 + 17 = 11 in an eight-bit word.
example : (execute 10 (arithmeticSwap 8) swapInitialState).map
    (fun result => result.snd.ram) = some swapFinalState := by
  apply congrArg some
  apply (RAMState.mk.injEq ..).mpr
  refine ⟨?_, ?_, rfl⟩
  · funext addr
    by_cases h0 : addr = 0#8 <;> by_cases h1 : addr = 1#8 <;>
      simp [step, RAMState.writeRegister, BinOp.eval, swapInitialState,
        swapAddr, swapA, swapB, swapInputMemory, h0, h1]
  · funext r
    fin_cases r <;> decide

-- Ten primitive operations, with no memory probes outside the two input cells.
example : (execute 10 (arithmeticSwap 8) swapInitialState).map
    (fun result => (result.fst.tell.time, result.fst.tell.auxiliarySpace {0, 1})) =
      some (10, 0) := by decide

end SillySwapExample

section EvenSumExample

open scoped Prog

private abbrev evenSum : Register 7 := 0

private abbrev inputIndex : Register 7 := 1

private abbrev inputSize : Register 7 := 2

private abbrev inputValue : Register 7 := 3

private abbrev lowBit : Register 7 := 4

private abbrev zero : Register 7 := 5

private abbrev one : Register 7 := 6

/-- Cell 0 contains `n`; sum the even words in cells 1 through `n`, modulo `2^w`.
Incrementing the index before the load supports `n = 2^w - 1` without wrapping the index.
At width 8, the header and input cells are bytes. -/
private def sumEvenWords (w : Nat) : Prog (WordRAM w 7) Unit := do [WordRAM w 7]
  evenSum ←ᵣ imm[0]
  inputIndex ←ᵣ imm[0]
  inputSize ←ᵣ mem[inputIndex]
  zero ←ᵣ imm[0]
  one ←ᵣ imm[1]
  whileₚ .ult inputIndex inputSize do
    inputIndex ←ᵣ inputIndex + one
    inputValue ←ᵣ mem[inputIndex]
    lowBit ←ᵣ inputValue &&& one
    ifₚ test .eq lowBit zero then
      evenSum ←ᵣ evenSum + inputValue
    else
      pure ()

/-- Five input bytes: the even ones sum to `250 + 8 + 4 = 262`, or 6 modulo 256. -/
private def evenSumInputMemory : Memory 8 :=
  fun addr => #[5, 250, 3, 8, 7, 4][addr.toNat]?.getD 99

private def evenSumInitialState : RAMState 8 7 where
  Memory := evenSumInputMemory
  Registers := fun _ => 0

example : (execute 100 (sumEvenWords 8) evenSumInitialState).map
    (fun result => result.snd.ram.Registers evenSum) = some 6 := by decide

-- The header and input cells are the entire memory footprint.
example : (execute 100 (sumEvenWords 8) evenSumInitialState).map
    (fun result => (result.fst.tell.time, result.fst.tell.auxiliarySpace {0, 1, 2, 3, 4, 5})) =
      some (34, 0) := by decide

-- An empty input clears a stale result and does not read any payload cells.
example :
    let s : RAMState 8 7 :=
      { Memory := fun addr => if addr = 0 then 0 else 42, Registers := fun _ => 255 }
    (execute 7 (sumEvenWords 8) s).map
      (fun result => (result.snd.ram.Registers evenSum, result.fst.tell.addresses)) =
        some (0, {0}) := by decide

-- The header plus three elements fills the entire two-bit address space.
example :
    let s : RAMState 2 7 :=
      { Memory := fun addr => #[3, 2, 1, 2][addr.toNat]?.getD 0, Registers := fun _ => 0 }
    (execute 40 (sumEvenWords 2) s).map
      (fun result => result.snd.ram.Registers evenSum) = some 0 := by decide

end EvenSumExample

end Examples

end Algolean.Algorithms.WordRAM
