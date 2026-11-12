/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAMSyntax
public import AlgoleanTests.WordRAM

/-!
# WordRAM syntax

Check instruction precedence, query-type propagation, nested control and program blocks,
and instruction pretty-printing. Programs written with notation agree with the execution tests.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMSyntax

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM Cslib
open AlgoleanTests.WordRAM
open scoped Prog WordRAM

-- Each word operation is one instruction, with width and register count fixed by the block.
example (dst x y : Register k) (value : Word w) : (do [WordRAM w k]
    dst ←ᵣ imm[value]
    dst ←ᵣ x
    dst ←ᵣ x + y
    dst ←ᵣ x - y
    dst ←ᵣ x &&& y
    dst ←ᵣ x ||| y
    dst ←ᵣ x ^^^ y
    dst ←ᵣ x <<< y
    dst ←ᵣ x >>> y
    dst ←ᵣ ~~~x
    dst ←ᵣ mem[x]
    mem[x] ←ᵣ dst
    reset .eq
    nop) = (do
      set (w := w) dst value
      copy (w := w) dst x
      binop (w := w) .add dst x y
      binop (w := w) .sub dst x y
      binop (w := w) .band dst x y
      binop (w := w) .bor dst x y
      binop (w := w) .bxor dst x y
      binop (w := w) .shl dst x y
      binop (w := w) .shr dst x y
      bnot (w := w) dst x
      load (w := w) dst x
      store (w := w) x dst
      clearFlag (w := w) (k := k) .eq
      (WordRAM.nop : WordRAM w k Unit)) := rfl

-- Local bindings and parenthesized register expressions retain their ordinary Lean meaning.
example (registers : Register k × Register k) : (do [WordRAM w k]
    let dst := registers.1
    dst ←ᵣ (registers.1) + (registers.2)) =
      (FreeM.lift (.binop .add registers.1 registers.1 registers.2) :
        Prog (WordRAM w k) Unit) := rfl

example (dst x y : Register k) : (do [WordRAM w k]
    ifₚ x =ᵣ y then
      dst ←ᵣ x
    else
      ifₚ x <ᵣ y then
        dst ←ᵣ y
      else
        nop
    reset .eq) = (do
      Prog.ifThenElse (test .eq x y) (FreeM.lift (.copy dst x))
        (Prog.ifThenElse (test .ult x y) (FreeM.lift (.copy dst y)) (FreeM.lift .nop))
      FreeM.lift (.clearFlag .eq)) := rfl

example : (do [WordRAM 8 4]
    ifₚ flag .eq then
      whileₚ .ult do
        reset .ult
    else
      whileₚ .ult r0 r1 do
        r0 ←ᵣ r0 + r2) =
      branch .eq (whileLoop .ult (FreeM.lift (.clearFlag .ult)))
        (whileCompare .ult r0 r1 (FreeM.lift (.binop .add r0 r0 r2))) := rfl

-- A nested block has its own word width and register count.
example : (do [WordRAM 8 4]
    let inner := do [WordRAM 2 1]
      (0 : Register 1) ←ᵣ imm[1]
    let _ := inner
    r0 ←ᵣ imm[7]) = (FreeM.lift (.set r0 7) : Prog (WordRAM 8 4) Unit) := rfl

example (n : Nat) : (do [WordRAM 8 4]
    repeat [n]
      r0 ←ᵣ r0 + r2) =
      Prog.repeatLoop (fun yes _ => yes) (FreeM.lift (.binop .add r0 r0 r2)) n := rfl

-- The notation contributes no extra operations or interpreter steps.
example : (do [WordRAM 8 4]
    r0 ←ᵣ imm[7]
    r1 ←ᵣ imm[255]
    r2 ←ᵣ r1
    r3 ←ᵣ imm[1]
    r1 ←ᵣ r1 + r3
    mem[r0] ←ᵣ r1) = overflow := rfl

example : (do [WordRAM 8 4]
    r2 ←ᵣ imm[1]
    whileₚ .ult r0 r1 do
      r0 ←ᵣ r0 + r2
    mem[r3] ←ᵣ r0) = count := rfl

example : (do [WordRAM 8 4]
    ifₚ r0 <ᵣ r1 then
      r2 ←ᵣ imm[42]
      mem[r3] ←ᵣ r2
    else
      r2 ←ᵣ imm[99]) = choose := rfl

example : (execute 4 (do [WordRAM 8 4]
    r2 ←ᵣ imm[1]
    repeat [3]
      r0 ←ᵣ r0 + r2) RAMState.zero).map
      (fun r => (r.snd.machine.Registers r0, r.fst.tell.time, r.snd.fuel)) =
        some (3, 4, 0) := by decide

/-- info: fun dst x y ↦ dst ←ᵣ x + y : Register 4 → Register 4 → Register 4 → WordRAM 8 4 Unit -/
#guard_msgs in
#check fun (dst x y : Register 4) => WordRAM.binop (w := 8) .add dst x y

/-- info: fun dst x ↦ dst ←ᵣ ~~~x : Register 4 → Register 4 → WordRAM 8 4 Unit -/
#guard_msgs in
#check fun (dst x : Register 4) => WordRAM.bnot (w := 8) dst x

/-- info: fun op ↦ reset op : CmpOp → WordRAM 8 4 Unit -/
#guard_msgs in
#check fun (op : CmpOp) => WordRAM.clearFlag (w := 8) (k := 4) op

end AlgoleanTests.WordRAMSyntax
