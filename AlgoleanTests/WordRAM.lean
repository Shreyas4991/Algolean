/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM

/-!
# Strict WordRAM execution

Check register aliasing, modular arithmetic, state-dependent footprints, structured control,
fuel exhaustion, and composition of exact completion proofs. Runtime data stays in the machine.
-/

@[expose] public section

namespace AlgoleanTests.WordRAM

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM Cslib

abbrev r0 : Register 4 := 0
abbrev r1 : Register 4 := 1
abbrev r2 : Register 4 := 2
abbrev r3 : Register 4 := 3

def overflow : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 7
  set (w := 8) r1 255
  copy (w := 8) r2 r1
  set (w := 8) r3 1
  binop (w := 8) .add r1 r1 r3
  store (w := 8) r0 r1

example : (execute 6 overflow RAMState.zero).map (fun r =>
    (r.snd.machine.Memory 7, r.snd.machine.Registers r2, r.fst.tell, r.snd.fuel)) =
      some (0, 255, ⟨6, {7}⟩, 0) := by decide

example : execute 5 overflow RAMState.zero = none := rfl

def byteBinop (op : BinOp) (x y : Word 8) : Option (Word 8) :=
  (execute 1 (FreeM.lift (.binop op r0 r0 r1))
    ⟨Memory.zero, fun r => if r = r0 then x else y, fun _ => false⟩).map
      (fun r => r.snd.machine.Registers r0)

example : byteBinop .sub 0 1 = some 255 := by decide
example : byteBinop .band 170 204 = some 136 := by decide
example : byteBinop .bor 170 204 = some 238 := by decide
example : byteBinop .bxor 170 204 = some 102 := by decide
example : byteBinop .shl 129 1 = some 2 := by decide
example : byteBinop .shr 128 1 = some 64 := by decide
example : byteBinop .shl 255 8 = some 0 := by decide
example : byteBinop .shr 255 255 = some 0 := by decide

example : (execute 1 (FreeM.lift (.bnot r0 r0))
    (⟨Memory.zero, fun _ => 170, fun _ => true⟩ : RAMState 8 4)).map
      (fun r => (r.snd.machine.Registers r0, r.snd.machine.Flags .eq, r.fst.tell)) =
        some (85, true, ⟨1, ∅⟩) := by decide

def pointerState (ptr : Word 8) : RAMState 8 4 :=
  ⟨fun addr => if addr = 0 then ptr else 42, fun _ => 0, fun _ => false⟩

def followPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  load (w := 8) r1 r0

-- The first load overwrites its own address register; its footprint uses the old address.
example : (execute 2 followPointer (pointerState 9)).map (fun r =>
    (r.snd.machine.Registers r1, r.fst.tell)) = some (42, ⟨2, {0, 9}⟩) := by decide

example : (execute 4 (do followPointer; followPointer) (pointerState 0)).map
    (fun r => r.fst.tell) = some ⟨4, {0}⟩ := by decide

example : (execute 2 followPointer (pointerState 9)).map (fun r =>
    (r.fst.tell.auxiliarySpace {0}, r.fst.tell.totalSpace {0, 1})) = some (1, 3) := by decide

example : (execute 2 (do load (w := 8) r0 r0; store (w := 8) r0 r0; pure ())
    (pointerState 9)).map (fun r => (r.snd.machine.Memory 9, r.fst.tell.addresses)) =
      some (9, {0, 9}) := by decide

def initial (x y : Word 8) : RAMState 8 4 :=
  ⟨Memory.zero, fun r => if r = r0 then x else if r = r1 then y else 9, fun _ => false⟩

def choose : Prog (WordRAM 8 4) Unit :=
  Prog.ifThenElse (test .ult r0 r1)
    (do set (w := 8) r2 42; store (w := 8) r3 r2)
    (do set (w := 8) r2 99)

example : (execute 4 choose (initial 3 7)).map (fun r =>
    (r.snd.machine.Memory 9, r.fst.tell, r.snd.machine.Flags .ult)) =
      some (42, ⟨3, {9}⟩, true) := by decide

example : (execute 3 choose (initial 7 3)).map (fun r =>
    (r.snd.machine.Registers r2, r.fst.tell)) = some (99, ⟨2, ∅⟩) := by decide

-- Comparing and clearing one flag retains the other flag.
example : (execute 3 (do
    cmp (w := 8) .eq r0 r0
    cmp (w := 8) .ult r0 r1
    clearFlag (w := 8) (k := 4) .ult
    pure ()) (initial 3 7)).map
      (fun r => (r.snd.machine.Flags .eq, r.snd.machine.Flags .ult, r.fst.tell.time)) =
        some (true, false, 3) := by decide

def count : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r2 1
  whileCompare .ult r0 r1 (do binop (w := 8) .add r0 r0 r2)
  store (w := 8) r3 r0

example : execute 12 count (initial 0 3) = none := rfl

example : (execute 13 count (initial 0 3)).map (fun r =>
    (r.snd.machine.Memory 9, r.fst.tell, r.snd.fuel)) = some (3, ⟨9, {9}⟩, 0) := by decide

example : (execute 4 count (initial 3 3)).map (fun r =>
    (r.snd.machine.Memory 9, r.fst.tell.time)) = some (3, 3) := by decide

def stop : Prog (WordRAM 8 4) Unit := whileLoop .ult (FreeM.lift (.clearFlag .ult))

example : (execute 3 stop (RAMState.zero.writeFlag .ult true)).map
    (fun r => (r.fst.tell.time, r.snd.machine.Flags .ult, r.snd.fuel)) = some (1, false, 0) := by
  decide

-- Empty infinite loops must fail for every finite budget, although their RAM time is zero.
example (fuel : Nat) (s : RAMState w k) (h : s.Flags .eq = true) :
    execute fuel (whileLoop .eq (pure ())) s = none := by
  induction fuel with
  | zero => simp
  | succ fuel ih => simpa [execute_while_succ, h] using ih

-- An unselected divergent branch neither executes nor consumes its own fuel.
example : (execute 2 (branch .eq (FreeM.lift (.set r0 42)) (whileLoop .eq (pure ())))
    ((RAMState.zero : RAMState 8 4).writeFlag .eq true)).map
      (fun r => (r.snd.machine.Registers r0, r.fst.tell.time)) = some (42, 1) := by decide

-- Exact completion composes through the shared runner, and accepts runs with spare fuel.
example (s : RAMState w k) :
    Completes (do (nop : WordRAM w k Unit); (nop : WordRAM w k Unit)) s ⟨2, ∅⟩ s := by
  have h : Completes (FreeM.lift (.nop : WordRAM w k Unit)) s ⟨1, ∅⟩ s :=
    ⟨1, by simp⟩
  simpa using h.seq h

example : Completes stop (RAMState.zero.writeFlag .ult true) ⟨1, ∅⟩
    ((RAMState.zero : RAMState 8 4).writeFlag .ult false) := by
  apply Completes.while_stop (t := (RAMState.zero : RAMState 8 4).writeFlag .ult false)
  · exact ⟨1, by simp⟩
  · simp
  · simp

example (s : RAMState w k) :
    Completes (FreeM.lift (.nop : WordRAM w k Unit)) s ⟨1, ∅⟩ s := by
  apply completes_of_execute (fuel := 8) (result := ⟨(), ⟨1, ∅⟩⟩) (final := ⟨s, 7⟩)
  simp

example : (execute 1 (FreeM.lift (.nop : WordRAM 0 0 Unit)) RAMState.zero).map
    (fun r => (r.fst.tell, r.snd.fuel)) = some (⟨1, ∅⟩, 0) := rfl

end AlgoleanTests.WordRAM
