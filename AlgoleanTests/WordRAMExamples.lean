/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.WordRAM.LinearSearch

/-! # Register operations, structured control, and uniform linear search -/

@[expose] public section

namespace AlgoleanTests.WordRAMExamples

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM
open scoped Prog WordRAM

abbrev r0 : Register 4 := 0
abbrev r1 : Register 4 := 1
abbrev r2 : Register 4 := 2
abbrev r3 : Register 4 := 3

def increment (w : Nat) : Prog (WordRAM w 4) Unit := do
  load (w := w) r1 r0
  binop (w := w) .add r1 r1 r3
  store (w := w) r0 r1

def overflow : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 7
  set (w := 8) r1 255
  set (w := 8) r3 1
  store (w := 8) r0 r1
  increment 8

example : (execute 7 overflow RAMState.zero).map (fun r =>
    (r.snd.ram.Memory 7, r.snd.ram.Registers r1, r.fst.tell.time, r.fst.tell.addresses)) =
      some (0, 0, 7, {7}) := by decide

example : execute 6 overflow RAMState.zero = none := rfl

def copyExample : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 42
  copy (w := 8) r1 r0
  set (w := 8) r0 7

example : (execute 3 copyExample RAMState.zero).map
    (fun r => (r.snd.ram.Registers r1, r.fst.tell.time)) = some (42, 3) := by decide

def followPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  load (w := 8) r1 r0

def pointerState (ptr : Word 8) : RAMState 8 4 :=
  ⟨fun addr => if addr = 0 then ptr else 42, fun _ => 0, fun _ => false⟩

example : (execute 2 followPointer (pointerState 9)).map (fun r =>
    (r.snd.ram.Registers r1, r.fst.tell.time, r.fst.tell.addresses, r.fst.tell.space)) =
      some (42, 2, {0, 9}, 2) := by decide

example : (execute 2 followPointer (pointerState 0)).map
    (fun r => r.fst.tell.addresses) = some {0} := by decide

example : (execute 4 (followPointer *> followPointer) (pointerState 0)).map
    (fun r => r.fst.tell) = some ⟨4, {0}⟩ := by decide

example : (execute 2 followPointer (pointerState 9)).map (fun r =>
    (r.fst.tell.auxiliarySpace {0}, r.fst.tell.totalSpace {0, 1})) = some (1, 3) := by decide

def storeThroughPointer : Prog (WordRAM 8 4) Unit := do
  load (w := 8) r0 r0
  store (w := 8) r0 r0

example : (execute 2 storeThroughPointer (pointerState 9)).map
    (fun r => (r.snd.ram.Memory 9, r.fst.tell.addresses)) = some (9, {0, 9}) := by decide

def byteBinop (op : BinOp) (x y : Word 8) : Option (Word 8) :=
  (execute 1 (do binop (w := 8) op r2 r0 r1 : Prog (WordRAM 8 4) Unit)
    ⟨fun _ => 0, fun r => if r = r0 then x else y, fun _ => false⟩).map
      (fun r => r.snd.ram.Registers r2)

example : byteBinop .sub 0 1 = some 255 := by decide

example : byteBinop .band 170 204 = some 136 := by decide

example : byteBinop .bor 170 204 = some 238 := by decide

example : byteBinop .bxor 170 204 = some 102 := by decide

example : byteBinop .shl 129 1 = some 2 := by decide

example : byteBinop .shr 128 1 = some 64 := by decide

example : byteBinop .shl 255 8 = some 0 := by decide

example : byteBinop .shr 255 8 = some 0 := by decide

example : byteBinop .shl 255 9 = some 0 := by decide

example : byteBinop .shr 255 255 = some 0 := by decide

def wordOnly : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r0 170
  bnot (w := 8) r1 r0
  cmp (w := 8) .eq r0 r1

example : (execute 3 wordOnly RAMState.zero).map (fun r =>
    (r.snd.ram.Registers r1, r.snd.ram.Flags .eq, r.fst.tell.time, r.fst.tell.space)) =
      some (85, false, 3, 0) := by decide

namespace Branches

def initial (x y : Word 8) : RAMState 8 4 :=
  ⟨fun _ => 0, fun r => if r = r0 then x else if r = r1 then y else if r = r3 then 9 else 0,
    fun _ => false⟩

def choose : Prog (WordRAM 8 4) Unit := do
  ifₚ test .ult r0 r1 then
    set (w := 8) r2 42
    store (w := 8) r3 r2
  else
    set (w := 8) r2 99

example : (execute 4 choose (initial 3 7)).map (fun r =>
    (r.snd.ram.Memory 9, r.fst.tell.time, r.fst.tell.addresses, r.snd.ram.Flags .ult)) =
      some (42, 3, {9}, true) := by decide

example : (execute 3 choose (initial 7 3)).map (fun r =>
    (r.snd.ram.Memory 9, r.snd.ram.Registers r2, r.fst.tell.time, r.fst.tell.addresses)) =
      some (0, 99, 2, ∅) := by decide

def independentFlags : Prog (WordRAM 8 4) Unit := do
  cmp (w := 8) .eq r0 r0
  cmp (w := 8) .ult r0 r1

example : (execute 2 independentFlags (initial 3 7)).map
    (fun r => (r.snd.ram.Flags .eq, r.snd.ram.Flags .ult)) = some (true, true) := by decide

def nested : Prog (WordRAM 8 4) Unit := do
  cmp (w := 8) .ult r0 r1
  branch .ult (do branch .ult (do set (w := 8) r2 42) (pure ())) (pure ())
  store (w := 8) r3 r2

example : execute 4 nested (initial 3 7) = none := rfl

example : (execute 5 nested (initial 3 7)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Memory 9, r.snd.fuel)) = some (3, 42, 0) := by decide

example : (execute 8 nested (initial 3 7)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Memory 9, r.snd.fuel)) = some (3, 42, 3) := by decide

end Branches

namespace Loops

def repeated (fuel : Nat) : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r2 1
  repeat [fuel]
    binop (w := 8) .add r0 r0 r2

example : (execute 4 (repeated 3) RAMState.zero).map
    (fun r => (r.snd.ram.Registers r0, r.fst.tell.time)) = some (3, 4) := by decide

example : (execute 1 (repeated 0) RAMState.zero).map
    (fun r => (r.snd.ram.Registers r0, r.fst.tell.time)) = some (0, 1) := by decide

-- The indented flag loop and comparison loop use the same WordRAM query type as branches.
def count : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r2 1
  whileₚ .ult r0 r1 do
    binop (w := 8) .add r0 r0 r2
  store (w := 8) r3 r0

example : execute 12 count (Branches.initial 0 3) = none := rfl

example : (execute 13 count (Branches.initial 0 3)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Memory 9, r.snd.fuel)) = some (9, 3, 0) := by decide

example : (execute 4 count (Branches.initial 3 3)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Memory 9)) = some (3, 3) := by decide

def flagLoop : Prog (WordRAM 8 4) Unit := do
  whileₚ .ult do
    clearFlag (w := 8) (k := 4) .ult

example : (execute 3 flagLoop (RAMState.zero.writeFlag .ult true)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Flags .ult, r.snd.fuel)) = some (1, false, 0) := by decide

example : (execute 1 flagLoop RAMState.zero).map
    (fun r => r.fst.tell.time) = some 0 := by decide

def forever : Prog (WordRAM 8 4) Unit := do
  cmp (w := 8) .eq r0 r0
  whileₚ .eq do
    pure ()

example (fuel : Nat) (s : RAMState 8 4) : execute fuel forever s = none := by
  have loops : ∀ fuel (s : RAMState 8 4), s.Flags .eq = true →
      runCode fuel [.whileCode .eq []] s = none := by
    intro fuel
    induction fuel with
    | zero => intro s h; rfl
    | succ fuel ih => intro s h; simp [runCode, step, h, ih]
  cases fuel <;> simp [execute_eq_runCode, forever, whileLoop, runCode, step, CmpOp.eval, loops]

def nested : Prog (WordRAM 8 4) Unit := do
  set (w := 8) r2 1
  whileₚ .ult r0 r1 do
    whileₚ .ult r0 r1 do
      binop (w := 8) .add r0 r0 r2
  store (w := 8) r3 r0

example : execute 16 nested (Branches.initial 0 3) = none := rfl

example : (execute 17 nested (Branches.initial 0 3)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Memory 9)) = some (11, 3) := by decide

def skipped : Prog (WordRAM 8 4) Unit := do
  cmp (w := 8) .ult r0 r1
  branch .ult (do set (w := 8) r2 42) forever

example : (execute 3 skipped (Branches.initial 0 3)).map
    (fun r => (r.fst.tell.time, r.snd.ram.Registers r2)) = some (2, 42) := by decide

end Loops

example : execute 0 (pure () : Prog (WordRAM 8 4) Unit) RAMState.zero =
    some (⟨(), 0⟩, ⟨RAMState.zero, 0⟩) := rfl

example : execute 0 (set (w := 8) r0 1 : Prog (WordRAM 8 4) Unit) RAMState.zero = none := rfl

section WeakestPreconditions

open Cslib.FreeM Std.Do

local instance : HasHandler (WordRAM 8 4)
    (.arg (RAMCost 8 4) (.arg (ExecutionState 8 4) (.except PUnit .pure))) :=
  timeAndSpaceCost.hasCostHandler

set_option mvcgen.warning false in
example :
    ⦃fun cost s => ⌜cost = 0 ∧ s = ⟨pointerState 9, 2⟩⌝⦄ followPointer
      ⦃⇓ _ cost s => ⌜cost.time = 2 ∧ cost.addresses = {0, 9} ∧ s.ram.Registers r1 = 42⌝⦄ := by
  mvcgen [followPointer]
  simp_all [HasHandler.handler, ModelStateM.costHandler, timeAndSpaceCost,
    runBlock, runCode, step, pointerState, r0, r1, Finset.pair_comm]

set_option mvcgen.warning false in
example :
    ⦃fun cost s => ⌜cost = 0 ∧ s = ⟨Branches.initial 3 7, 4⟩⌝⦄ Branches.choose
      ⦃⇓ _ cost s => ⌜cost.time = 3 ∧ cost.addresses = {9} ∧ s.ram.Memory 9 = 42⌝⦄ := by
  mvcgen [Branches.choose, Prog.ifThenElse, test, branch]
  simp_all [HasHandler.handler, ModelStateM.costHandler, timeAndSpaceCost,
    runBlock, runCode, step, Branches.initial, CmpOp.eval, r0, r1, r2, r3]

set_option mvcgen.warning false in
example :
    ⦃fun cost s => ⌜cost = 0 ∧ s = ⟨RAMState.zero.writeFlag .ult true, 3⟩⌝⦄ Loops.flagLoop
      ⦃⇓ _ cost s => ⌜cost.time = 1 ∧ s.ram.Flags .ult = false ∧ s.fuel = 0⌝⦄ := by
  mvcgen [Loops.flagLoop, whileLoop]
  simp_all [HasHandler.handler, ModelStateM.costHandler, timeAndSpaceCost,
    runBlock, runCode, step, RAMState.zero]

end WeakestPreconditions

example (p : Prog (WordRAM w k) (List Bool)) (s t : RAMState w k)
    (fuel fuel' : Nat) (result result' : AddWriter (RAMCost w k) (List Bool))
    (final final' : ExecutionState w k)
    (h : execute fuel p s = some (result, final))
    (h' : execute fuel' p t = some (result', final')) : result.ret = result'.ret :=
  execute_ret_independent p s t h h'

section LinearSearch

def searchInput : Array (Word 8) := #[12, 7, 42, 7, 99]

def searchExample : Prog (WordRAM 8 5) Unit := linearSearch 8

example : (execute 50 searchExample (linearSearchState searchInput 7)).map (fun r =>
    (searchOutput LinearSearch.index r.snd.ram, r.fst.tell.time, r.fst.tell.addresses,
      r.fst.tell.auxiliarySpace (inputRegion searchInput))) =
      some (some 1, 10, {0, 1}, 0) := by decide

example : (execute 50 searchExample (linearSearchState searchInput 2)).map (fun r =>
    (searchOutput LinearSearch.index r.snd.ram, r.fst.tell.time, r.fst.tell.totalSpace
      (inputRegion searchInput))) = some (none, 22, 5) := by decide

example : (execute 30 (linearSearch 2) (linearSearchState #[0, 1, 2, 3] 3)).map
    (fun r => (searchOutput LinearSearch.index r.snd.ram, r.fst.tell.time)) =
      some (some 3, 18) := by decide

example : (execute 9 (linearSearch 0) (linearSearchState #[0] 0)).map
    (fun r => (searchOutput LinearSearch.index r.snd.ram, r.fst.tell.time)) =
      some (some 0, 6) := by decide

example : (execute 4 (linearSearch 0)
    ((linearSearchState #[] 0).writeFlag .eq true)).map
      (fun r => (searchOutput LinearSearch.index r.snd.ram, r.fst.tell.time)) =
        some (none, 3) := by decide

def representingState (target junk : Word 8) : RAMState 8 5 :=
  ⟨fun addr => if addr.toNat < searchInput.size then arrayMemory searchInput addr else junk,
    fun r => if r = LinearSearch.key then target
      else if r = LinearSearch.last then 4 else 255, fun _ => true⟩

private theorem representingState_input (target junk : Word 8) :
    RepresentsBoundedSearchInput ⟨searchInput, target⟩ LinearSearch.key LinearSearch.last
      (representingState target junk) := by
  have hfits : searchInput.size ≤ 2 ^ 8 := by decide
  refine ⟨⟨⟨hfits, ?_⟩, by simp [representingState]⟩,
    by simp [representingState, LinearSearch.last, LinearSearch.key, searchInput],
    by simp [representingState, searchInput]⟩
  intro i hi
  have hiw : i < 2 ^ 8 := by have : searchInput.size = 5 := rfl; lia
  simpa only [representingState, wordAddress_toNat i hiw, if_pos hi] using
    arrayMemory_ofNat searchInput (by decide) i hi

example (target junk : Word 8) :
    ∃ fuel cost t, execute fuel searchExample (representingState target junk) =
      some (⟨(), cost⟩, ⟨t, 0⟩) :=
  linearSearch_terminates ⟨searchInput, target⟩ _ (representingState_input target junk)

example (target junk : Word 8) (fuel : Nat) (result : AddWriter (RAMCost 8 5) Unit)
    (final : ExecutionState 8 5)
    (hr : execute fuel searchExample (representingState target junk) = some (result, final)) :
    Search.linearSearch.spec ⟨searchInput, target⟩ (searchOutput LinearSearch.index final.ram) ∧
      result.tell.auxiliarySpace (inputRegion searchInput) = 0 :=
  ⟨linearSearch_correct _ _ (representingState_input target junk) hr,
    linearSearch_auxiliarySpace _ _ (representingState_input target junk) hr⟩

example : (execute 50 searchExample (representingState 7 173)).map
    (fun r => (searchOutput LinearSearch.index r.snd.ram, r.snd.ram.Memory 200)) =
      some (some 1, 173) := by decide

end LinearSearch

end AlgoleanTests.WordRAMExamples
