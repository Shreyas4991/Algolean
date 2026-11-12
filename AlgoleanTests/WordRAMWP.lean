/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM.Verification
public import Algolean.Models.WordRAMSyntax

/-!
# Cost-aware WordRAM verification

The failure postcondition is false throughout: verified programs must finish within their fuel
budget. Initial costs and state-dependent memory footprints are retained by the shared handler.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMWP

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM Cslib Cslib.FreeM Std.WP Lean.Order
open scoped WordRAM Prog WordRAM.Spec

set_option experimental.vcgen true

abbrev r0 : Register 2 := 0
abbrev r1 : Register 2 := 1

def followPointer : Prog (WordRAM 8 2) Unit := do [WordRAM 8 2]
  r0 ←ᵣ mem[r0]
  r1 ←ᵣ mem[r0]

example (s : RAMState 8 2) (initial : RAMCost 8) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 2⟩ ⦄ followPointer
      ⦃ fun _ cost final =>
        cost = initial + ⟨2, {s.Registers r0, s.Memory (s.Registers r0)}⟩ ∧
        final.machine.Registers r1 = s.Memory (s.Memory (s.Registers r0)) ∧ final.fuel = fuel;
        fun _ => False ⦄ := by
  vcgen [followPointer]
  all_goals simp_all [add_assoc]

def choose : Prog (WordRAM 8 2) Unit := do [WordRAM 8 2]
  ifₚ r0 <ᵣ r1 then
    r0 ←ᵣ mem[r0]
  else
    nop

example (s : RAMState 8 2) (initial : RAMCost 8) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 3⟩ ⦄ choose
      ⦃ fun _ cost final =>
        cost = initial + ⟨2, if CmpOp.eval .ult (s.Registers r0) (s.Registers r1)
          then {s.Registers r0} else ∅⟩ ∧
        final.machine.Registers r0 =
          (if CmpOp.eval .ult (s.Registers r0) (s.Registers r1)
            then s.Memory (s.Registers r0) else s.Registers r0) ∧ final.fuel = fuel;
        fun _ => False ⦄ := by
  vcgen [choose, Prog.ifThenElse, test]
  all_goals simp_all only [lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true,
    ↓binderNameHint.eq_1, Fin.isValue, step, Nat.add_one_sub_one, true_and]
  vcgen
  split
  all_goals simp_all [add_assoc]

def stop : Prog (WordRAM 8 2) Unit := do [WordRAM 8 2]
  whileₚ .ult do
    reset .ult

theorem stop_spec (s : RAMState 8 2) (hflag : s.Flags .ult = true)
    (initial : RAMCost 8) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 3⟩ ⦄ stop
      ⦃ fun _ cost final => cost = initial + ⟨1, ∅⟩ ∧
        final.machine = s.writeFlag .ult false ∧ final.fuel = fuel; fun _ => False ⦄ := by
  vcgen [stop] invariants
  · fun cost current =>
      (cost = initial ∧ current = ⟨s, fuel + 3⟩) ∨
      (cost = initial + ⟨1, ∅⟩ ∧ current = ⟨s.writeFlag .ult false, fuel + 1⟩)
  all_goals (try simp_all)
  all_goals grind

-- The soundness bridge preserves the supplied fuel budget and rules out exhaustion.
example (s : RAMState 8 2) (hflag : s.Flags .ult = true) (fuel : Nat) :
    ∃ result final, execute (fuel + 3) stop s = some (result, final) ∧ final.fuel = fuel := by
  obtain ⟨result, final, hr, _, _, hf⟩ :=
    WordRAM.Spec.execute (stop_spec s hflag 0 fuel)
      (initial := 0) (s := s) (fuel := fuel + 3) ⟨rfl, rfl⟩
  exact ⟨result, final, hr, hf⟩

example (s : RAMState 8 2) (hflag : s.Flags .ult = true) (fuel : Nat) :
    ∃ (cost : RAMCost 8) (final : ExecutionState 8 2),
      Completes stop s cost final.machine ∧ cost = ⟨1, ∅⟩ ∧
      final.machine = s.writeFlag .ult false ∧ final.fuel = fuel := by
  simpa only [zero_add] using WordRAM.Spec.completes (stop_spec s hflag 0 fuel)
    (initial := 0) (s := s) (fuel := fuel + 3) ⟨rfl, rfl⟩

-- Even a no-op cannot be verified as completing with zero fuel.
example (post : Unit → RAMCost 8 → ExecutionState 8 2 → Prop) :
    ¬Triple (FreeM.lift (.nop : WordRAM 8 2 Unit))
      (fun cost current => cost = 0 ∧ current = ⟨RAMState.zero, 0⟩) post (fun _ => False) := by
  intro h
  obtain ⟨result, final, hr, _⟩ := WordRAM.Spec.execute h
    (initial := 0) (s := RAMState.zero) (fuel := 0) ⟨rfl, rfl⟩
  simp at hr

def invertCell : Prog (WordRAM 8 2) Unit := do [WordRAM 8 2]
  r1 ←ᵣ mem[r0]
  r1 ←ᵣ ~~~r1
  mem[r0] ←ᵣ r1

example (s : RAMState 8 2) (initial : RAMCost 8) (fuel : Nat) :
    ⦃ fun cost current => cost = initial ∧ current = ⟨s, fuel + 3⟩ ⦄ invertCell
      ⦃ fun _ cost final => cost = initial + ⟨3, {s.Registers r0}⟩ ∧
        final.machine.Memory =
          Function.update s.Memory (s.Registers r0) (~~~s.Memory (s.Registers r0)) ∧
        final.fuel = fuel; fun _ => False ⦄ := by
  vcgen [invertCell]
  all_goals simp_all [add_assoc]

section Evaluation

local instance : HasHandler (WordRAM 8 2) (ExecutionState 8 2 → Prop) (Unit → Prop) :=
  timeAndSpaceCost.hasHandler

example (s : RAMState 8 2) (fuel : Nat) :
    ⦃ fun current => current = ⟨s, fuel + 1⟩ ⦄ (FreeM.lift (.nop : WordRAM 8 2 Unit))
      ⦃ fun _ current => current = ⟨s, fuel⟩; fun _ => False ⦄ := by
  vcgen
  rename_i current hp
  subst current
  change wp (timeAndSpaceCost.evalQuery (.nop : WordRAM 8 2 Unit)) _ _ ⟨s, fuel + 1⟩
  cases fuel <;> rfl

example (p : Prog (WordRAM 8 2) α) (post : α → ExecutionState 8 2 → Prop)
    (epost : Unit → Prop) :
    (wpH timeAndSpaceCost.handler p).apply post epost ⊑
      wp (p.evalStateM timeAndSpaceCost) post epost :=
  timeAndSpaceCost.wp_le_wp_evalStateM p post epost

end Evaluation

end AlgoleanTests.WordRAMWP
