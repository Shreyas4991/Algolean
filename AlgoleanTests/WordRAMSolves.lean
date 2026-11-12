/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.WordRAM.Computes
public import Algolean.Models.WordRAMSyntax

/-!
# WordRAM computation contracts

Check computations from arbitrary representing states, composition, unread input space, termination,
and the canonical-initial-state form shared with the TM correctness interface.
-/

@[expose] public section

namespace AlgoleanTests.WordRAMSolves

open Algolean Algolean.Algorithms Algolean.Algorithms.WordRAM Cslib
open scoped Prog WordRAM

abbrev r0 : Register 2 := 0
abbrev r1 : Register 2 := 1

/-- Only the input register is constrained; scratch registers, flags, and memory are arbitrary. -/
def inRegister (value : Word 8) (s : RAMState 8 2) : Prop := s.Registers r0 = value

def increment : Prog (WordRAM 8 2) Unit := do [WordRAM 8 2]
  r1 ←ᵣ imm[1]
  r0 ←ᵣ r0 + r1

theorem increment_computes : ComputesIn increment (· + 1) inRegister inRegister
    (timeSpaceBound (fun _ => ∅) (fun _ => 2) (fun _ => 0)) := by
  intro input s hi
  simp only [inRegister, r0] at hi
  let t := s.writeRegister r1 1
  let final := t.writeRegister r0 (input + 1)
  have hs : Completes (FreeM.lift (.set r1 1)) s ⟨1, ∅⟩ t := ⟨1, execute_set_succ 0 s r1 1⟩
  have hb : Completes (FreeM.lift (.binop .add r0 r0 r1)) t ⟨1, ∅⟩ final := by
    refine ⟨1, ?_⟩
    simpa [t, final, BinOp.eval, r0, r1, hi] using execute_binop_succ 0 t .add r0 r0 r1
  refine ⟨input + 1, ⟨2, ∅⟩, final, ?_, ?_, rfl, ?_⟩
  · simpa [increment] using hs.seq hb
  · simp [inRegister, final]
  · simp [timeSpaceBound, RAMCost.totalSpace]

-- The same function and representation compose without reinitializing the machine.
example : Computes (do increment; increment) (fun input => input + 1 + 1)
    inRegister inRegister := increment_computes.computes.comp increment_computes.computes

-- A function computation also solves any relation allowing that answer.
example : Solves increment (fun input => {output | output = input ∨ output = input + 1})
    inRegister inRegister := by
  apply increment_computes.solves.consequence
  intro input output ho
  have ho : output = input + 1 := ho
  exact Or.inr ho

-- Bounds can inspect the final state as well as costs, as required for TM space accounting.
example : ComputesIn increment (· + 1) inRegister inRegister
    (fun input cost final => cost.time ≤ 3 ∧ final.Registers r0 = input + 1) := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, hb⟩ := increment_computes input s hi
  refine ⟨output, cost, final, hc, ho, hs, hb.1.trans (by change 2 ≤ 3; decide), ?_⟩
  have hs : output = input + 1 := hs
  simpa [inRegister, hs] using ho

/-- The input lives in two memory cells, with arbitrary registers, flags, and other cells. -/
def inMemory (input : Word 8 × Word 8) (s : RAMState 8 2) : Prop :=
  s.Memory 7 = input.1 ∧ s.Memory 8 = input.2

-- Total space retains unread input cells even when the program makes no memory accesses.
theorem memory_identity : ComputesIn (pure ()) id inMemory inMemory
    (timeSpaceBound (fun _ => {7, 8}) (fun _ => 0) (fun _ => 2)) := by
  intro input s hi
  refine ⟨input, 0, s, completes_pure s, hi, rfl, ?_⟩
  simp [timeSpaceBound, RAMCost.totalSpace]

example : ¬ComputesIn (pure ()) id inMemory inMemory
    (timeSpaceBound (fun _ => {7, 8}) (fun _ => 0) (fun _ => 0)) := by
  intro h
  have hb := h.bounded (input := (0, 0)) (s := RAMState.zero)
    (by exact ⟨rfl, rfl⟩) (completes_pure RAMState.zero)
  change (0 : Nat) ≤ 0 ∧ 2 ≤ 0 at hb
  omega

-- Divergence cannot satisfy a contract merely because there are no completed executions.
example : ¬Solves (whileLoop .eq (pure ()) : Prog (WordRAM 8 2) Unit)
    (fun (_ : Unit) => Set.univ)
    (fun _ s => s.Flags .eq = true) (fun (_ : Unit) _ => True) := by
  intro h
  obtain ⟨cost, final, fuel, hfuel⟩ :=
    h.terminates (input := ()) (s := (RAMState.zero : RAMState 8 2).writeFlag .eq true) (by simp)
  have never (fuel : Nat) (s : RAMState 8 2) (hs : s.Flags .eq = true) :
      execute fuel (whileLoop .eq (pure ())) s = none := by
    induction fuel with
    | zero => simp
    | succ fuel ih => simpa [execute_while_succ, hs] using ih
  rw [never fuel _ (by simp)] at hfuel
  contradiction

-- Canonical initialization gives exactly the existential form used by TMSolves.
example (program : Prog (WordRAM w k) Unit) (init : Input → RAMState w k)
    (spec : Input → Set Output) (repOutput : Output → RAMState w k → Prop)
    (bound : Input → RAMCost w → RAMState w k → Prop) :
    SolvesIn program spec (fun input s => s = init input) repOutput bound ↔
      ∀ input, ∃ output cost final, Completes program (init input) cost final ∧
        repOutput output final ∧ output ∈ spec input ∧ bound input cost final :=
  solvesIn_init_iff program spec init repOutput bound

end AlgoleanTests.WordRAMSolves
