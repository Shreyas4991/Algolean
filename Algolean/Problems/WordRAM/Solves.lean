/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.WordRAM
public import Algolean.Problems.Basic

/-!
# Solving problems with one fixed WordRAM program

`Solves` requires termination and an allowed represented output on every represented input.
`SolvesIn` additionally bounds the cost and final state of that same completed execution.
The specification has the same `Input → Set Output` form as `TMSolves`.

Input and output representations are relations with physical machine states. Input admissibility,
including memory-fit conditions, belongs in the input relation. The guarantee covers every state
representing an input, allowing scratch registers, flags, and unrelated memory to be unconstrained.
Only inputs with a representing state are covered. Outputs are observed in the final machine state,
not through the program's Lean return value.

The program is fixed before quantifying over inputs. Interpreter fuel is hidden by `Completes`;
it is not a time bound. A resource bound may inspect both execution cost and final state, so this
interface can also express the final-state space convention used by Turing machines.
`timeSpaceBound` specializes it to WordRAM time and total accessed space,
including the input region.
Bounds may depend on abstract inputs. Compose with input size to obtain size-based bounds.

The parameters keep completion, representation, specification, and resource accounting
separate. `solvesIn_init_iff` gives the canonical-initial-state form used by `TMSolves`.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

variable {Input : Type u} {Output : Type v}

/-- A fixed program terminates with an allowed represented output and meets the resource bound.
The same statement applies to every initial state representing each input. -/
def SolvesIn (program : Prog (WordRAM w k) Unit) (spec : Input → Set Output)
    (repInput : Input → RAMState w k → Prop) (repOutput : Output → RAMState w k → Prop)
    (bound : Input → RAMCost w → RAMState w k → Prop) : Prop :=
  ∀ input s, repInput input s → ∃ output cost final,
    Completes program s cost final ∧ repOutput output final ∧ output ∈ spec input ∧
      bound input cost final

/-- Total correctness of a fixed program, without a resource bound. -/
abbrev Solves (program : Prog (WordRAM w k) Unit) (spec : Input → Set Output)
    (repInput : Input → RAMState w k → Prop) (repOutput : Output → RAMState w k → Prop) : Prop :=
  SolvesIn program spec repInput repOutput (fun _ _ _ => True)

/-- Bound primitive-operation time and total accessed space, including unread input cells.
Registers and flags are excluded from space; interpreter fuel is excluded from time. -/
def timeSpaceBound (inputRegion : Input → Finset (Word w)) (time space : Input → Nat)
    (input : Input) (cost : RAMCost w) (_final : RAMState w k) : Prop :=
  cost.time ≤ time input ∧ cost.totalSpace (inputRegion input) ≤ space input

namespace SolvesIn

variable {program : Prog (WordRAM w k) Unit} {spec spec' : Input → Set Output}
variable {repInput : Input → RAMState w k → Prop} {repOutput : Output → RAMState w k → Prop}
variable {bound bound' : Input → RAMCost w → RAMState w k → Prop}

/-- Weakening the resource bound preserves the same computation and output specification. -/
theorem mono (h : SolvesIn program spec repInput repOutput bound)
    (hle : ∀ input cost final, bound input cost final → bound' input cost final) :
    SolvesIn program spec repInput repOutput bound' := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, hb⟩ := h input s hi
  exact ⟨output, cost, final, hc, ho, hs, hle input cost final hb⟩

/-- Allowing more outputs preserves correctness and the resource guarantee. -/
theorem consequence (h : SolvesIn program spec repInput repOutput bound)
    (hpost : ∀ input, spec input ⊆ spec' input) :
    SolvesIn program spec' repInput repOutput bound := by
  intro input s hi
  obtain ⟨output, cost, final, hc, ho, hs, hb⟩ := h input s hi
  exact ⟨output, cost, final, hc, ho, hpost input hs, hb⟩

/-- A contract also applies when the allowed initial states are restricted. -/
theorem restrict (h : SolvesIn program spec repInput repOutput bound)
    {repInput' : Input → RAMState w k → Prop}
    (hpre : ∀ input s, repInput' input s → repInput input s) :
    SolvesIn program spec repInput' repOutput bound :=
  fun input s hi => h input s (hpre input s hi)

/-- Forgetting resource bounds retains total correctness. -/
theorem solves (h : SolvesIn program spec repInput repOutput bound) :
    Solves program spec repInput repOutput := h.mono (fun _ _ _ _ => trivial)

/-- A represented input must have a completed execution, independently of its resource bound. -/
theorem terminates (h : SolvesIn program spec repInput repOutput bound)
    {input : Input} {s : RAMState w k} (hi : repInput input s) :
    ∃ cost final, Completes program s cost final := by
  obtain ⟨_, cost, final, hc, _⟩ := h input s hi
  exact ⟨cost, final, hc⟩

/-- Every completed execution from a represented input has an allowed represented output.
This reuses determinism of completion, rather than imposing a second execution semantics. -/
theorem correct (h : SolvesIn program spec repInput repOutput bound)
    {input : Input} {s final : RAMState w k} {cost : RAMCost w} (hi : repInput input s)
    (hc : Completes program s cost final) :
    ∃ output, repOutput output final ∧ output ∈ spec input := by
  obtain ⟨output, _, _, hc', ho, hs, _⟩ := h input s hi
  obtain ⟨rfl, rfl⟩ := hc'.unique hc
  exact ⟨output, ho, hs⟩

/-- Every completed execution from a represented input satisfies the resource bound. -/
theorem bounded (h : SolvesIn program spec repInput repOutput bound)
    {input : Input} {s final : RAMState w k} {cost : RAMCost w} (hi : repInput input s)
    (hc : Completes program s cost final) : bound input cost final := by
  obtain ⟨_, _, _, hc', _, _, hb⟩ := h input s hi
  obtain ⟨rfl, rfl⟩ := hc'.unique hc
  exact hb

end SolvesIn

/-- Choosing one canonical initial state recovers the initialized-input form used for TMs. -/
theorem solvesIn_init_iff (program : Prog (WordRAM w k) Unit) (spec : Input → Set Output)
    (init : Input → RAMState w k) (repOutput : Output → RAMState w k → Prop)
    (bound : Input → RAMCost w → RAMState w k → Prop) :
    SolvesIn program spec (fun input s => s = init input) repOutput bound ↔
      ∀ input, ∃ output cost final, Completes program (init input) cost final ∧
        repOutput output final ∧ output ∈ spec input ∧ bound input cost final := by
  constructor
  · intro h input
    exact h input (init input) rfl
  · rintro h input s rfl
    exact h input

/-- Increasing time and total-space bounds preserves the corresponding resource predicate. -/
theorem timeSpaceBound_mono {inputRegion : Input → Finset (Word w)}
    {time space time' space' : Input → Nat}
    (htime : ∀ input, time input ≤ time' input) (hspace : ∀ input, space input ≤ space' input)
    {input : Input} {cost : RAMCost w} {final : RAMState w k}
    (h : timeSpaceBound inputRegion time space input cost final) :
    timeSpaceBound inputRegion time' space' input cost final :=
  ⟨h.1.trans (htime input), h.2.trans (hspace input)⟩

end Algolean.Algorithms.WordRAM
