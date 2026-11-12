/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Problems.WordRAM.Solves

/-!
# Computing functions with one fixed WordRAM program

`Computes` specializes `Solves` to a singleton output specification. `ComputesIn` adds the same
resource bound as `SolvesIn`. Functions, representations, and bounds describe the mathematical
contract; the running program obtains its inputs and produces its outputs through machine state.

The input representation of a second computation may be the output representation of the first.
`Computes.comp` then composes them using the existing `Completes.seq` lemma.
-/

@[expose] public section

namespace Algolean.Algorithms.WordRAM

variable {Input : Type u} {Output : Type v}

/-- A fixed program computes the represented function on every represented input. -/
abbrev Computes (program : Prog (WordRAM w k) Unit) (f : Input → Output)
    (repInput : Input → RAMState w k → Prop) (repOutput : Output → RAMState w k → Prop) : Prop :=
  Solves program (fun input => {f input}) repInput repOutput

/-- Computing a represented function with a bound on execution cost and final state. -/
abbrev ComputesIn (program : Prog (WordRAM w k) Unit) (f : Input → Output)
    (repInput : Input → RAMState w k → Prop) (repOutput : Output → RAMState w k → Prop)
    (bound : Input → RAMCost w → RAMState w k → Prop) : Prop :=
  SolvesIn program (fun input => {f input}) repInput repOutput bound

/-- Forgetting resource bounds retains the same function computation. -/
theorem ComputesIn.computes {program : Prog (WordRAM w k) Unit} {f : Input → Output}
    {repInput : Input → RAMState w k → Prop} {repOutput : Output → RAMState w k → Prop}
    {bound : Input → RAMCost w → RAMState w k → Prop}
    (h : ComputesIn program f repInput repOutput bound) : Computes program f repInput repOutput :=
  h.solves

/-- A computation's output representation holds for every completed execution. -/
theorem ComputesIn.output {program : Prog (WordRAM w k) Unit} {f : Input → Output}
    {repInput : Input → RAMState w k → Prop} {repOutput : Output → RAMState w k → Prop}
    {bound : Input → RAMCost w → RAMState w k → Prop}
    (h : ComputesIn program f repInput repOutput bound) {input : Input}
    {s final : RAMState w k} {cost : RAMCost w} (hi : repInput input s)
    (hc : Completes program s cost final) : repOutput (f input) final := by
  obtain ⟨output, ho, hs⟩ := h.correct hi hc
  have heq : output = f input := hs
  simpa only [heq] using ho

/-- Leaving a represented input unchanged computes the identity function. -/
theorem computes_id (rep : Input → RAMState w k → Prop) :
    Computes (pure ()) id rep rep := by
  intro input s hi
  exact ⟨input, 0, s, completes_pure s, hi, rfl, trivial⟩

/-- Compose function computations when the intermediate output represents the next input. -/
theorem Computes.comp {Middle : Type*} {p q : Prog (WordRAM w k) Unit}
    {f : Input → Middle} {g : Middle → Output}
    {repInput : Input → RAMState w k → Prop} {repMiddle : Middle → RAMState w k → Prop}
    {repOutput : Output → RAMState w k → Prop}
    (hp : Computes p f repInput repMiddle) (hq : Computes q g repMiddle repOutput) :
    Computes (do p; q) (g ∘ f) repInput repOutput := by
  intro input s hi
  obtain ⟨middle, a, t, hp, hm, hf, _⟩ := hp input s hi
  obtain ⟨output, b, final, hq, ho, hg, _⟩ := hq middle t hm
  have hf : middle = f input := hf
  have hg : output = g middle := hg
  exact ⟨output, a + b, final, hp.seq hq, ho, by simp [hf, hg], trivial⟩

end Algolean.Algorithms.WordRAM
