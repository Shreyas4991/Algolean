/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Compiler.Internal.Control
import Mathlib.Data.Fintype.EquivFin

/-!
# Constructing the compiled transition table

This file turns a query program into an ordinary single-tape Turing machine.

* A compiled control state records a program position and a source logical label.
* Each query becomes a transition that performs its tape action and selects the next position.
* Finishing the program halts the compiled machine and preserves the output tape.

The source type `tm.State` supplies logical labels. The program position also carries control
information. With `R` program positions and `Q` logical labels, the compiled machine has
`R * (Q + 1)` control states. The extra label is `none`. Since `L` source instructions give at most
`L + 1` positions, the compiled machine has at most `(L + 1) * (Q + 1)` control states.
For a fixed logical label count `Q`, this state bound is linear in program size `L`.
The source machine's transition table is unused.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery.Compiler.Internal

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/-- A compiled control state pairs a program position with a source logical label or `none`. -/
abbrev CompiledState (program : Program tm) :=
  Fin (programPositions program).card × Option tm.State

/-- Every execution position is assigned a bounded natural-number label. -/
noncomputable def position (program pending : Program tm)
    (h : pending ∈ programPositions program) : Fin (programPositions program).card :=
  (programPositions program).equivFin ⟨pending, h⟩

/-- The compiled transition writes or moves exactly as the query does and updates its label. -/
def action (program : Program tm) (label : Option tm.State) (symbol : Option Symbol) :
    SingleTapeTM.Stmt Symbol × Option tm.State :=
  match program with
  | .pure _ => (⟨symbol, none⟩, label)
  | .liftBind query _ =>
    match query with
    | .write value => (⟨value, none⟩, label)
    | .update state => (⟨symbol, none⟩, some state)
    | .move direction =>
      (⟨symbol, match direction with | .Left => some .left | .Right => some .right | .Stop => none⟩,
        label)
    | .branchCode _ _ _ => (⟨symbol, none⟩, label)
    | .whileCode _ _ => (⟨symbol, none⟩, label)

/-- This value distinguishes completed programs from programs that have another query to run. -/
def finished (program : Program tm) : Bool :=
  match program with
  | .pure _ => true
  | .liftBind _ _ => false

/--
The compiled machine stores the program's execution position in its finite control. Its
transition table implements each query and halts only after the program has finished.
-/
noncomputable def machine (program : Program tm) : SingleTapeTM Symbol where
  State := CompiledState program
  q₀ := (position program program (mem_programPositions program), some tm.q₀)
  tr control symbol :=
    let pending := ((programPositions program).equivFin.symm control.1).val
    let result := action pending control.2 symbol
    (result.1,
      if finished pending then none
      else some (position program (advance pending control.2 symbol)
        (advance_mem_programPositions program pending
          ((programPositions program).equivFin.symm control.1).property control.2 symbol),
          result.2))

/-- This configuration records a source tape and logical label at a chosen compiled position. -/
noncomputable def encodeCfg (program pending : Program tm) (h : pending ∈ programPositions program)
    (cfg : tm.Cfg) : (machine program).Cfg :=
  ⟨some (position program pending h, cfg.state), cfg.BiTape⟩

/-- Compilation places the same input tape under the same initial logical label. -/
theorem encodeCfg_init (program : Program tm) (input : List Symbol) :
    encodeCfg program program (mem_programPositions program) (tm.initCfg input) =
      (machine program).initCfg input := rfl

/-- The program chosen by a compiled transition agrees with the query interpreter's next program. -/
theorem advance_eq_step_program (query : TMQuery tm α) (next : α → Program tm) (s : TMState tm) :
    advance (.liftBind query next) s.config.state s.config.BiTape.head =
      (TMQuery.step query next s).program := by
  cases query with
  | write value => rfl
  | update state => rfl
  | move direction => rfl
  | branchCode condition yes no =>
    simp only [advance, test_eq_eval, assemble_eq_forM, TMQuery.step]
  | whileCode condition body =>
    simp only [advance, test_eq_eval, TMQuery.step]
    split
    · rw [assemble_eq_forM]
      congr 1
    · rfl

/-- Applying the compiled tape action gives exactly the configuration produced by the query. -/
theorem action_eq_step_config (query : TMQuery tm α) (next : α → Program tm) (s : TMState tm) :
    (⟨(action (.liftBind query next) s.config.state s.config.BiTape.head).2,
      (s.config.BiTape.write
        (action (.liftBind query next) s.config.state s.config.BiTape.head).1.symbol).optionMove
          (action (.liftBind query next) s.config.state
            s.config.BiTape.head).1.movement⟩ : tm.Cfg) =
      (TMQuery.step query next s).machine.config := by
  cases query with
  | write value => rfl
  | update state => rfl
  | move direction => cases direction <;> rfl
  | branchCode condition yes no => rfl
  | whileCode condition body => rfl

/-- A compiled query step advances to the matching source configuration and next program. -/
theorem machine_step (program : Program tm) (query : TMQuery tm α) (next : α → Program tm)
    (h : (.liftBind query next : Program tm) ∈ programPositions program) (s : TMState tm) :
    (machine program).step (encodeCfg program (.liftBind query next) h s.config) =
      some (encodeCfg program (TMQuery.step query next s).program
        (advance_eq_step_program query next s ▸
          advance_mem_programPositions program (.liftBind query next) h _ _)
        (TMQuery.step query next s).machine.config) := by
  have hprogram := advance_eq_step_program query next s
  have hconfig := action_eq_step_config query next s
  have hmem := advance_mem_programPositions program (.liftBind query next) h
    s.config.state s.config.BiTape.head
  have hsubtype : (⟨advance (.liftBind query next) s.config.state s.config.BiTape.head, hmem⟩ :
      ↥(programPositions program)) = ⟨(TMQuery.step query next s).program, hprogram ▸ hmem⟩ :=
    Subtype.ext hprogram
  have hposition := congrArg ((programPositions program).equivFin)
    hsubtype
  have hstate := congrArg SingleTapeTM.Cfg.state hconfig
  have htape := congrArg SingleTapeTM.Cfg.BiTape hconfig
  simp only [SingleTapeTM.step, encodeCfg, machine, position, Equiv.symm_apply_apply, finished,
    Bool.false_eq_true, ite_false]
  exact congrArg some (congrArg₂ SingleTapeTM.Cfg.mk
    (congrArg some (congrArg₂ Prod.mk hposition hstate)) htape)

/-- At the final program position, the compiled machine halts without changing the tape. -/
theorem machine_halt (program : Program tm) (h : (pure () : Program tm) ∈ programPositions program)
    (cfg : tm.Cfg) :
    (machine program).step (encodeCfg program (pure ()) h cfg) = some ⟨none, cfg.BiTape⟩ := by
  simp [machine, encodeCfg, position, finished, action, BiTape.optionMove, BiTape.write,
    ← FreeM.pure_eq_pure]

end Algolean.Algorithms.TMQuery.Compiler.Internal
