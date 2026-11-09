/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Finite descriptions of Turing machines

* `Description` numbers the states and records the initial state and transition table.
* `Description.machine` interprets the description as a CSLib single-tape Turing machine.

Each transition writes a symbol, optionally moves the head, and selects a state or halts.
Blank cells are distinct from every tape symbol.
-/

@[expose] public section

namespace Cslib.Turing.SingleTapeTM

/--
A transition specifies a symbol to write, an optional direction, and an optional next state.
The direction is false for left and true for right. A missing direction keeps the head still,
and a missing next state halts the machine.
-/
abbrev Transition (Symbol : Type) (states : ℕ) :=
  Option Symbol × Option Bool × Option (Fin (states + 1))

/-- A description numbers the finitely many states and supplies one transition for each case. -/
structure Description (Symbol : Type) where
  /-- There are `states + 1` states, so the initial state always exists. -/
  states : ℕ
  /-- Execution starts in this numbered state. -/
  initial : Fin (states + 1)
  /-- The current state and scanned symbol select the next transition. -/
  transition : Fin (states + 1) → Option Symbol → Transition Symbol states

namespace Description

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

/-- This machine executes the finite transition table without changing its step count. -/
def machine (description : Description Symbol) : SingleTapeTM Symbol where
  State := Fin (description.states + 1)
  q₀ := description.initial
  tr state symbol :=
    let (write, movement, next) := description.transition state symbol
    (⟨write, movement.map (fun right => if right then .right else .left)⟩, next)

/-- A description is equivalent to its largest state number, initial state, and transition table. -/
def equiv : Description Symbol ≃
    Σ states : ℕ, Fin (states + 1) ×
      (Fin (states + 1) → Option Symbol → Transition Symbol states) where
  toFun description := ⟨description.states, description.initial, description.transition⟩
  invFun description := ⟨description.1, description.2.1, description.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Description
end Cslib.Turing.SingleTapeTM
