/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Running an existing machine over an augmented alphabet

`tm.augment` keeps the original control states and adds the separator to its tape alphabet.
`augmentProg p` changes every original symbol in `p` to `Augmented.symbol`. It also changes
symbols inside conditions, branches, and loops. Blank cells remain blank.

On a tape containing only original symbols, the lifted program has the same execution,
interpreter fuel, head position, allocated storage, and head visits. The separator is available
to surrounding procedures; lifting an existing program does not give it separator instructions.
-/

@[expose] public section

open Algolean Algolean.Algorithms

namespace Cslib.Turing

variable {Symbol : Type}

/-- Change original symbols to tagged symbols, preserving every blank and tape position. -/
def StackTape.augment (t : StackTape Symbol) : StackTape (Augmented Symbol) where
  toList := t.toList.map (Option.map Augmented.symbol)
  toList_getLast?_ne_some_none := by
    have h := t.toList_getLast?_ne_some_none
    rw [List.getLast?_map]
    cases he : t.toList.getLast? with
    | none => simp
    | some a => cases a <;> simp_all

@[simp] theorem StackTape.augment_nil :
    (StackTape.nil : StackTape Symbol).augment = StackTape.nil := rfl

@[simp] theorem StackTape.augment_head (t : StackTape Symbol) :
    t.augment.head = t.head.map Augmented.symbol := by
  cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.augment_tail (t : StackTape Symbol) :
    t.augment.tail = t.tail.augment := by
  cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.augment_cons (a : Option Symbol) (t : StackTape Symbol) :
    (StackTape.cons a t).augment = StackTape.cons (a.map Augmented.symbol) t.augment := by
  cases a <;> cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.augment_length (t : StackTape Symbol) :
    t.augment.length = t.length := by simp [augment, length]

@[simp] theorem StackTape.augment_mapSome (input : List Symbol) :
    (StackTape.mapSome input).augment = StackTape.mapSome (input.map Augmented.symbol) := by
  simp [augment, mapSome, List.map_map, Function.comp_def]

/-- Tag the symbols on both sides of the head, preserving blanks. -/
@[simps] def BiTape.augment (t : BiTape Symbol) : BiTape (Augmented Symbol) :=
  ⟨t.head.map Augmented.symbol, t.left.augment, t.right.augment⟩

@[simp] theorem BiTape.augment_mk₁ (input : List Symbol) :
    (BiTape.mk₁ input).augment = BiTape.mk₁ (input.map Augmented.symbol) := by
  cases input <;> simp [augment, mk₁, nil]

@[simp] theorem BiTape.augment_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).augment = t.augment.write (a.map Augmented.symbol) := rfl

@[simp] theorem BiTape.augment_moveLeft (t : BiTape Symbol) :
    t.moveLeft.augment = t.augment.moveLeft := by simp [augment, moveLeft]

@[simp] theorem BiTape.augment_moveRight (t : BiTape Symbol) :
    t.moveRight.augment = t.augment.moveRight := by simp [augment, moveRight]

variable [Inhabited Symbol] [Fintype Symbol]

/-- Extend a machine's tape alphabet, retaining its finite control and original transitions.
The extra separator is treated as blank by this transition table. -/
abbrev SingleTapeTM.augment (tm : SingleTapeTM Symbol) : SingleTapeTM (Augmented Symbol) where
  State := tm.State
  q₀ := tm.q₀
  tr q a :=
    let (statement, next) := tm.tr q (a.bind Augmented.equivOption)
    (⟨statement.symbol.map Augmented.symbol, statement.movement⟩, next)

/-- The underlying transition machine also follows exactly the original transitions on tagged
original-symbol tapes. This is independent of the query-program interpreter. -/
theorem SingleTapeTM.step_augment (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    tm.augment.step ⟨cfg.state, cfg.BiTape.augment⟩ =
      (tm.step cfg).map (fun t => ⟨t.state, t.BiTape.augment⟩) := by
  obtain ⟨state, tape⟩ := cfg
  cases state with
  | none => rfl
  | some q =>
    have hhead : (tape.head.map Augmented.symbol).bind Augmented.equivOption = tape.head := by
      cases tape.head <;> rfl
    cases htr : tm.tr q tape.head with
    | mk statement next =>
      cases statement with
      | mk symbol direction =>
        cases direction with
        | none =>
          simp [SingleTapeTM.step, SingleTapeTM.augment, BiTape.augment, hhead, htr,
            BiTape.optionMove, BiTape.write]
        | some direction =>
          cases direction <;>
            simp [SingleTapeTM.step, SingleTapeTM.augment, BiTape.augment, hhead, htr,
              BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.moveRight, BiTape.write]

end Cslib.Turing

namespace Algolean.Algorithms

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}

/-- Lift a complete machine state, retaining all accounting records. -/
@[simps] def TMState.augment (s : TMState tm) : TMState tm.augment where
  config := ⟨s.config.state, s.config.BiTape.augment⟩
  headPos := s.headPos
  cellsAllocated := s.cellsAllocated
  cellsVisited := s.cellsVisited

@[simp] theorem TMState.augment_init (input : List Symbol) :
    (TMState.init tm input).augment = TMState.init tm.augment (input.map Augmented.symbol) := by
  cases input <;> simp [augment, TMState.init, SingleTapeTM.initCfg, SingleTapeTM.augment,
    BiTape.mk₁, BiTape.nil, BiTape.augment]

/-- Tag tape constants in a condition, keeping control-state tests unchanged. -/
@[simp] def TMCondition.augment : TMCondition tm → TMCondition tm.augment
  | .tapeIs a => .tapeIs (a.map Augmented.symbol)
  | .stateIs q => .stateIs q
  | .not condition => .not condition.augment

/-- Lift all instructions, including the bodies of branches and loops. -/
def TMQuery.augment : TMQuery tm α → TMQuery tm.augment α
  | .write a => .write (a.map Augmented.symbol)
  | .update q => .update q
  | .move direction => .move direction
  | .branchCode condition yes no =>
    .branchCode condition.augment (yes.map augment) (no.map augment)
  | .whileCode condition body => .whileCode condition.augment (body.map augment)

namespace TMQuery

/-- Lift an existing fixed program without giving its Lean continuations access to the input. -/
def augmentProg (p : Prog (TMQuery tm) Unit) : Prog (TMQuery tm.augment) Unit :=
  p.liftM (fun q => FreeM.lift q.augment)

@[simp] theorem instructions_augmentProg (p : Prog (TMQuery tm) Unit) :
    instructions (augmentProg p) = (instructions p).map TMQuery.augment := by
  induction p with
  | pure a => cases a; rfl
  | liftBind q next ih => cases q <;> simp_all [augmentProg, FreeM.liftM, instructions, augment]

variable [DecidableEq Symbol] [DecidableEq tm.State]

@[simp] theorem eval_augment (condition : TMCondition tm) (s : TMState tm) :
    condition.augment.eval s.augment.config = condition.eval s.config := by
  induction condition with
  | tapeIs a => simp [TMState.augment, (Option.map_injective Augmented.symbol_injective).eq_iff]
  | stateIs q => rfl
  | not condition ih => simpa using congrArg Bool.not ih

/-- Lift the pending code and machine state of a step, retaining its exact resource cost. -/
@[simps] def Step.augment (next : Step tm) : Step tm.augment :=
  ⟨next.cost, next.machine.augment, next.code.map TMQuery.augment⟩

theorem step_augment (q : TMQuery tm Unit) (rest : List (TMQuery tm Unit)) (s : TMState tm) :
    step q.augment (rest.map TMQuery.augment) s.augment = (step q rest s).augment := by
  cases q with
  | move direction =>
    cases direction <;> simp [TMQuery.augment, step, Step.augment, TMState.augment] <;>
      split <;> simp_all
  | branchCode condition yes no =>
    have he := eval_augment condition s
    simp only [TMState.augment] at he
    cases h : condition.eval s.config <;>
      simp [TMQuery.augment, step, Step.augment, TMState.augment, he, h]
  | whileCode condition body =>
    have he := eval_augment condition s
    simp only [TMState.augment] at he
    cases h : condition.eval s.config <;>
      simp [TMQuery.augment, step, Step.augment, TMState.augment, he, h]
  | _ => simp [TMQuery.augment, step, Step.augment, TMState.augment]

theorem runCode_augment (fuel : ℕ) (code : List (TMQuery tm Unit)) (s : TMState tm) :
    runCode fuel (code.map TMQuery.augment) s.augment =
      (runCode fuel code s).map (fun (r, u) => (r, ⟨u.machine.augment, u.fuel⟩)) := by
  induction fuel generalizing code s with
  | zero => cases code <;> rfl
  | succ fuel ih =>
    simp only [runCode] at ih
    cases code with
    | nil => rfl
    | cons q rest =>
      simp only [List.map_cons, runCode, runCodeWith, step_augment, Step.augment_machine,
        Step.augment_code, Step.augment_cost, ih]
      cases runCodeWith step fuel (step q rest s).code (step q rest s).machine <;> rfl

/-- Alphabet lifting preserves execution, including failed runs and remaining fuel. -/
@[simp] theorem execute_augmentProg (fuel : ℕ) (p : Prog (TMQuery tm) Unit) (s : TMState tm) :
    execute fuel (augmentProg p) s.augment =
      (execute fuel p s).map (fun (r, u) => (r, ⟨u.machine.augment, u.fuel⟩)) := by
  simp [execute_eq_runCode, runCode_augment]

/-- Lift a completed procedure with precisely the same time and additional storage. -/
theorem Completes.augment {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) : Completes (augmentProg p) s.augment cost t.augment := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, by simp [h]⟩

/-- Lift an initialized computation to a tape containing tagged original symbols. -/
theorem OutputsWithinTime.augment {p : Prog (TMQuery tm) Unit} {input output : List Symbol}
    {time : ℕ} (h : OutputsWithinTime p input output time) :
    OutputsWithinTime (augmentProg p) (input.map Augmented.symbol)
      (output.map Augmented.symbol) time := by
  obtain ⟨fuel, r, u, hr, ht, hc⟩ := h
  refine ⟨fuel, r, ⟨u.machine.augment, u.fuel⟩, ?_, ?_, hc⟩
  · rw [← TMState.augment_init, execute_augmentProg, hr]
    rfl
  · simp [TMState.augment, ht]

end TMQuery

namespace EncodedComputer

variable [DecidableEq Symbol] [DecidableEq tm.State]

/-- Lift a verified machine automatically. Its logical inputs, outputs, bounds, and head-position
contract stay the same; the tape encodings use tagged original symbols. -/
@[simps program]
def augment {α β : Type} {ei : α → List Symbol} {eo : β → List Symbol} {f : α → β}
    {time : α → ℕ} {position : α → ℤ → ℤ}
    (machine : EncodedComputer tm ei eo f time position) :
    EncodedComputer tm.augment (fun x => (ei x).map Augmented.symbol)
      (fun y => (eo y).map Augmented.symbol) f time position where
  program := TMQuery.augmentProg machine.program
  correct input s hs := by
    let original : TMState tm := {
      config := ⟨s.config.state, BiTape.mk₁ (ei input)⟩
      headPos := s.headPos
      cellsAllocated := s.cellsAllocated
      cellsVisited := s.cellsVisited }
    have hstate : original.augment = s := by
      cases s with | mk cfg pos allocated visited =>
      cases cfg with | mk state tape => simp_all [original, TMState.augment]
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := machine.correct input original rfl
    refine ⟨cost, final.augment, ?_, ?_, hp, hm⟩
    · simpa [hstate] using hc.augment
    · simp [TMState.augment, ht, original]

end EncodedComputer

end Algolean.Algorithms
