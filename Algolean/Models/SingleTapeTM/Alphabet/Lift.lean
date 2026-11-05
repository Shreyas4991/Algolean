/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Alphabet.Basic
public import Algolean.Models.SingleTapeTM.Composition.Functions

/-!
# Running Turing machine programs over an extended alphabet

This file lifts an existing Turing machine program from `Symbol` to `Alphabet.Extended Symbol
markers`, with at least one added marker. It tags the original symbols with `Sum.inl`, preserves
blanks, and retains the original control states. The translation also handles symbol tests inside
branches and loops.

The lifted program has the same execution result, interpreter fuel, head-move cost, head position,
and tape histories on a tape of tagged original symbols. Surrounding programs can use the added
markers to separate input from certificate before running the lifted program.

The query translation is an ordinary `Reduction`; whole programs use the existing
`Prog.reduceProg` API. No second program interpreter is needed.
-/

@[expose] public section

open Algolean Algolean.Algorithms

namespace Cslib.Turing

variable {Symbol : Type} {markers : ℕ}

/--
This pure Lean function tags every occupied stack cell with `Sum.inl`, preserving all blanks
and the positions of the original cells.
-/
def StackTape.extendAlphabet (t : StackTape Symbol) :
    StackTape (Alphabet.Extended Symbol markers) where
  toList := t.toList.map (Option.map Sum.inl)
  toList_getLast?_ne_some_none := by
    have h := t.toList_getLast?_ne_some_none
    rw [List.getLast?_map]
    cases he : t.toList.getLast? with
    | none => simp
    | some a => cases a <;> simp_all

@[simp] theorem StackTape.extendAlphabet_nil :
    (StackTape.nil : StackTape Symbol).extendAlphabet (markers := markers) = StackTape.nil := rfl

@[simp] theorem StackTape.extendAlphabet_head (t : StackTape Symbol) :
    (t.extendAlphabet (markers := markers)).head = t.head.map Sum.inl := by
  cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.extendAlphabet_tail (t : StackTape Symbol) :
    (t.extendAlphabet (markers := markers)).tail = t.tail.extendAlphabet := by
  cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.extendAlphabet_cons (a : Option Symbol) (t : StackTape Symbol) :
    (StackTape.cons a t).extendAlphabet (markers := markers) =
      StackTape.cons (a.map Sum.inl) t.extendAlphabet := by
  cases a <;> cases t with | mk l h => cases l <;> rfl

@[simp] theorem StackTape.extendAlphabet_length (t : StackTape Symbol) :
    (t.extendAlphabet (markers := markers)).length = t.length := by
  simp [extendAlphabet, length]

@[simp] theorem StackTape.extendAlphabet_mapSome (input : List Symbol) :
    (StackTape.mapSome input).extendAlphabet (markers := markers) =
      StackTape.mapSome (input.map Sum.inl) := by
  simp [extendAlphabet, mapSome, List.map_map, Function.comp_def]

/--
This pure Lean function tags the symbols on the entire tape with `Sum.inl`. It preserves the
head's location within the tape and every blank separating occupied regions.
-/
@[simps] def BiTape.extendAlphabet (t : BiTape Symbol) :
    BiTape (Alphabet.Extended Symbol markers) :=
  ⟨t.head.map Sum.inl, t.left.extendAlphabet, t.right.extendAlphabet⟩

@[simp] theorem BiTape.extendAlphabet_mk₁ (input : List Symbol) :
    (BiTape.mk₁ input).extendAlphabet (markers := markers) = BiTape.mk₁ (input.map Sum.inl) := by
  cases input <;> simp [extendAlphabet, mk₁, nil]

@[simp] theorem BiTape.extendAlphabet_write (t : BiTape Symbol) (a : Option Symbol) :
    (t.write a).extendAlphabet (markers := markers) =
      t.extendAlphabet.write (a.map Sum.inl) := rfl

@[simp] theorem BiTape.extendAlphabet_moveLeft (t : BiTape Symbol) :
    t.moveLeft.extendAlphabet (markers := markers) = t.extendAlphabet.moveLeft := by
  simp [extendAlphabet, moveLeft]

@[simp] theorem BiTape.extendAlphabet_moveRight (t : BiTape Symbol) :
    t.moveRight.extendAlphabet (markers := markers) = t.extendAlphabet.moveRight := by
  simp [extendAlphabet, moveRight]

variable [Inhabited Symbol] [Fintype Symbol] [NeZero markers]

/--
This machine retains the original finite control and translates its transition table to the
extended alphabet. Tagged original symbols follow the original transitions. An added marker is
treated as blank by this table; the query programs surrounding a lifted program can test and
write markers explicitly.
-/
abbrev SingleTapeTM.extendAlphabet (tm : SingleTapeTM Symbol) :
    SingleTapeTM (Alphabet.Extended Symbol markers) where
  State := tm.State
  q₀ := tm.q₀
  tr q a :=
    let (statement, next) := tm.tr q (a.bind Sum.getLeft?)
    (⟨statement.symbol.map Sum.inl, statement.movement⟩, next)

/--
On a tape containing only tagged original symbols, one transition of the extended machine
matches one original transition after tagging its resulting tape. This statement concerns the
transition tables independently of query-program execution.
-/
theorem SingleTapeTM.step_extendAlphabet (tm : SingleTapeTM Symbol) (cfg : tm.Cfg) :
    (tm.extendAlphabet (markers := markers)).step ⟨cfg.state, cfg.BiTape.extendAlphabet⟩ =
      (tm.step cfg).map (fun t => ⟨t.state, t.BiTape.extendAlphabet⟩) := by
  obtain ⟨state, tape⟩ := cfg
  cases state with
  | none => rfl
  | some q =>
    have hhead : (tape.head.map (Sum.inl : Symbol → Alphabet.Extended Symbol markers)).bind
        Sum.getLeft? = tape.head := by cases tape.head <;> rfl
    cases htr : tm.tr q tape.head with
    | mk statement next =>
      cases statement with
      | mk symbol direction =>
        cases direction with
        | none =>
          simp [SingleTapeTM.step, SingleTapeTM.extendAlphabet, BiTape.extendAlphabet, hhead, htr,
            BiTape.optionMove, BiTape.write]
        | some direction =>
          cases direction <;>
            simp [SingleTapeTM.step, SingleTapeTM.extendAlphabet, BiTape.extendAlphabet, hhead, htr,
              BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.moveRight, BiTape.write]

end Cslib.Turing

namespace Algolean.Algorithms

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] {tm : SingleTapeTM Symbol}
variable {markers : ℕ} [NeZero markers]

/--
This pure Lean function lifts the machine's tape to the extended alphabet. It retains the control
label, absolute head coordinate, allocated-cell history, and visited-cell history.
-/
@[simps] def TMState.extendAlphabet (s : TMState tm) :
    TMState (tm.extendAlphabet (markers := markers)) where
  config := ⟨s.config.state, s.config.BiTape.extendAlphabet⟩
  headPos := s.headPos
  cellsAllocated := s.cellsAllocated
  cellsVisited := s.cellsVisited

@[simp] theorem TMState.extendAlphabet_init (input : List Symbol) :
    (TMState.init tm input).extendAlphabet (markers := markers) =
      TMState.init tm.extendAlphabet (input.map Sum.inl) := by
  cases input <;> simp [extendAlphabet, TMState.init, SingleTapeTM.initCfg,
    SingleTapeTM.extendAlphabet, BiTape.mk₁, BiTape.nil, BiTape.extendAlphabet]

/--
This translation tags the tape-symbol constants in a machine condition. It keeps control-state
tests unchanged and translates negated conditions recursively.
-/
@[simp] def TMCondition.extendAlphabet : TMCondition tm →
    TMCondition (tm.extendAlphabet (markers := markers))
  | .tapeIs a => .tapeIs (a.map Sum.inl)
  | .stateIs q => .stateIs q
  | .not condition => .not condition.extendAlphabet

/--
This query translation tags every symbol written or tested by the original program, including
instructions inside branches and loops. It preserves state updates and head movements.
-/
def TMQuery.extendAlphabet : TMQuery tm α → TMQuery (tm.extendAlphabet (markers := markers)) α
  | .write a => .write (a.map Sum.inl)
  | .update q => .update q
  | .move direction => .move direction
  | .branchCode condition yes no =>
    .branchCode condition.extendAlphabet (yes.map extendAlphabet) (no.map extendAlphabet)
  | .whileCode condition body =>
    .whileCode condition.extendAlphabet (body.map extendAlphabet)

namespace TMQuery

/--
This reduction implements each original query by its alphabet-extended query. Applying
`Prog.reduceProg` with this reduction lifts a whole Turing machine program.
-/
def alphabetReduction :
    Reduction (TMQuery tm) (TMQuery (tm.extendAlphabet (markers := markers))) where
  reduce q := FreeM.lift q.extendAlphabet

private theorem extendAlphabet_forM (body : List (TMQuery tm Unit)) :
    FreeM.liftM (m := Prog (TMQuery (tm.extendAlphabet (markers := markers))))
      (fun {α} (q : TMQuery tm α) => FreeM.lift q.extendAlphabet)
      (forM body (fun q => FreeM.lift q)) =
      forM body (fun q => FreeM.lift q.extendAlphabet) := by
  induction body with
  | nil => rfl
  | cons q rest ih => simp only [List.forM_cons, FreeM.liftM_bind, FreeM.liftM_lift, ih]

variable [DecidableEq Symbol] [DecidableEq tm.State]

@[simp] theorem eval_extendAlphabet (condition : TMCondition tm) (s : TMState tm) :
    (condition.extendAlphabet (markers := markers)).eval s.extendAlphabet.config =
      condition.eval s.config := by
  induction condition with
  | tapeIs a => simp [TMState.extendAlphabet, (Option.map_injective Sum.inl_injective).eq_iff]
  | stateIs q => rfl
  | not condition ih => simpa using congrArg Bool.not ih

/--
This translation lifts the pending program and machine state of an interpreter step while keeping
its resource cost unchanged.
-/
@[simps] def extendAlphabetStep
    (next : FuelExecMonad.Step (TMQuery tm) (TMState tm) TMCost α) :
    FuelExecMonad.Step (TMQuery (tm.extendAlphabet (markers := markers)))
      (TMState (tm.extendAlphabet (markers := markers))) TMCost α :=
  ⟨next.cost, next.machine.extendAlphabet, next.program.reduceProg alphabetReduction⟩

theorem step_extendAlphabet (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β) (s : TMState tm) :
    step (q.extendAlphabet (markers := markers))
      (fun a => Prog.reduceProg (next a) alphabetReduction) s.extendAlphabet =
      extendAlphabetStep (step q next s) := by
  cases q with
  | move direction =>
    cases direction <;> simp [extendAlphabet, step, extendAlphabetStep,
      TMState.extendAlphabet] <;> split <;> simp_all
  | branchCode condition yes no =>
    have he := eval_extendAlphabet (markers := markers) condition s
    simp only [TMState.extendAlphabet] at he
    cases h : condition.eval s.config <;>
      simp [extendAlphabet, step, extendAlphabetStep, TMState.extendAlphabet,
        he, h, Prog.reduceProg, alphabetReduction,
        FreeM.liftM_bind, extendAlphabet_forM]
  | whileCode condition body =>
    have he := eval_extendAlphabet (markers := markers) condition s
    simp only [TMState.extendAlphabet] at he
    cases h : condition.eval s.config <;>
      simp [extendAlphabet, step, extendAlphabetStep, TMState.extendAlphabet,
        he, h, Prog.reduceProg, alphabetReduction,
        FreeM.liftM_bind, extendAlphabet_forM]
  | _ => simp [extendAlphabet, step, extendAlphabetStep, TMState.extendAlphabet]

/--
Lifting a Turing machine program and its initial tape preserves execution, including failures,
the exact resource cost, and any remaining interpreter fuel.
-/
@[simp] theorem execute_extendAlphabet (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm) :
    execute fuel (p.reduceProg (alphabetReduction (markers := markers))) s.extendAlphabet =
      (execute fuel p s).map (fun (result, final) =>
        (result, ⟨final.machine.extendAlphabet, final.fuel⟩)) := by
  induction fuel generalizing p s with
  | zero =>
    cases p with
    | pure a => simp [Prog.reduceProg, alphabetReduction]
    | liftBind q next =>
      change execute 0 (.liftBind q.extendAlphabet
        (fun a => Prog.reduceProg (next a) alphabetReduction)) _ = _
      simp only [FuelExecMonad.execute_zero_liftBind, Option.map_none]
  | succ fuel ih =>
    cases p with
    | pure a => simp [Prog.reduceProg, alphabetReduction]
    | liftBind q next =>
      change execute (fuel + 1) (.liftBind q.extendAlphabet
        (fun a => Prog.reduceProg (next a) alphabetReduction)) _ = _
      simp only [FuelExecMonad.execute_liftBind_succ, step_extendAlphabet,
        extendAlphabetStep_machine, extendAlphabetStep_program, extendAlphabetStep_cost, ih]
      simp only [execute, TMModel]
      cases FuelExecMonad.execute (interpreter tm).toModel fuel
        (step q next s).program (step q next s).machine <;> rfl

/--
A completed Turing machine program lifts to the extended alphabet with the same head-move and
allocation costs, final control label, head coordinate, and tape histories.
-/
theorem Completes.extendAlphabet {p : Prog (TMQuery tm) Unit} {s t : TMState tm} {cost : TMCost}
    (h : Completes p s cost t) :
    Completes (p.reduceProg (alphabetReduction (markers := markers)))
      s.extendAlphabet cost t.extendAlphabet := by
  obtain ⟨fuel, h⟩ := h
  exact ⟨fuel, by simp [h]⟩

/--
A bounded computation on an initialized tape lifts to the tagged input and output words with the
same head-move bound.
-/
theorem OutputsWithinTime.extendAlphabet {p : Prog (TMQuery tm) Unit} {input output : List Symbol}
    {time : ℕ} (h : OutputsWithinTime p input output time) :
    OutputsWithinTime (p.reduceProg (alphabetReduction (markers := markers)))
      (input.map Sum.inl) (output.map Sum.inl) time := by
  obtain ⟨fuel, r, u, hr, ht, hc⟩ := h
  refine ⟨fuel, r, ⟨u.machine.extendAlphabet, u.fuel⟩, ?_, ?_, hc⟩
  · rw [← TMState.extendAlphabet_init, execute_extendAlphabet, hr]
    rfl
  · simp [TMState.extendAlphabet, ht]

end TMQuery

namespace EncodedComputer

variable [DecidableEq Symbol] [DecidableEq tm.State]

/--
This value lifts a verified Turing machine program to an extended alphabet. Its logical function,
time bound, and final head coordinate stay the same; both tape encodings tag their symbols with
`Sum.inl`.
-/
@[simps program]
def extendAlphabet {α β : Type} {ei : α → List Symbol} {eo : β → List Symbol} {f : α → β}
    {time : α → ℕ} {position : α → ℤ → ℤ}
    (machine : EncodedComputer tm ei eo f time position) :
    EncodedComputer (tm.extendAlphabet (markers := markers))
      (fun x => (ei x).map Sum.inl) (fun y => (eo y).map Sum.inl) f time position where
  program := machine.program.reduceProg TMQuery.alphabetReduction
  correct input s hs := by
    let original : TMState tm := {
      config := ⟨s.config.state, BiTape.mk₁ (ei input)⟩
      headPos := s.headPos
      cellsAllocated := s.cellsAllocated
      cellsVisited := s.cellsVisited }
    have hstate : original.extendAlphabet = s := by
      cases s with | mk cfg pos allocated visited =>
      cases cfg with | mk state tape => simp_all [original, TMState.extendAlphabet]
    obtain ⟨cost, final, hc, ht, hp, hm⟩ := machine.correct input original rfl
    refine ⟨cost, final.extendAlphabet, ?_, ?_, hp, hm⟩
    · simpa [hstate] using hc.extendAlphabet (markers := markers)
    · simp [TMState.extendAlphabet, ht, original]

end EncodedComputer

end Algolean.Algorithms
