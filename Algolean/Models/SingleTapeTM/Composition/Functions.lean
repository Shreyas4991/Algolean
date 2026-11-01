/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Sequential
public import Algolean.Complexity.PolytimeBasicClasses

/-!
# Reusing programs that compute functions

This file states when a tape program can be reused to compute a function. It must work with any
starting state label and records of tape use, preserve that label, and finish at its
starting head coordinate with the head at the first output cell.

These requirements let procedures run in sequence using the actual tape left by the previous
procedure. The file proves bounds on their combined time, tape use, and output length. It also
packages these proofs as [TimeComputable](##Algolean.Algorithms.TMQuery.TimeComputable) and
[PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable) records.

## Main definitions and results

* [Computes](##Algolean.Algorithms.TMQuery.Computes) states the requirements for a reusable
  procedure.
* [Computes.comp](##Algolean.Algorithms.TMQuery.Computes.comp) composes two procedures and adds
  their time bounds.
* [Computes.space](##Algolean.Algorithms.TMQuery.Computes.space) bounds the number of cells
  added to the recorded tape range.
* [Computes.output_length_le](##Algolean.Algorithms.TMQuery.Computes.output_length_le) bounds
  the output length.
* [Computer.polyTimeComputable](##Algolean.Algorithms.Computer.polyTimeComputable) packages a
  procedure with its polynomial time bound.
* [EncodedComputer.polyTimeComputable](##Algolean.Algorithms.EncodedComputer.polyTimeComputable)
  does the same when the result is represented by a list of symbols.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
The program computes the specified function within the time allowed for each input. It must work
from any starting state label and records of tape use, preserve that label, and return
the head to its starting coordinate at the first output cell. The input and time bound describe
the required behavior; the program receives its input through the tape.
-/
def Computes (program : Prog (TMQuery tm) Unit) (f : List Symbol → List Symbol)
    (time : List Symbol → ℕ) : Prop :=
  ∀ input (s : TMState tm), s.config.BiTape = BiTape.mk₁ input →
    ∃ moves, Runs program s (BiTape.mk₁ (f input)) s.headPos moves ∧ moves ≤ time input

/-- The same computation proof remains valid when the allowed time is increased for every input. -/
theorem Computes.mono {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time time' : List Symbol → ℕ} (h : Computes p f time) (hle : ∀ x, time x ≤ time' x) :
    Computes p f time' := by
  intro input s hs
  obtain ⟨moves, hr, ht⟩ := h input s hs
  exact ⟨moves, hr, ht.trans (hle input)⟩

/--
The time bound also bounds the number of cells added to the recorded tape range. Cells counted
before the procedure starts remain part of the final total.
-/
theorem Computes.space {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time : List Symbol → ℕ} (h : Computes p f time) (input : List Symbol) (s : TMState tm)
    (hs : s.config.BiTape = BiTape.mk₁ input) :
    ∃ cost final, Completes p s cost final ∧ cost.steps ≤ time input ∧
      cost.cellsAllocated ≤ time input ∧
      final.cellsAllocated.card ≤ s.cellsAllocated.card + time input := by
  obtain ⟨moves, hr, ht⟩ := h input s hs
  obtain ⟨cost, final, hc, hcsteps, hcspace, htotal⟩ := hr.space
  exact ⟨cost, final, hc, by lia, by lia, by lia⟩

/--
Running the two procedures in sequence computes the second function on the first function's
output. The time required adds up, with the second procedure's time evaluated on that
intermediate output.
-/
theorem Computes.comp {p q : Prog (TMQuery tm) Unit} {f g : List Symbol → List Symbol}
    {time₁ time₂ : List Symbol → ℕ} (hp : Computes p f time₁) (hq : Computes q g time₂) :
    Computes (do p; q) (g ∘ f) (fun input => time₁ input + time₂ (f input)) := by
  intro input s hs
  obtain ⟨a, ⟨ca, t, hp, ht, hpos, hca⟩, ha⟩ := hp input s hs
  obtain ⟨b, ⟨cb, u, hq, hu, hup, hcb⟩, hb⟩ := hq (f input) t (by simp [ht])
  refine ⟨a + b, ⟨ca + cb, u, hp.seq hq, ?_, ?_, ?_⟩, Nat.add_le_add ha hb⟩
  · simpa [ht] using hu
  · simpa [hpos] using hup
  · simp [hca, hcb]

/--
One instruction increases the tape span counted by
[BiTape.spaceUsed](##Cslib.Turing.BiTape.spaceUsed) by at most its number of head moves. This
span counts the cell under the head and the stored cells on either side; it is used here to
bound output length.
-/
theorem step_tapeExtent_le (q : TMQuery tm α) (next : α → Prog (TMQuery tm) β)
    (s : TMState tm) :
    (step q next s).machine.config.BiTape.spaceUsed ≤
      s.config.BiTape.spaceUsed + (step q next s).cost.steps := by
  cases q with
  | move direction =>
    cases direction with
    | Left => simpa [step, BiTape.move] using BiTape.spaceUsed_move s.config.BiTape .left
    | Right => simpa [step, BiTape.move] using BiTape.spaceUsed_move s.config.BiTape .right
    | Stop => simp [step]
  | _ => simp [step]

/--
After a successful run, the tape span counted by
[BiTape.spaceUsed](##Cslib.Turing.BiTape.spaceUsed) is at most its initial span plus the number
of head moves.
-/
theorem execute_tapeExtent_le (fuel : ℕ) (p : Prog (TMQuery tm) α) (s : TMState tm)
    (result : AddWriter TMCost α) (final : ExecutionState tm)
    (h : execute fuel p s = some (result, final)) :
    final.machine.config.BiTape.spaceUsed ≤ s.config.BiTape.spaceUsed + result.tell.steps := by
  induction fuel generalizing p s result final with
  | zero =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next => simp only [FuelExecMonad.execute_zero_liftBind] at h; cases h
  | succ fuel ih =>
    cases p with
    | pure a =>
      simp only [FreeM.pure_eq_pure, FuelExecMonad.execute_pure,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    | liftBind q next =>
      simp only [FuelExecMonad.execute_liftBind_succ] at h
      cases hr : execute fuel (step q next s).program (step q next s).machine with
      | none => simp [hr] at h
      | some pair =>
        obtain ⟨r, u⟩ := pair
        have hrest := ih _ _ _ _ hr
        have hstep := step_tapeExtent_le q next s
        simp only [hr, Option.pure_def] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [TMCost.add_steps]
        omega

/--
The output length is at most one plus the input length plus the procedure's time bound. The
extra cell allows an empty input to become a one-symbol output without a head move.
-/
theorem Computes.output_length_le {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {time : List Symbol → ℕ} (h : Computes p f time) (input : List Symbol) :
    (f input).length ≤ 1 + input.length + time input := by
  obtain ⟨moves, ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, hc⟩, ht⟩ :=
    h input (TMState.init tm input) rfl
  have := execute_tapeExtent_le fuel _ _ _ _ hfuel
  simp only [hcfg, TMState.init_config, SingleTapeTM.initCfg, BiTape.spaceUsed_mk₁] at this
  lia

/--
This construction packages the procedure and its correctness proof as a
[TimeComputable](##Algolean.Algorithms.TMQuery.TimeComputable) record. Its time bound depends
only on the input length.
-/
def Computes.timeComputable {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {timeBound : ℕ → ℕ} (h : Computes p f (fun input => timeBound input.length)) :
    TimeComputable f where
  tm := tm
  program := p
  timeBound := timeBound
  outputsFunInTime input := by
    obtain ⟨moves, ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, hc⟩, ht⟩ :=
      h input (TMState.init tm input) rfl
    exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, hfuel, by simp [hcfg], by lia⟩

/--
This construction packages the procedure and its polynomial time bound as a
[PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable) record.
-/
def Computes.polyTimeComputable {p : Prog (TMQuery tm) Unit} {f : List Symbol → List Symbol}
    {poly : Polynomial ℕ} (h : Computes p f (fun input => poly.eval input.length)) :
    PolyTimeComputable f where
  toTimeComputable := h.timeComputable (timeBound := poly.eval)
  poly := poly
  bounds _ := le_rfl

/--
Two procedures can be composed with a polynomial time bound when each has a polynomial time
bound and the first output's length has a polynomial bound. The second procedure's polynomial is
evaluated at that output-length bound.
-/
theorem Computes.comp_polynomial {p q : Prog (TMQuery tm) Unit}
    {f g : List Symbol → List Symbol} {a b size : Polynomial ℕ}
    (hp : Computes p f (fun input => a.eval input.length))
    (hq : Computes q g (fun input => b.eval input.length))
    (hsize : ∀ input, (f input).length ≤ size.eval input.length) :
    Computes (do p; q) (g ∘ f) (fun input => (a + b.comp size).eval input.length) := by
  apply (hp.comp hq).mono
  intro input
  simpa using Nat.add_le_add_left (b.eval_mono (hsize input)) (a.eval input.length)

end Algolean.Algorithms.TMQuery

namespace Algolean.Algorithms.Computer

open Cslib.Turing TMQuery Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]
variable {f : List Symbol → List Symbol} {time : List Symbol → ℕ}

/--
This construction stores the program and an existing
[Computes](##Algolean.Algorithms.TMQuery.Computes) proof together as a
[Computer](##Algolean.Algorithms.Computer).
-/
@[simps program]
def ofComputes {p : Prog (TMQuery tm) Unit} (h : Computes p f time) : Computer tm f time where
  program := p
  correct input s hs := by
    obtain ⟨moves, ⟨cost, final, hc, ht, hp, hm⟩, hbound⟩ := h input s hs
    exact ⟨cost, final, hc, ht, hp, by lia⟩

/--
The stored program and correctness proof establish the
[Computes](##Algolean.Algorithms.TMQuery.Computes) statement for the same function and time
bound.
-/
theorem computes (machine : Computer tm f time) : Computes machine.program f time := by
  intro input s hs
  obtain ⟨cost, final, hc, ht, hp, hb⟩ := machine.correct input s hs
  exact ⟨cost.steps, ⟨cost, final, hc, ht, hp, rfl⟩, hb⟩

/--
The procedure's polynomial time bound supplies a
[PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable) record for the same
function.
-/
def polyTimeComputable {poly : Polynomial ℕ}
    (machine : Computer tm f (fun input => poly.eval input.length)) : PolyTimeComputable f :=
  machine.computes.polyTimeComputable

end Algolean.Algorithms.Computer

namespace Algolean.Algorithms.EncodedComputer

open Cslib.Turing TMQuery Polynomial

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
The same program and correctness proof satisfy a larger allowed time for every input. The
representation of inputs and outputs and the required final head position stay the same.
-/
@[simps program]
def mono {α β : Type} {ea : α → List Symbol} {eb : β → List Symbol} {f : α → β}
    {a b : α → ℕ} {position : α → ℤ → ℤ}
    (machine : EncodedComputer tm ea eb f a position) (bound : ∀ input, a input ≤ b input) :
    EncodedComputer tm ea eb f b position where
  program := machine.program
  correct input s hs := by
    obtain ⟨cost, final, hc, ht, hp, hb⟩ := machine.correct input s hs
    exact ⟨cost, final, hc, ht, hp, hb.trans (bound input)⟩

/--
This construction gives a [TimeComputable](##Algolean.Algorithms.TMQuery.TimeComputable) record
for the list of symbols representing the procedure's output. The head may finish at a different
recorded coordinate, provided it points to the first output cell.
-/
def timeComputable {β : Type} {outputEncoding : β → List Symbol} {f : List Symbol → β}
    {timeBound : ℕ → ℕ} {position : List Symbol → ℤ → ℤ}
    (machine : EncodedComputer tm id outputEncoding f (fun input => timeBound input.length)
      position) : TimeComputable (outputEncoding ∘ f) where
  tm := tm
  program := machine.program
  timeBound := timeBound
  outputsFunInTime input := by
    obtain ⟨cost, final, ⟨fuel, hfuel⟩, hcfg, _, ht⟩ :=
      machine.correct input (TMState.init tm input) rfl
    exact ⟨fuel, ⟨(), cost⟩, ⟨final, 0⟩, hfuel, by simp [hcfg], ht⟩

/--
The procedure's polynomial time bound gives a
[PolyTimeComputable](##Algolean.Algorithms.TMQuery.PolyTimeComputable) record for the list of
symbols representing its output.
-/
def polyTimeComputable {β : Type} {outputEncoding : β → List Symbol} {f : List Symbol → β}
    {poly : Polynomial ℕ} {position : List Symbol → ℤ → ℤ}
    (machine : EncodedComputer tm id outputEncoding f (fun input => poly.eval input.length)
      position) : PolyTimeComputable (outputEncoding ∘ f) where
  toTimeComputable := machine.timeComputable
  poly := poly
  bounds _ := le_rfl

end Algolean.Algorithms.EncodedComputer
