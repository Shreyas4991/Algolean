/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Models.SingleTapeTM.Composition.Component
public import Algolean.Models.SingleTapeTMSyntax

/-!
# Running procedures in sequence on the same machine

This file joins procedures that already use the same machine and its state names. The first
procedure finishes before the second begins. The second inherits the first procedure's tape,
state label, head position, and records of tape use. The time and storage costs add up.

The results combine proofs about individual procedures into proofs about the whole program. They
also cover adding a single write or move before or after a procedure.

[MachineComposition](Algolean/Models/SingleTapeTM/Composition/MachineComposition.html)
handles independently defined machines. It gives their states distinct names, sets the second
machine's initial state, and proves a combined bound in terms of the original input length.

## Main definitions and results

* [Completes.seq](##Algolean.Algorithms.TMQuery.Completes.seq) joins two completed executions
  and adds their costs.
* [Runs.seq](##Algolean.Algorithms.TMQuery.Runs.seq) combines proofs about the output tape, head
  position, and time.
* [Component.andThen](##Algolean.Algorithms.Component.andThen) joins procedures when the first
  establishes the conditions required by the second.
* [EncodedComputer.seq](##Algolean.Algorithms.EncodedComputer.seq) joins procedures whose
  representations of the intermediate result agree.
-/

@[expose] public section

namespace Algolean.Algorithms.TMQuery

open Cslib Cslib.Turing

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
The second procedure starts from the state left by the first. Their completed executions
combine, and their costs add up.
-/
theorem Completes.seq {p q : Prog (TMQuery tm) Unit} {s t u : TMState tm} {a b : TMCost}
    (hp : Completes p s a t) (hq : Completes q t b u) : Completes (do p; q) s (a + b) u := by
  obtain ⟨fuel, hp⟩ := hp
  obtain ⟨extra, hq⟩ := hq
  refine ⟨fuel + extra, ?_⟩
  simp [FuelExecMonad.execute_add_fuel fuel extra p s _ _ hp, hq]


/--
The two procedures run in sequence, using the actual intermediate state. Their proofs of the
output tape, head position, and execution time combine.
-/
theorem Runs.seq {p q : Prog (TMQuery tm) Unit} {s : TMState tm}
    {first second : BiTape Symbol} {pos₁ pos₂ : ℤ} {time₁ time₂ : ℕ}
    (hp : Runs p s first pos₁ time₁)
    (hq : ∀ t : TMState tm, t.config = {s.config with BiTape := first} →
      t.headPos = pos₁ → Runs q t second pos₂ time₂) :
    Runs (do p; q) s second pos₂ (time₁ + time₂) := by
  obtain ⟨a, t, hp, ht, hpos, ha⟩ := hp
  obtain ⟨b, u, hq, hu, hup, hb⟩ := hq t ht hpos
  exact ⟨a + b, u, hp.seq hq, by simpa [ht] using hu, hup, by simp [ha, hb]⟩


section PrimitiveComposition

/--
A completed procedure can run before the given procedure if it preserves the state label. The
time required adds up.
-/
theorem Runs.prepend {p q : Prog (TMQuery tm) Unit} {s t : TMState tm} {a : TMCost}
    {output : BiTape Symbol} {pos : ℤ} {time : ℕ} (h : Runs q t output pos time)
    (hp : Completes p s a t) (hc : t.config.state = s.config.state) :
    Runs (do p; q) s output pos (a.steps + time) := by
  obtain ⟨b, u, hq, ht, hpos, hb⟩ := h
  exact ⟨a + b, u, hp.seq hq, by simpa [hc] using ht, hpos, by simp [hb]⟩

/--
A write can run before the given procedure. The proof uses the tape after that write, and the
write adds no head moves.
-/
theorem Runs.prepend_write {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {a : Option Symbol} {output : BiTape Symbol} {pos : ℤ} {time : ℕ}
    (h : Runs p (s.write a) output pos time) :
    Runs (do FreeM.lift (.write a); p) s output pos time := by
  simpa using h.prepend (completes_write s a) rfl

/--
A move can run before the given procedure. It adds one time step and updates the records of tape
use.
-/
theorem Runs.prepend_move {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {direction : Dir} {output : BiTape Symbol} {pos : ℤ} {time : ℕ}
    (h : Runs p (s.move direction) output pos time) :
    Runs (do FreeM.lift (.move direction); p) s output pos (1 + time) := by
  simpa [TMState.moveCost] using h.prepend (completes_move s direction) rfl

/--
A write can run after the given procedure. It changes the output tape without adding a head
move.
-/
theorem Runs.append_write {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {output : BiTape Symbol} {pos : ℤ} {time : ℕ} (h : Runs p s output pos time)
    (a : Option Symbol) : Runs (do p; FreeM.lift (.write a)) s (output.write a) pos time := by
  obtain ⟨c, t, hp, ht, hpos, hc⟩ := h
  refine ⟨c, t.write a, ?_, ?_, hpos, hc⟩
  · simpa using hp.seq (completes_write t a)
  · simp [TMState.write, ht, BiTape.write]

/--
A move can run after the given procedure. The proof describes the resulting tape and head
position, and the move adds one time step.
-/
theorem Runs.append_move {p : Prog (TMQuery tm) Unit} {s : TMState tm}
    {output : BiTape Symbol} {pos : ℤ} {time : ℕ} (h : Runs p s output pos time)
    (direction : Dir) :
    Runs (do p; FreeM.lift (.move direction)) s
      (match direction with
        | .Left => output.moveLeft
        | .Right => output.moveRight
        | .Stop => output) (pos + direction.offset) (time + 1) := by
  obtain ⟨c, t, hp, ht, hpos, hc⟩ := h
  refine ⟨c + t.moveCost direction, t.move direction, hp.seq (completes_move t direction),
    ?_, by simp [hpos], by simp [TMState.moveCost, hc]⟩
  cases direction <;> simp [TMState.move, ht]

end PrimitiveComposition

end TMQuery

end Algolean.Algorithms

namespace Algolean.Algorithms.Component

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
Two components run in sequence when the first establishes the conditions required by the second.
The resulting proof records both executions and their combined cost. The input indices are used
in the proof; both programs stay fixed.
-/
@[simps program]
def andThen {ι κ : Type} {pre : ι → TMState tm → Prop}
    {post : ι → TMState tm → TMCost → TMState tm → Prop}
    {nextPre : κ → TMState tm → Prop}
    {nextPost : κ → TMState tm → TMCost → TMState tm → Prop}
    (first : Component tm pre post) (second : Component tm nextPre nextPost) (index : ι → κ)
    (compatible : ∀ i s cost t, pre i s → post i s cost t → nextPre (index i) t) :
    Component tm pre (fun i s cost final => ∃ a middle b,
      cost = a + b ∧ post i s a middle ∧ nextPost (index i) middle b final) where
  program := do [TMQuery tm]
    first.program
    second.program
  correct i s hs := by
    obtain ⟨a, t, ha, hp⟩ := first.correct i s hs
    obtain ⟨b, u, hb, hq⟩ := second.correct (index i) t (compatible i s a t hs hp)
    exact ⟨a + b, u, ha.seq hb, a, t, b, rfl, hp, hq⟩

end Algolean.Algorithms.Component

namespace Algolean.Algorithms.EncodedComputer

open Cslib Cslib.Turing TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
The two programs run in sequence when the first output and second input use the same
representation on tape. Their time bounds add up on the actual intermediate value.
-/
@[simps program]
def seq {α β γ : Type} {ea : α → List Symbol} {eb : β → List Symbol} {ec : γ → List Symbol}
    {f : α → β} {g : β → γ} {a : α → ℕ} {b : β → ℕ}
    {pa : α → ℤ → ℤ} {pb : β → ℤ → ℤ}
    (first : EncodedComputer tm ea eb f a pa) (second : EncodedComputer tm eb ec g b pb) :
    EncodedComputer tm ea ec (g ∘ f) (fun input => a input + b (f input))
      (fun input origin => pb (f input) (pa input origin)) where
  program := do [TMQuery tm]
    first.program
    second.program
  correct input s hs := by
    obtain ⟨ca, t, hp, ht, hpos, ha⟩ := first.correct input s hs
    obtain ⟨cb, u, hq, hu, hup, hb⟩ := second.correct (f input) t (by simp [ht])
    exact ⟨ca + cb, u, hp.seq hq, by simpa [ht] using hu, by simpa [hpos] using hup,
      by simpa using Nat.add_le_add ha hb⟩

/-- Changing the parentheses around three programs in sequence leaves their program unchanged. -/
theorem seq_assoc {α β γ δ : Type}
    {ea : α → List Symbol} {eb : β → List Symbol} {ec : γ → List Symbol} {ed : δ → List Symbol}
    {f : α → β} {g : β → γ} {h : γ → δ} {a : α → ℕ} {b : β → ℕ} {c : γ → ℕ}
    {pa : α → ℤ → ℤ} {pb : β → ℤ → ℤ} {pc : γ → ℤ → ℤ}
    (first : EncodedComputer tm ea eb f a pa) (second : EncodedComputer tm eb ec g b pb)
    (third : EncodedComputer tm ec ed h c pc) :
    ((first.seq second).seq third).program = (first.seq (second.seq third)).program := by
  simp [bind_assoc]

end Algolean.Algorithms.EncodedComputer

namespace Algolean.Algorithms.Computer

open Cslib Cslib.Turing TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]
variable {tm : SingleTapeTM Symbol} [DecidableEq Symbol] [DecidableEq tm.State]

/--
This program leaves the tape, head position, control label, and cell histories unchanged.
It makes no head moves.
-/
@[simps program]
def identity : Computer tm id (fun _ => 0) where
  program := pure ()
  correct _ s hs := by
    simp only [id_eq] at hs
    exact ⟨0, s, completes_pure s, by simp [← hs], rfl, le_rfl⟩

/-- Running the identity before a program leaves that program unchanged. -/
theorem identity_seq {f : List Symbol → List Symbol} {time : List Symbol → ℕ}
    (machine : Computer tm f time) :
    (EncodedComputer.seq (identity (tm := tm)) machine).program = machine.program := by simp

/-- Running the identity after a program leaves that program unchanged. -/
theorem seq_identity {f : List Symbol → List Symbol} {time : List Symbol → ℕ}
    (machine : Computer tm f time) :
    (EncodedComputer.seq machine (identity (tm := tm))).program = machine.program := by simp

/-- This notation runs two verified programs in sequence, from left to right. -/
scoped infixr:55 " ≫ₜ " => EncodedComputer.seq

end Algolean.Algorithms.Computer
