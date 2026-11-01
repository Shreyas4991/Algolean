/-
Copyright (c) 2026 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

module

public import Algolean.Algorithms.SingleTapeTuringMachines.Augmented
public import Algolean.Models.SingleTapeTM.Composition.Augment
public import Algolean.Models.SingleTapeTM.Composition.Computability

/-!
# Polynomial verification of input-certificate pairs

`P.onFirstWord` turns an existing decider into a verifier that ignores the certificate.
The adapter is an actual machine program: it erases the separator and certificate, returns to
the first input cell, and runs the original program with its tape symbols tagged.

`NP.ofP` uses this adapter with empty certificates. Both the input alphabet and the original
machine's finite control remain generic.
-/

@[expose] public section

namespace Algolean.Algorithms

open Cslib Cslib.Turing Polynomial TMQuery
open scoped TMQuery

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol]

namespace TMQuery

section FirstWord

/-- Include preparation time and enlarge the original bound to the encoded input's length. -/
private theorem firstWord_outputs {tm : SingleTapeTM Symbol} [DecidableEq Symbol]
    [DecidableEq tm.State] {p : Prog (TMQuery tm) Unit} {input : List (Augmented Symbol)}
    {output : List Symbol} {time : ℕ → ℕ} (mono : Monotone time)
    (h : OutputsWithinTime p (Augmented.firstWord input) output
      (time (Augmented.firstWord input).length)) :
    OutputsWithinTime (do [TMQuery tm.augment]
      SingleTapeTuringMachines.firstWord tm.augment
      augmentProg p) input (output.map Augmented.symbol)
      (2 * input.length + 4 + time input.length) := by
  apply ((SingleTapeTuringMachines.firstWord_computes
    (tm := tm.augment)).outputsWithinTime_seq h.augment).mono
  grind [Monotone]

attribute [local grind →] firstWord_outputs

/-- For defining the class NP we need to distinguish the input from the
certificate. For a generic alphabet, we do this using a dedicated constructor.
This saves us from dealing with encoding tricks.
Run a computation on the word before the first separator. Missing separators keep the
whole word. The program is fixed, and preparing the input is included in the time bound. -/
@[simps! tm program timeBound]
def TimeComputable.onFirstWord {f : List Symbol → List Symbol} (machine : TimeComputable f)
    (mono : Monotone machine.timeBound) :
    TimeComputable (fun input => (f (Augmented.firstWord input)).map Augmented.symbol) := by
  letI := machine.symbolDecidableEq
  letI := machine.stateDecidableEq
  exact {
    tm := machine.tm.augment
    program := do [TMQuery machine.tm.augment]
      SingleTapeTuringMachines.firstWord machine.tm.augment
      augmentProg machine.program
    timeBound n := 2 * n + 4 + machine.timeBound n
    outputsFunInTime input := by
      have := machine.outputsFunInTime (Augmented.firstWord input)
      grind }

end FirstWord

/-- Ignoring a certificate adds only linear preparation time to a polynomial-time machine. -/
noncomputable def PolyTimeComputable.onFirstWord {f : List Symbol → List Symbol}
    (machine : PolyTimeComputable f) :
    PolyTimeComputable (fun input => (f (Augmented.firstWord input)).map Augmented.symbol) where
  toTimeComputable := machine.polynomialBound.onFirstWord
    (fun _ _ h => machine.poly.eval_mono h)
  poly := 2 * X + 4 + machine.poly
  bounds _ := by simp [PolyTimeComputable.polynomialBound]

end TMQuery

/-- Make a verifier from a decider: prepare the first encoded word, then run the decider.
This is polynomial-time on every augmented input word, including malformed pair encodings. -/
theorem P.onFirstWord {L : Language Symbol} (h : P L) :
    P (fun input : List (Augmented Symbol) => L (Augmented.firstWord input)) := by
  obtain ⟨f, yes, ⟨machine⟩, hcorrect⟩ := h
  refine ⟨_, yes.map Augmented.symbol, ⟨machine.onFirstWord⟩, ?_⟩
  simpa using fun input => hcorrect (Augmented.firstWord input)

/-- `P ⊆ NP`: the encoded-pair verifier ignores the certificate; the empty certificate suffices. -/
theorem NP.ofP {L : Language Symbol} (h : P L) : NP L := by
  exact ⟨_, 0, h.onFirstWord, by simp⟩

end Algolean.Algorithms
