# Reusable single-tape Turing machine templates

The definitions in this folder build Query programs from fixed Lean arguments. For example,
`appendBit tm bit` builds instructions that append the chosen bit, and
`checkPrefix tm yes no expected` builds instructions that compare the tape with a chosen word.
We call these definitions **meta TMs** because they construct programs that can be included in
another Turing machine.

A template becomes part of one machine after its arguments have been fixed. Its parameters
describe the instructions to construct. The input to the resulting machine is the word on its
single tape.

## Fixed arguments and changing tape contents

Choose the alphabet, control states, comparison words, symbols, polynomials, and other program
arguments once for the containing machine. Those choices must stay the same for every input
and every input length. For example:

- `writeRight tm word` writes a fixed word. It does not read a word-valued Lean argument during
  execution.
- `moveCells tm direction count` contains a fixed number of move instructions. A count that
  depends on the current input must instead be represented on the tape and processed by a loop.
- `writePolynomial tm symbols word p` fixes the polynomial and the repeated word. Its running
  program reads the input length from the tape to determine how many copies to write.
- `forUnary tm zero one tick unitTail action` fixes one action and the word representing each
  unit. The count and position counter stay on the tape. The same action runs at every position.

Lean allows a function to choose different template arguments for different inputs. That would
describe a family of programs, rather than one machine computing on all inputs. The template's
type alone does not prevent this mistake. A final construction must fix one `Prog` independently
of the input; correctness and time theorems then quantify over its possible input words.

Tape tests can choose between fixed programs during execution. A finite alphabet also lets a
program contain one case for each symbol and select the appropriate case by inspecting the
scanned cell. Both constructions give one fixed program. A counter or an input-dependent state
number stays on the tape; it does not become a new Lean argument to a program constructor.

## Building one fixed program

This example fixes a Boolean tape alphabet and a single control state. It appends `false` if
the first input bit is `true`, and appends `true` otherwise, including on empty input.

```lean
module

import Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs.Transformations
import Algolean.Models.SingleTapeTM.Compiler.Basic

open Cslib Cslib.Turing
open Algolean.Algorithms Algolean.Algorithms.SingleTapeTuringMachines
open scoped TMQuery

namespace Example

abbrev control : SingleTapeTM Bool where
  State := Unit
  q₀ := ()
  tr _ symbol := (⟨symbol, none⟩, none)

def program : Prog (TMQuery control) Unit := do [TMQuery control]
  ifₜ tape =ₜ some true then
    appendBit control false
  else
    appendBit control true

noncomputable def compiled : SingleTapeTM.Description Bool :=
  TMQuery.Compiler.compile program

end Example
```

`program` has no Lean arguments. Every input is processed by those same instructions, and the
conditional reads the tape during execution. `control` fixes the available control states;
the Query program describes the actions. `Compiler.compile program` constructs a transition
table that executes those actions. Its correctness and time theorems are in
[`Compiler/Basic.lean`](../../../Models/SingleTapeTM/Compiler/Basic.lean).

For another algorithm, fix its alphabet and finite control states, choose its template
arguments, and compose the resulting programs with sequencing, tape or state conditionals,
and loops. The `tm` argument must be the containing machine so that all its instructions use
the same alphabet and control states.

## Proving correctness and time bounds

Each template has correctness theorems describing its tape changes, final head position, and
cost. Check their assumptions before composing templates. Some require an otherwise blank
tape; others preserve neighboring words separated by blanks. All regions are parts of the
same physical tape.

Each public program has a public `@[spec]` theorem. Use these specifications to compose proofs
with `vcgen`: open `scoped TMQuery.Spec Std.WP` and enable `experimental.vcgen`. State what is
true before and after the program using `⦃ precondition ⦄ program ⦃ postcondition ⦄`. A call to
`vcgen [program, child_spec ...]` uses the child program's specification and leaves the tape
and arithmetic facts to prove. The tape descriptions, head coordinates, and elapsed costs in
a specification are proof arguments; they do not become arguments to the running program.

The existing execution theorems remain useful when an execution itself is needed. `Runs`
describes a completed computation that preserves the control state, with an exact tape, head
position, and number of head moves. `Completes` also allows the control state to change.
`Spec.runs` and `Spec.completes` derive these statements from Hoare-style proofs. `Computer`
and `EncodedComputer` combine a program with its correctness and time proofs;
`PolyTimeComputable` records a polynomial time bound.

For a complete program, `TMSolves` states correctness and time and total space bounds on every
input word. The final tape contains exactly an allowed output word, with its first cell under
the head and blanks everywhere outside the word. This follows CSLib's output convention.
The final head need not be at the original input position. `TMQuery.ComputesWithin` specifies the output as a
function of the input. `TMQuery.DecidesWithin` requires a fixed acceptance word exactly on yes
inputs. These predicates are defined in `Models/SingleTapeTM/Solves`.
The computation records in `Models/SingleTapeTM/Computability` store this word-computation
statement in their `computesWithin` field. Their `outputsFunInTime` accessor derives the
per-input execution statement when a compiler or composition proof needs it.

The Query cost counts head moves. Compilation gives a transition-count bound with a constant
factor and an additive constant, both fixed by the chosen program and alphabet. These constants
are independent of the input and its length.

## Finding a building block

| Modules | Contents |
| --- | --- |
| `Basic`, `BitOperations`, `Transformations` | Primitive writes, bit flips, appending, and complementation. |
| `Scanning`, `Gaps`, `Regions` | Moving within a word, across blanks, and between neighboring regions. |
| `Reading`, `Comparison`, `FiniteState` | Comparing fixed words and reading symbols while updating control states. |
| `Writing`, `Erasing`, `Expanding` | Writing or erasing words and making room for inserted symbols. |
| `Increment` | Binary counters that grow to the right or left. |
| `Copying`, `Framed`, `Augmented` | Copying words, transforming one word of a pair, and keeping a prefix before a separator. |
| `SymbolEncoding`, `PolynomialWriter`, `PolynomialFields`, `Serialization` | Replacing symbols and writing fixed words or polynomially many copies. |
| `CertificatePadding` | Removing padding from an encoded certificate. |
| `BasicTMs` | Packaged correctness and polynomial time results for basic Boolean programs. |

Import a module through `Algolean.Algorithms.SingleTapeTuringMachines.MetaTMs`. Declaration
names remain in their existing namespaces, including `SingleTapeTuringMachines`, `Copying`,
and `PolynomialWriter`. The SAT verifier is in the parent's `SAT` subfolder.
The Boolean pair encoding is in `Problems/Encodings/Pairing.lean`.
Its program composition API is in `Models/SingleTapeTM/Composition/Pairing.lean`.
