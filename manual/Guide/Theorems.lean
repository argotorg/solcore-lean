import VersoManual
import Solcore.Core.Eval
import Solcore.Core.Check

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Reading a theorem without reading its proof" =>
%%%
tag := "reading-theorems"
file := "reading-theorems"
%%%

A theorem is a reusable promise with conditions. To understand it, ask:
what objects does it range over, what must already be true, and what does it
then guarantee? The proof explains why the promise holds; the statement tells
you when you may use it.

# A small vocabulary

: Soundness

  Every successful executable answer satisfies the specification. A checker
  that accepts a program does not accept a program outside its typing rules.

: Completeness

  Every case described by the specification is covered by the implementation,
  subject to the theorem's conditions. For an evaluator this often means
  “there exists enough fuel,” not “every supplied budget succeeds.”

: Determinism

  With the same specified inputs, two outcomes of the relation must agree.
  Changing the world, environment, or profile changes the inputs.

: Preservation

  A property survives a step or a complete execution. Type preservation says
  evaluation does not turn a well-typed value into a value of the wrong type.

: Progress

  A properly formed state has a permitted next action. For a host-aware
  machine, requesting a host operation is progress too.

: Correspondence

  Two descriptions agree through an explicit relation: a checker and typing
  rules, a machine and evaluation rules, or named and positional expressions.

# Read the arrows

Lean writes `P → Q` for “if P, then Q,” `P ↔ Q` for both directions, and
`∃ x, P x` for “there exists an x satisfying P.” An equality compares the
whole values on its two sides. If a result includes a final store, equality
includes that store, not just the returned number.

For example, here is the source documentation of the checker equivalence:

{docstring Solcore.Core.Program.checkDetailedIn_iff_wellTyped}

The `↔` in its statement is the signal to look for both directions. Compare
that with a uniqueness result:

{docstring Solcore.Core.evaluation_deterministic}

# Follow the assumptions all the way down

A typed context lists the types available to an expression. To run an open
expression, the actual environment must supply values of those types. If
values contain cell references, the local store must also match its typing.
A theorem about typed states is not a theorem about arbitrary raw machine
states assembled by hand.

Likewise, a theorem beginning with a successful lowering equation only applies
when that lowering succeeds. A theorem about a known terminating path can
calculate its exact fuel threshold without proving every possible computation
terminates.

# Examples and general guarantees

A checked example establishes one concrete claim. It is excellent for showing
an evaluation order or catching a stale explanation. A universally quantified
theorem establishes the property for every input covered by its assumptions.
Tests exercise implementations and interfaces; they do not turn a missing
universal theorem into an existing one.

The guide uses all three forms of evidence. Short Lean blocks show examples.
Named theorem discussions explain general guarantees. Wire fixtures exercise
published behavior. An English paraphrase remains something to review even
when its declaration reference is compiler-checked.
