import VersoManual
import Solcore.Core.Safety
import Solcore.Core.FuelResumptionProperties

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Evaluation, safety, and fuel" =>
%%%
tag := "execution"
file := "execution"
%%%

The model describes evaluation twice. The declarative relation says what a
computation means. The machine says how to perform it one step at a time.
The correspondence theorems establish that these descriptions agree.

# A value and the store it leaves behind

{name Solcore.Core.Evaluates}`Evaluates` relates five things: an environment,
an initial local store, an expression, its result value, and its final store.
Read it as “in these inputs, this expression evaluates to this value and leaves
this store.” It describes successful evaluation, not a timeout or a raw fault.

{name Solcore.Core.State}`State` instead records the current expression or
returned value, a continuation of pending work, and the store. The environment
travels with expressions and saved frames. This is a CEK-style machine: the
continuation remembers what to do after the current computation finishes.
It is not the bounded operand stack of the EVM.

For `let x = true; x`, the machine visits these stages:

```
work                         environment    pending work
let true; var 0              []             finish
true                         []             bind, then var 0
returned true                               bind, then var 0
var 0                        [true]         finish
returned true                               finish
```

```lean
open Solcore.Core

def binding : Expr := .letE (.bool true) (.var 0)

example : runStateful 4 (State.initial binding) =
    .done (.bool true) [] := by
  rfl
```

We can connect this executable result to the declarative relation by applying
the soundness theorem, rather than constructing a separate evaluation proof:

```lean
example : Evaluates [] [] binding (.bool true) [] :=
  runStateful_evaluation_sound (fuel := 4) rfl
```

The four transitions move between the five rows. Inspecting a final state does
not require another transition's worth of fuel.

# Why trust the executor's answer?

{name Solcore.Core.runStateful_evaluation_sound}`runStateful_evaluation_sound`
says that a completed run from an initial state gives a declarative evaluation
with exactly the same value and final store. It does not require a separate
typing premise: a completed raw run must still obey the dynamic rules.

{name Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel}`evaluation_runStateful_complete_with_sufficient_fuel`
goes the other way. Given a declarative evaluation, there is a threshold such
that every fuel budget at least that large returns its value and store.
Together these theorems connect executable answers to the language rules.

{name Solcore.Core.evaluation_deterministic}`evaluation_deterministic`
then tells us that another successful evaluation from those same inputs cannot
produce a different value or store.

# What typing adds

{name Solcore.Core.well_typed_evaluates}`well_typed_evaluates`
assumes an expression typing, well-formed data definitions, a matching runtime
environment, and a matching local store. It guarantees an evaluation to a
value of the expected type and a well-typed final store, possibly with newly
allocated locations.

For closed expressions, the starting context and environment are empty.
{name Solcore.Core.closed_well_typed_runStateful_completes}`closed_well_typed_runStateful_completes`
establishes the existence of a successful fuel budget for this pure Core
boundary. This is a termination result as well as a type-safety result.
The restrictions on cells matter: allowing arbitrary function-valued mutable
cells would require revisiting the termination argument.

{name Solcore.Core.well_typed_runStateful_never_faults}`well_typed_runStateful_never_faults`
excludes raw machine faults under its runtime typing assumptions. It does not
exclude exhaustion of a budget that is too small. Host-enabled contract
execution has its own safety theorem, discussed in
{ref "contracts"}[the contract chapter].

# Exhaustion is a checkpoint

{name Solcore.Core.runStateful}`runStateful` distinguishes completion, a raw
fault, and exhaustion retaining an actual machine state. Exhaustion says the
budget did not finish this run. It does not prove divergence, reject the source
program, or describe EVM out-of-gas.

```lean
example : (match runStateful 3 (State.initial binding) with
    | .outOfFuel _ => true
    | _ => false) = true := by
  rfl
```

{name Solcore.Core.Steps.runStateful_done_iff}`Steps.runStateful_done_iff`
assumes a path of a known length to a final state. It proves that completion
occurs exactly when the fuel covers that length. The known final path is an
essential premise, not a conclusion inferred from a timeout.

{docstring Solcore.Core.runStateful_resume}

This resumption law is particularly useful: more time can continue the actual
checkpoint rather than replaying effects. Its premise requires the checkpoint
returned by the first run. A fresh initial state with the same remaining
budget is not interchangeable with it.
