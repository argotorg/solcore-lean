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

{includeDocstring Solcore.Core.Evaluates}

{includeDocstring Solcore.Core.State}

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

{includeDocstring Solcore.Core.runStateful_evaluation_sound}

{name Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel}`evaluation_runStateful_complete_with_sufficient_fuel`

{includeDocstring Solcore.Core.evaluation_runStateful_complete_with_sufficient_fuel}

{name Solcore.Core.evaluation_deterministic}`evaluation_deterministic`

{includeDocstring Solcore.Core.evaluation_deterministic}

# What typing adds

{name Solcore.Core.well_typed_evaluates}`well_typed_evaluates`

{includeDocstring Solcore.Core.well_typed_evaluates}

{name Solcore.Core.closed_well_typed_runStateful_completes}`closed_well_typed_runStateful_completes`

{includeDocstring Solcore.Core.closed_well_typed_runStateful_completes}

{name Solcore.Core.well_typed_runStateful_never_faults}`well_typed_runStateful_never_faults`

{includeDocstring Solcore.Core.well_typed_runStateful_never_faults}

Continue with {ref "contracts"}[host-enabled execution].

# Exhaustion is a checkpoint

{includeDocstring Solcore.Core.runStateful}

```lean
example : (match runStateful 3 (State.initial binding) with
    | .outOfFuel _ => true
    | _ => false) = true := by
  rfl
```

{name Solcore.Core.Steps.runStateful_done_iff}`Steps.runStateful_done_iff`

{includeDocstring Solcore.Core.Steps.runStateful_done_iff}

{docstring Solcore.Core.runStateful_resume}

Together these results explain how the four-step example can be paused after
three steps and then continued. The checkpoint keeps the pending work.
