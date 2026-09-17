import VersoManual
import Solcore.Core.Machine
import Solcore.Core.Conversions

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Values, bindings, and expression meaning" =>
%%%
tag := "core-language"
file := "core-language"
%%%

Semantic Core is a small typed expression language. It gives us a stable place
to explain computations independently of source spelling, module names, or a
compiler's intermediate representation. Core syntax below is Lean notation
for that model, not Solcore source syntax.

# Values and types

{includeDocstring Solcore.Core.Ty}

{includeDocstring Solcore.Core.Word}

```lean
open Solcore.Core

example : Word.add Word.maximum
    (Word.ofNatModulo 1) = Word.zero := by
  decide

example : Word.udiv (Word.ofNatModulo 17)
    Word.zero = Word.zero := by
  decide
```

{name Solcore.Core.Word.udiv}`Word.udiv`

{includeDocstring Solcore.Core.Word.udiv}

{name Solcore.Core.Word.shiftArithmeticRight}`Word.shiftArithmeticRight`

{includeDocstring Solcore.Core.Word.shiftArithmeticRight}

{name Solcore.Core.Word.byteAt}`Word.byteAt`

{includeDocstring Solcore.Core.Word.byteAt}

{name Solcore.Core.Word.addMod}`Word.addMod`

{includeDocstring Solcore.Core.Word.addMod}

# Names become positions

{includeDocstring Solcore.Core.Expr}

Here is a nested binding example:

```lean
def olderBinding : Expr :=
  .letE (.bool true)
    (.letE (.bool false) (.var 1))

example : run 20 (State.initial olderBinding) =
    .done (.bool true) := by
  rfl
```

Inside the inner body, the environment is `[false, true]`. Asking for `var 1`
therefore retrieves the earlier value. The new binding is not in scope in its
own initializer. The {ref "frontend"}[frontend chapter] explains how stable
source identities become these positions without confusing shadowed names.

# Evaluation order is part of the meaning

The expression rules above distinguish checking both branches from executing
only one. We can observe that distinction even in an unchecked expression:

```lean
example : run 20 (State.initial
    (.ifE (.bool true) (.bool false) (.var 99))) =
    .done (.bool false) := by
  rfl
```

This raw expression runs because the bad variable is in the skipped branch.
It does not pass whole-expression checking. Checking examines both branches;
execution visits the selected branch. Neither fact contradicts the other.

{name Solcore.Core.Expr.boolToWord}`Expr.boolToWord`

{includeDocstring Solcore.Core.Expr.boolToWord}

A derived operation can have useful laws without adding a new machine
instruction or wire tag. The expansion is the implementation to reason about.

# A closure remembers its binding

Here a function captures `true`, then runs inside a scope with a newer `false`
binding. Its body still sees the captured value. Position zero in the body is
the function argument; position one is the captured value.

```lean
def capturedBinding : Expr :=
  .letE (.bool true)
    (.letE (.lambda .unit .bool (.var 1))
      (.letE (.bool false) (.apply (.var 1) .unit)))

example : run 30 (State.initial capturedBinding) =
    .done (.bool true) := by
  rfl
```

# Structured data

Products support first and second projections. A sum case selects the branch
for its tag and binds the payload at position zero. Named data extends this
idea with a program-owned table of data definitions and constructor payload
types. Constructor identities include their owning data type.

{includeDocstring Solcore.Core.Expr.matchData}

A sum example chooses the left branch and makes its Boolean payload available
as `var 0`:

```lean
example : run 20 (State.initial
    (.caseE (.inLeft .word (.bool true))
      (.var 0) (.bool false))) = .done (.bool true) := by
  rfl
```

# Local mutation

`newCell` allocates a typed cell, `loadCell` reads it, and `storeCell` updates it.
Closures capture references, so two closures can share a cell. Allocation and
mutation are visible in the explicit store passed through evaluation.
The {ref "state"}[state chapter] works through an example and distinguishes
this store from persistent contract storage.
