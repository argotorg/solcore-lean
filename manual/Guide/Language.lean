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

{name Solcore.Core.Ty}`Ty` includes unit, Boolean, Word, pairs, sums, functions,
local cells, and named data. Unit carries no interesting information. A pair
carries both components; a sum carries one of two alternatives with a tag.
Functions become closures containing a body and its captured environment.
A cell value refers to an entry in a separate local store.

{name Solcore.Core.Word}`Word` is a natural number less than `2^256`.
Addition, subtraction, and multiplication wrap at that boundary. Boolean
values remain distinct from Word-valued flags such as zero and one.

```lean
open Solcore.Core

example : Word.add Word.maximum
    (Word.ofNatModulo 1) = Word.zero := by
  decide

example : Word.udiv (Word.ofNatModulo 17)
    Word.zero = Word.zero := by
  decide
```

Division by zero is defined to produce zero. That result does not skip operand
evaluation: both operands still run in order. Signed operations interpret the
same 256 bits using the sign bit; they do not introduce a separate signed
runtime type. Logical shifts fill with zero, while arithmetic right shift
extends the sign. Oversized logical shifts produce zero.

For exact arithmetic definitions, inspect
{name Solcore.Core.Word.udiv}`Word.udiv`,
{name Solcore.Core.Word.shiftArithmeticRight}`Word.shiftArithmeticRight`, and
{name Solcore.Core.Word.sdiv}`Word.sdiv`. Byte selection counts from the most
significant byte. Modular addition and multiplication with an explicit modulus
use the mathematical intermediate result before reducing by that modulus;
ordinary wrapping addition followed by remainder is a different operation.

# Names become positions

Core variables use positions in an environment. Position zero is the newest
binding, position one the next, and so on. A `letE` first evaluates its
initializer, then puts the value at the front of the environment for its body.

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

Binary primitives and pairs evaluate left, then right. Function application
evaluates the function and then its argument. The function body receives the
argument followed by the closure's captured environment. A conditional first
evaluates its condition, then only the selected branch.

```lean
example : run 20 (State.initial
    (.ifE (.bool true) (.bool false) (.var 99))) =
    .done (.bool false) := by
  rfl
```

This raw expression runs because the bad variable is in the skipped branch.
It does not pass whole-expression checking. Checking examines both branches;
execution visits the selected branch. Neither fact contradicts the other.

Short-circuit Boolean builders expand to conditionals. Conversion builders
such as {name Solcore.Core.Expr.boolToWord}`Expr.boolToWord` use existing
expressions. A derived operation can have important laws without adding a
new machine instruction or wire tag. Its expansion must preserve operand
order and avoid evaluating an effectful operand twice.

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

A named-data match supplies branches in constructor-table order and an explicit
result type. Checking requires the normalized branch list to be exhaustive.
The selected branch receives the payload at position zero. Recursive data
definitions describe finite constructed values; they do not by themselves add
recursive functions or general looping.

A sum example chooses the left branch and makes its Boolean payload available
as `var 0`:

```lean
example : run 20 (State.initial
    (.caseE (.inLeft .word (.bool true))
      (.var 0) (.bool false))) = .done (.bool true) := by
  rfl
```

Source patterns, wildcards, guards, and arm reordering need their own frontend
translation. The Core match operation does not silently implement all of those
source conveniences.

# Local mutation

`newCell` allocates a typed cell, `loadCell` reads it, and `storeCell` updates it.
Closures capture references, so two closures can share a cell. Allocation and
mutation are visible in the explicit store passed through evaluation.
The {ref "state"}[state chapter] works through an example and distinguishes
this store from persistent contract storage.
