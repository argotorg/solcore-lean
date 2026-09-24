# ADR-0022: Semantic Core vNext first-order local cells

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fourth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context

The Core can now represent products, non-recursive functions, lexical
closures, and binary sums, but every binding still denotes an immutable value.
Solcore also needs local mutation whose meaning does not depend on a particular
source spelling for mutable declarations or assignment.

Mutation cannot be implemented by changing a captured host-language value in
place. The evaluator, machine, and proofs must expose the state that changes.
Stable cell identities are also required so that two closures capturing the
same local cell observe each other's writes.

Allowing arbitrary values in cells would introduce recursion earlier than the
roadmap intends. For example, a closure can capture a cell, store a closure
that calls the contents of that cell, and then call itself through the cell.
That program can diverge without a recursive Core expression. The first cell
slice must therefore exclude higher-order and nested cell contents so that the
current total-evaluation and sufficient-fuel claims remain meaningful.

## Decision

The internal Core adds the following forms:

```text
Ty.cell elementType

Expr.newCell elementType initializer
Expr.loadCell reference
Expr.storeCell reference value

Value.cellRef elementType location

Location := Nat
Store := List Value
StoreTyping := List Ty
```

A `location` is a natural-number index into an explicit local `Store`. A cell
reference retains its element type so that `Value.type` remains computable
without reading the store. This annotation is checked by the static and safety
layers; it does not make cell identity or cell equality a Core operation.

The store is append-only with respect to allocation. Evaluating a successful
`newCell` appends one entry and returns the index that entry received. Existing
locations are never reused or renumbered. A write replaces the value at an
existing location but does not change the store's length or its store typing.
There is no deallocation or observable garbage collection in this slice.

The runtime environment remains a list of values. A closure captures that
environment, which may contain cell references, but it does not capture or
copy the store. All evaluation within one program threads one explicit store,
so closures that contain the same reference share the same cell.

## Admissible cell contents

The predicate `CellPayload` is the least predicate satisfying:

```text
CellPayload unit
CellPayload bool
CellPayload word

CellPayload left and CellPayload right
  imply CellPayload (product left right)

CellPayload left and CellPayload right
  imply CellPayload (sum left right)
```

There is no `CellPayload` case for `function` or `cell`. The exclusion is
recursive: a product or sum containing a function or another cell is not an
admissible cell payload.

This still permits closures to capture, receive, and return cell references.
It only prevents closures and references from being stored inside cells. A
later recursion-and-divergence decision may deliberately relax this boundary
and replace the current termination claims.

## Static semantics

The three typing rules are:

```text
context |- initializer : elementType    CellPayload elementType
----------------------------------------------------------------
context |- newCell elementType initializer : cell elementType

context |- reference : cell elementType    CellPayload elementType
------------------------------------------------------------------
context |- loadCell reference : elementType

context |- reference : cell elementType
context |- value : elementType
CellPayload elementType
------------------------------------------------------------------
context |- storeCell reference value : unit
```

`storeCell` returns `unit`; assignment does not return the assigned value.
Executable inference, detailed checking, and declarative typing must agree on
the payload restriction and these result types.

These are Core operations, not source assignment syntax. A future elaborator
may represent a mutable source binding by binding a new cell, a read by
`loadCell`, and an assignment by `storeCell`. This ADR does not choose source
keywords, implicit dereferencing, lvalue syntax, or compound assignment rules.

## Dynamic semantics and evaluation order

Big-step evaluation becomes a store-threaded judgment:

```text
Evaluates environment inputStore expression value outputStore
```

The new operations behave as follows.

1. `newCell elementType initializer` evaluates `initializer` exactly once.
   Allocation happens only after that evaluation finishes, in the store it
   produced. The new location is that store's previous length.
2. `loadCell reference` evaluates `reference` exactly once and then reads the
   referenced location from the resulting store.
3. `storeCell reference value` evaluates `reference` exactly once first. It
   then evaluates `value` exactly once in the same lexical environment and in
   the store produced by the reference expression. Finally it updates the
   already selected location and returns `unit`.

Resolving the reference before the right-hand side is observable when either
subexpression allocates or mutates cells. An invalid reference stops before
the right-hand side begins.

Every existing compound expression threads the store through its
subexpressions in its already accepted order. In particular, pairs and binary
operations remain left-to-right, application remains callee then argument then
body, and conditionals and cases still evaluate only the selected branch. A
lambda captures its environment without changing the store.

The unchecked machine adds structured faults for a non-cell reference and an
invalid location. Store typing makes both faults unreachable from a
well-typed state. Cells are always initialized, so this slice has no
uninitialized-read state or fault.

## Store typing and safety

The safety layer uses an explicit `StoreTyping`, with one element type for
each store location. Runtime value, environment, closure, frame, and machine
state typing are indexed by that store typing.

Allocation extends the store typing by exactly one admissible element type.
Writing preserves it. Existing well-typed values and captured environments
remain well typed when a store typing is extended. Preservation may therefore
return a larger store typing together with evidence that it extends the input
typing.

The implementation establishes:

- executable/declarative checker soundness and completeness;
- deterministic value and final-store evaluation;
- CEK and big-step correspondence with the exact order above;
- store-typing preservation for allocation and update;
- progress, typed results, and cell-fault exclusion;
- total evaluation and sufficient fuel for `CellPayload`-restricted programs;
- weakening and logical-reducibility lemmas under store-typing extension; and
- computable structural equality for references and machine data.

The store is kept separate from `Value`. A closure contains location values,
not a store snapshot. This both preserves sharing and keeps structural value
equality finite and computable.

## Runner boundary

The internal stateful runner returns both the value and the final local store
on success. Its initial program entry point starts with an empty local store.
Returning the store is necessary because a result may itself be a cell
reference or a closure that contains one.

The existing `Program.run` interface remains as a compatibility wrapper. It
uses the stateful runner and erases the final local store from a successful
result.

## Boundary

Cell locations are local runtime identities. They are not contract-storage
keys, account addresses, ABI values, or public serialized identities.

## Alternatives considered

Lexical mutable binders and direct de Bruijn assignment were not chosen as the
Core primitive. They would require a mixed mutable/immutable binding context
and would still need stable locations for closure sharing. A later resolved
language can elaborate those source concepts into the cell operations fixed
here.

A separate stateful expression language was also not chosen. Keeping functions
in the existing pure Core would prevent their bodies from using local state;
lifting functions into a second language would duplicate the type, evaluator,
machine, and proof boundaries. A separate runtime layer remains appropriate
for external contract state.

## Deferred

This ADR does not add:

- a source spelling or source-to-Core elaborator;
- implicit dereferencing, lvalues, or compound assignment;
- uninitialized cells or default initialization;
- function-valued, cell-valued, or otherwise higher-order cell payloads;
- recursion or a semantics of divergence;
- reference equality, ordering, hashing, or serialization;
- deallocation, regions, garbage collection, borrowing, or concurrency;
- contract storage, accounts, balances, logs, calls, transactions, or
  rollback.

## Test coverage

Focused tests cover allocation identity, initializer-before-allocation,
reference-before-right-hand-side order, exactly-once evaluation, reads after
writes, aliases shared by multiple closures, rejected higher-order payloads,
invalid raw references, exact fuel, and final-store results. Existing Core
regression tests remain requirements.
