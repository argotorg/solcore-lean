# ADR-0023: Semantic Core vNext named algebraic data

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fifth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context

Binary products and sums can encode many data shapes, but they do not preserve
the identity of a user-declared data type or its constructors. The Core needs
that identity in order to represent recursive data, distinguish structurally
similar declarations, and execute exhaustive constructor matching.

Concrete type names, constructor spellings, nested patterns, wildcards, and
guards belong to a future resolved source language. They are likely to
change and are not needed by an evaluator after elaboration. The Core should
therefore receive a small normalized description of each data declaration
rather than source syntax.

## Decision

Each Core program has an immutable data-definition table. A `DataTypeId` is an
index into that program-local table. A constructor is identified by the pair
of its owning data type and its index within that type:

```text
DataTypeId    := table index
ConstructorId := (DataTypeId, constructor index)
```

These identities contain no source name, namespace, module path, or source
location. Two entries with the same shape remain different data types because
they occupy different table positions. An identity has meaning only together
with the table of the program that contains it.

Each constructor has exactly one payload type. A nullary source constructor is
normalized to a `unit` payload. Multiple source fields can later be normalized
to a product payload by an elaboration adapter. The Core itself does not
distinguish positional, tuple, or named source fields.

The internal Core adds three semantic concepts:

- a named-data type referring to a `DataTypeId`;
- construction from a `ConstructorId` and one payload expression; and
- exhaustive matching on a named-data value with one branch per constructor.

The exact Lean constructor names are an implementation detail. The observable
rules in this ADR are not.

## Definition-table validity

At the program boundary, the whole definition table is validated before the
body is accepted or an execution is claimed to be checked. A valid table
guarantees that:

- every named-data index referenced by a definition payload exists in the same
  table;
- every constructor payload is an admissible first-order type; and
- constructor order is fixed by the table and cannot change during execution.

Program checking separately guarantees that every constructor identity used by
an accepted body selects an existing constructor of its stated owner. It also
checks named-data indices in the declared result type and in reached expression
annotations.

Definitions may refer to themselves, to earlier entries, or to later entries.
This permits recursive and mutually recursive named data. Validation therefore
checks the table as one finite unit rather than requiring declaration-order
acyclicity.

The lower-level expression inference function checks the identities and
annotations reached by that expression but does not reject an unrelated bad
entry elsewhere in the table. The raw machine runner is likewise deliberately
unchecked: it exists to expose fault behavior and receives no definition table
at runtime. `Program.check` and the checked-execution safety results are the
boundary that combine whole-table validity, result-type validity, and body
typing. This is the same separation already used for other raw Core faults.

Constructor payloads exclude function types recursively. They may contain
unit, boolean, word, products, sums, other named-data types, and admissible
cell-reference types. A cell reference is admissible only when its element
type satisfies the existing `CellPayload` restriction. Thus a data value may
carry a local reference, but this ADR does not make a named-data value storable
inside a cell or admit function-valued cells.

The exclusion of functions keeps constructor data first-order. Recursive type
definitions describe finite runtime trees; they do not add recursive
evaluation or a way to construct an infinite value.

## Construction

Constructing a value evaluates the payload expression exactly once. It then
produces a value tagged with the selected `ConstructorId` and containing that
payload. The payload type must equal the payload type recorded for the
constructor, and the resulting expression type is the constructor's owning
named-data type.

A malformed constructor identity or a payload with the wrong type is rejected
by checking. Raw construction cannot validate the identity because the
definition table is erased before execution. If a malformed tagged value later
reaches a match, the unchecked machine can report an owner mismatch or an
invalid branch index. A well-typed program with a valid definition table cannot
reach either fault.

## Direct normalized matching

A match contains:

- one scrutinee expression;
- an explicit result type; and
- a branch list in the definition table's constructor order.

There must be exactly one branch for every constructor. Matching evaluates the
scrutinee exactly once, selects the branch at the runtime constructor's index,
and evaluates only that branch. In the selected branch, the constructor's
single payload is de Bruijn index zero; the surrounding lexical environment
follows it in its existing order. This rule also applies to a nullary
constructor, whose bound payload is `unit`.

Every branch must have the explicit result type. The result annotation is
required even when a data type has no constructors. An empty data definition
therefore admits a typed eliminator with an empty branch list, although no
well-typed closed value can inhabit that data type.

This is direct matching on already normalized constructor identities. It is
not source pattern matching. Branch selection is determined by the definition
table, not by textual arm order or a first-match policy.

## Evaluation, state, and totality

Payload construction and scrutinee evaluation thread the explicit local-cell
store in the same way as every other Core expression. Construction adds no
store effect of its own. A match passes the scrutinee's resulting store into
the selected branch, and effects in unselected branches do not occur.

Named data does not add recursive functions, loops, or any other recursive
evaluation rule. Values of recursive named types are finite constructor trees.
The implementation must re-establish total evaluation and sufficient fuel for
well-typed closed programs rather than assuming that recursive type identities
are structurally smaller Lean types.

## Program and version boundary

The definition table is part of the internal program supplied to checking.
Checked execution is justified using that validated table, but evaluation and
the CEK state erase it because constructor selection needs only the nominal tag
and normalized branch list already present in the expression. Existing Core
vNext programs without named data use an empty table. The table is immutable
and is not a runtime heap, contract state, ABI registry, or global namespace.

The raw `Program.run` compatibility entry point does not implicitly check a
program. Callers that require the language guarantee must check first or use a
proved checked-execution result. Keeping the raw runner separate is useful for
testing the structured faults of malformed machine states.

The generalized logical-reducibility and totality theorems take whole-table
well-formedness as an explicit premise. This is an intentional change to the
unpublished internal Lean proof API; it does not change any published wire or
serialization interface.

## Required implementation

- program-local definition-table, data-type, and constructor identities;
- executable table validation and an independent validity relation;
- named-data types and finite constructor values;
- declarative and executable typing for construction and matching;
- explicit data-type and constructor coordinates for definition errors, plus
  detailed expression paths for payloads, scrutinees, and branches;
- diagnostics for invalid identities, inadmissible payload types, payload type
  mismatches, non-data scrutinees, wrong constructor ownership, branch-count
  mismatches, and branch-result mismatches;
- store-threaded big-step construction and selected-branch evaluation;
- CEK frames and transitions preserving exactly-once evaluation;
- evaluator/machine correspondence and determinism;
- value, environment, store, frame, continuation, and state safety coverage;
- a termination argument that supports recursive and mutually recursive data;
- progress, preservation, typed results, total evaluation, sufficient fuel,
  and fault exclusion;
- weakening beneath each payload binder; and
- focused recursive, mutual, empty-data, order, effects, diagnostics,
  exact-fuel, and cell-reference tests.

## Deferred

This ADR does not add:

- source data-declaration or pattern syntax;
- source names, namespaces, constructor lookup, or resolution;
- nested patterns, tuple patterns, literal patterns, wildcards, aliases, or
  binders for selected subfields;
- guards, overlapping arms, non-exhaustive matches, default arms, or
  first-match ordering;
- source field labels, record update, derived methods, equality, or ordering;
- generic data parameters, polymorphism, class evidence, or staging;
- recursive functions, loops, divergence, or coinductive/infinite values;
- changing the existing admissible contents of local cells;
- ABI encoding, storage layout, public serialization, or contract-state
  meaning.

## Consequences

The Core can represent distinct, recursive user data and exhaustive branching
without depending on unstable source syntax. A future resolved adapter has a
clear normalization target: assign table identities, turn constructor fields
into one payload, order branches by the table, and compile richer patterns and
guards before entering the Core.

The safety and termination proofs can no longer recurse naively on the shape
of a named-data type because its table references may form cycles. They must
reason about finite runtime values and table validity explicitly. This is the
main proof obligation of the slice, not an observable restriction on recursive
or mutually recursive data declarations.
