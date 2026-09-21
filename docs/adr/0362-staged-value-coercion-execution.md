# ADR-0362: Staged Core-representable coercion execution

## Status

Accepted for exact `Coerce<From, To>.coerce` paths encountered while evaluating
Core-representable staged values.  Coercions on marked-call arguments, marked
results, and expressions inside a staged callee now execute through the
authoritative selected implementation method.  The existing bare-`integer`
evaluator remains coercion-free, and this phase does not yet execute required
unary or binary operations or a directly invoked marked implementation method.

## Context

ADR-0358 through ADR-0361 established a bounded Unit/Bool/Word/product staged
carrier, authoritative marked-result direct calls, known marked inputs, and
proof-only predicate forwarding.  The evaluator nevertheless rejected every
typed expression node with a nonempty coercion path.  This left three ordinary
typing contexts disconnected from staging: conversion of a call argument to a
marked parameter, conversion of a marked result into its surrounding expected
type, and a conversion retained inside the staged callee itself.

Whole-program checking and ordinary runtime linking already supplied the
required authority.  Every coercion edge retains exact source and target types,
one primary `Coerce<From, To>` requirement followed by the selected `coerce`
method's requirements, and solved evidence.  The runtime linker validates that
metadata, selects and checks the unique method, and builds a capture-free
resolved application of its body.  Defining a second conversion semantics for
staging would risk disagreeing with both inference and runtime execution.

## Decision

### Reuse the authoritative coercion plan

For each staged coercion edge, the direct linker obtains the same checked plan
used by ordinary lowering.  Consequently staged execution inherits its checks
for:

- an exact closed `Coerce<From, To>` primary predicate and canonical witness;
- the exact primary-plus-method requirement identities in declaration order;
- equality of every solved predicate and evidence goal;
- forwarding of a unique concrete witness through nested generic assumptions;
- unique selection of the trait and implementation method named `coerce`; and
- exact one-input source type and one-result target type for the selected
  method.

Endpoints describe and validate the conversion; they never synthesize its
behavior.  The selected method body remains authoritative.

### Validate and apply the typed path in Source Core

Source Core removes the current node's coercions only while evaluating its
coercion-cleared base expression.  Before any step runs, the staged policy must
declare Core source and target endpoints equal to the typed path and an exact
consumed-requirement list equal to the edge's attached requirements.  The
evaluator then applies the checked steps in source order, checking the actual
carrier type before and after every step and finally checking the node's
authoritative post-coercion type.

Base-expression requirements are retained first, followed by each coercion
edge's requirements in path order.  They are reconciled once against the
owning caller or callee's solved-requirement table.  Requirements used while
checking and linking the detached implementation method remain in that
method's ledger; numerically equal local identities never migrate between
declarations.

The same policy is installed both while building a runtime-callee draft from
known marked inputs and while recursively evaluating a marked-result callee.
Argument, result, let/return, conditional, and nested generic contexts therefore
use one mechanism rather than context-specific conversions.

### Execute a closed typed method application

The staged input value is reified as a closed `Resolved.Expr` and inserted into
the capture-free application constructed by the ordinary coercion plan.  The
resulting term is independently lowered in the empty context and re-inferred
at the exact target Core type before execution.

Execution starts with an empty Core store and uses a structural bound computed
from the complete resolved term.  The bound includes both conditional branches
and the expanded cost of ordered Word less-than.  Out-of-fuel, a machine fault,
or a nonempty final store rejects the staged conversion.  A successful result
must project back into exactly Unit, Bool, canonical Word, or a recursively
supported product; closures, cells, sums, nominal data, and host functions stay
outside the carrier.

### Preserve the existing whole-program termination boundary

Detached method linking and nested staged calls receive the current active
specialization-key stack and the remaining decreasing link-depth fuel.  A
coercion does not create an independent whole-program recursion budget or
permit a call cycle.  The local structural execution bound applies only after
the finite resolved method application has been produced.

## Phase boundary

This phase does not add:

- coercions to the arbitrary-precision bare-`integer` staged evaluator;
- staged required unary or binary operations, including trait-backed operator
  dispatch;
- direct staged invocation of a marked implementation method;
- effectful or store-changing compile-time methods;
- indirect calls, function values, mutation, assignment, or place-sensitive
  staged environments;
- nominal constructors, mappings, proxies, indexing, or staged carriers beyond
  Unit, Bool, Word, and right-associated products;
- value-indexed specialization or cross-occurrence memoization;
- direct, mutual, or selected-branch-only recursion, or compile-time Fibonacci;
- automatic staged-root discovery or a public source Oracle; or
- broad soundness, completeness, and preservation metatheory.

Required unary/binary staging and marked implementation-method staging remain
the next evidence-execution slices.

## Verification target

End-to-end regressions execute the selected Bool-to-Word implementation method
in three positions.  A marked Bool result is converted to Word and materializes
`41`.  A Bool argument is converted to a marked Word parameter, the callee
returns marked Bool, and the surrounding result conversion materializes `7`.
A constrained generic relay forwards `Coerce<T, Word>` evidence through nested
marked calls before the callee-local conversion materializes `41`.

All three cases execute through the public whole-program preparation boundary
and preserve a nonempty caller-provided runtime store because conversion occurs
in an isolated empty staged store.  Existing path checks retain rejection of
wrong endpoints, missing, duplicate, reordered, or primary-only requirements,
predicate/evidence mismatch, malformed method signatures, execution faults,
store changes, and values outside the staged carrier.
