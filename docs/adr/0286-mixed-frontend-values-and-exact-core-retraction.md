# ADR-0286: mixed frontend values and exact Core retraction

## Status

Accepted; a bounded value-representation foundation for future source closures.
Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`.
No old Core, Resolved, frontend evaluator, checker or source admission changes.

## Motivation and semantic boundary

ADR-0281 through ADR-0285 provide expected lambda typing and elaboration, with
generated-Core consumers. Their independent raw source interfaces still use
Core.Value and Core.Store. Merely adding a sum of an opaque Core.Value and a
source closure does not solve higher-order calls: an external Core closure cannot
receive a source closure argument through those old value-specific interfaces.

Introduce a separate recursive frontend value representation. Its Core-closure
variant carries the unchanged Core body but captures values of the new universe.
A future mixed evaluator could execute that body with a source-closure argument
directly, without an elaboration premise in a raw call rule. This phase provides
only the representation and exact Core embedding/projection laws, not that
evaluator, call rule, simulation, termination or runtime safety.

The fixed resolver keeps initializer lookup before the new let binding and
lambda parameters in a distinct scope (body_resolver.rs:40–55, 166–184).
The fixed specialization code retains lambda code and partially evaluates known
calls; a remaining direct Mono lambda is rejected by the generic emitter.
These facts justify retaining original lexical data and keeping backend claims
separate. They do not specify a general canonical runtime closure object.

## Value representation

Add `Solcore.Frontend.RuntimeValue`, a finite strictly positive datatype with all
ten existing Core.Value forms mirrored recursively: unit, Bool, Word, the exact
HostFunction enum, pair, Core closure, both sum injections with their original
other-side type tags, cell reference, and constructed data payload. Name the
Core-closure alternative `coreClosure`, preserving its parameter/result type
tags, unchanged Core.Expr body and ordered List RuntimeValue captures.

Add `sourceClosure` retaining the whole original Syntax.Expr, declaration owner,
ordered name-to-LocalId rows and ordered LocalId-to-RuntimeValue capture rows.
Use the underlying ordered list shapes where that avoids importing a resolver.
Keep every original span, parameter, annotation and body inside the single original
expression, without duplicated independently mutable syntax components.

This is inert code-and-capture data: a sourceClosure datum need not have a valid
unary lambda shape. A future raw creation/application rule must specify its actual
supported syntax; data construction here makes no admission or evaluation claim.
Retain duplicate spellings, duplicate/foreign IDs and misaligned rows literally.
Do not add a uniqueness, scope-alignment, well-formedness or validity requirement.

Do not attach a total Core type, inferred expected type, elaborated body,
checker proof or store snapshot to a source closure. Expected types are supplied
to a separate typing/elaboration judgment, not recovered from an unannotated raw
identity. Captured references are locations, not snapshots of their contents.

## Total embedding and structural partial projection

Provide `RuntimeValue.ofCore : Core.Value → RuntimeValue`, recursively preserving
all payloads, type tags, Core bodies, capture order and arbitrary captured values.
It accepts all old values, even values with ill-typed bodies/captures, unsupported
host behavior, invalid locations or unregistered nominal tags.

Provide `RuntimeValue.toCore? : RuntimeValue → Option Core.Value`. Mirror every
Core-shaped constructor recursively; return none for every sourceClosure without
checking, elaborating or otherwise translating its source. A sourceClosure nested
in a pair, sum, constructed payload or any Core-closure capture causes structural
projection failure even when that payload would be unused during execution.

Projection examines finite value subterms only. It never dereferences a cellRef:
the reference projects successfully even when an ambient store at that location
contains a sourceClosure. A whole raw store is simply a List RuntimeValue, whose
List.mapM projection fails if any actual slot is nonprojectable. Do not forbid
source closures in raw stores by using CellPayload, which restricts typed stores
only. No new public store/list abstraction is needed for this unit.

## Proofs and public surface

Prove the exact representation laws for arbitrary values with no semantic
premises: `toCore? (ofCore value) = some value`;
`toCore? value = some core ↔ value = ofCore core`; and injectivity of ofCore.
Successful projection is precisely the old-value image, so a source closure
cannot disappear or be replaced by an invented Core body.

Target six public declarations across RuntimeValue and RuntimeValueProperties:
the datatype, two functions and three laws. Keep list recursion/induction helpers
private and avoid new public equality, type-tag, validity or occurrence APIs.
No Eval, Safety, expected-lambda or checker import should be necessary.
Every new Lean file stays below 300 lines.

## Consumers and verification

Cover every old constructor, arbitrary closure code/type tags/captures, exact
source syntax and ordered shadow/duplicate/foreign metadata. Test nonprojectable
source closures inside both pair positions, sums, data, Core captures and raw
store slots. Contrast a projected cell reference with a nonprojectable store it
may point into. Construct only data and proof witnesses; do not call this raw
closure creation, application or canonical execution.

Run focused/aggregate/full tests, exact standard-only public and consumer axiom
catalogs, independent reviews, unchanged old bytes/headers/imports and kernel,
metadata, EOF and whitespace checks. Use separately verified small commits.

## Non-goals

No evaluator or source/Core operational correspondence, host/primitive adapters,
source closure compilation, value/runtime typing, world safety, store validation,
old entry-point admission changes or parser/diagnostic proofs.
