# ADR-0315: Owner transport of checked data-lambda Core images

## Status

Accepted.

## Context

ADR-0295 connects a checked unary data lambda to two exact Semantic Core
images. One theorem covers invocation of an already saved source closure after
actual caller-side callee and argument prefixes. The other covers direct
creation and application with the original argument resolution and lowering.

ADR-0314 reflects arbitrary endpoints of owner-mapped closed-source expression
and body evaluation to their original Core images. It does not yet transport
the expected-function checker used by the lambda theorems, nor package the
mapped checker, identifier and argument stages with the two application images.
Consumers would otherwise have to reconstruct those dependent premises by hand.

## Decision

Publish complete owner covariance for expected computation-lambda checking.
Given covariance of the child checker, injectively relabeling the owner and the
local type inputs returns exactly the same optional Core lambda. This is an
equality of the complete `Option`, so accepted terms keep the literal Core term
and type while every rejected term remains rejected.

The proof first transports the relational expected-lambda elaboration. Inferred
and explicitly typed parameters are handled separately so that the dependent
fresh-binder context is rewritten with the existing `bindFresh` owner law. The
computation-return tree is transported with its established covariance theorem.
The executable checker equality is then recovered from its graph
characterization, including the `none` case.

For saved invocation, require actual mapped callee and argument prefix
derivations. Reflect both prefixes through the injective owner map, invoke the
original checked-body image, and classify every arbitrary mapped complete-call
endpoint by the same Core body evaluation. The result also exposes mapped
checker success and exact mapped saved-environment/checker-context ID equality.

For direct application, retain the original checked lambda, ID alignment,
argument data gate, resolution and lowering. Return mapped checker success,
mapped ID equality, mapped argument resolution and literal old Core lowering,
then classify every arbitrary mapped endpoint by evaluation of the same direct
Core application. The argument and lambda Core expressions are unchanged by
owner relabeling.

Only injectivity is required. No inverse or surjectivity witness is constructed;
reflection recovers preimages only for values and stores actually observed at a
mapped evaluation endpoint.

## Independent checks

The symbolic consumer constructs old and mapped checker results, old and mapped
raw direct applications, old and mapped saved-call prefixes, both complete raw
calls and the Core paths before consuming the new bridges. It retains duplicate
and foreign-owner rows, a nonempty store, cell references, host functions and a
nested opaque Core closure under an injective nonsurjective owner shift.

Negative controls keep the important premises visible: a wrong expected type is
still rejected, reordered runtime rows do not satisfy checker ID alignment, a
lambda-valued body is outside the closed-data gate, and a source closure is not
manufactured into an embedded Core value by raw success.

Parsed direct-application and saved-invocation consumers are kept separate so
each proof file remains below 300 lines. Each preserves exact ASTs and spans,
EOF and empty diagnostics, independently runs old and mapped checkers and raw
evaluators, and constructs the Core result before invoking the corresponding
owner bridge.

## Preserved boundaries

Existing parsers, diagnostics, elaborators, raw evaluators, Core semantics,
resolution, lowering, owner maps, data gates and ADR-0295 interfaces are
unchanged. Checker covariance does not make an unsupported source admissible,
and raw evaluation does not manufacture checking, ID alignment, resolution,
lowering or a data-fragment proof.

No runtime typing or world/store validity, source-closure conversion, host/Core
dispatch, heap mutation, cost or fuel relation, failure taxonomy,
whole-language compilation, inverse mapping, surjectivity or unconditional
termination is claimed. Multiple or malformed parameters, unsupported bodies,
missing names and nonimage runtime payloads retain their existing boundaries.

Keep every proof file below 300 lines and every commit within 300 changed lines.
Verify exact import-only ports, public theorem types, actual declaration
ownership, complete consumers and standard public axioms.
