# ADR-0316: Owner transport of checked data-expression Core images

## Status

Accepted.

## Context

ADR-0314 proves that owner relabeling preserves the exact Core image of a
closed data expression when resolution and lowering are already available.
Its callers must nevertheless recover those stages from the executable local
expression checker and prove that the runtime environment has the same ordered
identifier layout as the checker context.

The checked unary and binary data bridges admitted by ADR-0297, ADR-0299 and
ADR-0301 all cross this same boundary. Publishing a separate owner theorem for
each logical-not, bit-not, short-circuit and strict-word form would duplicate
the checker, alignment, resolution, lowering and endpoint argument while
covering only individual constructors of `ClosedSourceDataExpression`.

## Decision

Publish one checked owner-transport theorem for every admitted closed data
expression. Given a successful local-expression check, exact ordered
environment/context identifier equality and an injective declaration-owner
map, the theorem returns all of the following together:

- the mapped executable checker succeeds with the literal old Core expression
  and type;
- the mapped runtime environment and checker context retain exact ordered
  identifier equality;
- one original resolved-expression witness with its environment-relative
  lowering;
- mapped resolution of the renamed witness and lowering to the literal old
  Core expression; and
- an equivalence between every arbitrary mapped raw endpoint and evaluation of
  that original Core expression in the original Core environment and store.

The resolution witness comes from checker soundness. Original context-relative
lowering is rewritten across the exact identifier equality. ADR-0314 then
transports the resolution and lowering stages and reflects arbitrary mapped
endpoints through the injective owner map. Complete checker covariance supplies
the mapped `Option` equality independently.

The general theorem deliberately keeps the `ClosedSourceDataExpression` gate
as an explicit premise. Its twelve constructors include references, literals,
groups, unit, pairs, tuples, conditionals, logical and bitwise unary forms,
boolean short-circuit forms and strict word binary forms. Constructor-specific
owner wrappers are therefore unnecessary.

Only injectivity is required. No inverse or surjectivity witness is introduced;
reflection recovers preimages only for values and stores observed at an actual
mapped evaluation endpoint.

## Independent checks

A symbolic frontend consumer must instantiate the common theorem at both Bool
and Word expressions and construct old, mapped and Core evaluations before
using the endpoint equivalence. Its fixture retains an injective nonsurjective
owner shift, duplicate or foreign-owner rows, exact ordered identifiers and a
nonempty Core store containing opaque payloads.

Executable or parsed consumers may cover larger unary, short-circuit and strict
binary expressions, but they consume the same public theorem rather than new
constructor-specific APIs. Negative controls keep checker rejection, identifier
misalignment and expressions outside the closed-data gate observable.

## Preserved boundaries

Existing syntax, parsers, diagnostics, elaborators, raw evaluators, Core
semantics, owner maps, gates and ADR-0314 contracts are unchanged. Mapped raw
success alone does not manufacture checking, exact ID alignment, resolution,
lowering or fragment admission.

No runtime typing or world/store validity, source-closure conversion,
host/Core dispatch, heap mutation, cost or fuel relation, failure taxonomy,
whole-language compilation, inverse mapping, surjectivity or unconditional
termination is claimed.

Keep every proof file below 300 lines and every commit within 300 changed
lines. Verify exact import-only ports, public theorem types, actual declaration
ownership, representative consumers and standard public axioms.
