# ADR-0314: Owner transport of the closed-source/Core image boundary

## Status

Accepted.

## Context

ADR-0293 and ADR-0294 relate every actual result of the closed data expression
and body fragments to evaluation of one checked Semantic Core expression. Their
strongest interfaces deliberately retain the complete original resolution,
lowering, shared body checking and exact runtime/context identity premises.

ADR-0311 transports successful closed-source evaluation through injective owner
maps, and ADR-0313 reflects every arbitrary observed mapped endpoint back to a
complete original endpoint. The published interfaces do not yet compose those
owner laws with the existing source/Core image boundary. A caller must otherwise
manually recover an old endpoint and reconnect it to the same Core term.

## Decision

Publish two representation laws. Mapping owners over an environment containing
embedded Core values changes its local keys but not any Core payload. Mapping
owners over an embedded Core store leaves the complete embedded store literal.
Neither law needs injectivity because Core values contain no source owner IDs.
Cell locations, Core closure bodies and captures, host functions and constructed
payloads are all retained rather than reconstructed through a partial projection.

For closed data expressions, combine injective owner reflection with the existing
whole-resolution/Core-image theorem. The new bridge takes the original resolution
and lowering as explicit premises. It returns resolution under mapped name IDs,
lowering of the renamed resolved expression to exactly the old positional Core
term, and an equivalence between every arbitrary actual mapped raw endpoint and
evaluation of that old Core term. Being an embedded Core value and complete store
is a conclusion on the forward direction, not an endpoint-shape premise.

For closed data bodies, retain the complete original shared-checker success and
exact equality between runtime environment IDs and checker context IDs. The bridge
returns checker success for the mapped owner and inputs with exactly the same
Core/type pair, mapped ID equality, and the corresponding complete actual-output
equivalence. Typed and inferred fresh binders therefore move only their owners;
their binder indices, source syntax, Core term and inferred type remain literal.

The proofs first rewrite embedded environments and stores into the general owner
map representation. They use ADR-0313 to recover a full old value and final-store
preimage, then apply the existing ADR-0293 or ADR-0294 image bridge. Runtime owner
mapping fixes the recovered Core images, so no inverse or onto map is constructed.
The reverse direction uses the old bridge followed by forward owner covariance.

## Independent checks

The expression consumer independently constructs old resolution, old lowering,
old raw evaluation, mapped raw evaluation and Core evaluation before invoking the
new theorem. A conditional with a short-circuit guard, tuple and strict addition
retains a nonempty Core store, nested Core closure captures, cell references, host
functions, duplicate rows, foreign owners and a nonsurjective owner shift.

The body consumer independently checks a typed then inferred let prefix followed
by an ordered Word match whose first literal misses and second literal wins. It
establishes old and mapped checker results, exact old and mapped ID equalities,
both raw paths and the Core path before using the bridge. Separate controls show
that raw success does not manufacture missing checker success, repair mismatched
IDs or turn a source closure into a Core image.

A parsed consumer retains exact complete ASTs, thirty-one source spans, EOF and
empty diagnostics for an expression and body. It runs both old and mapped source
paths, resolution/lowering/checking and an independent Core machine result before
consuming both bridges. Typed/inferred fresh IDs, literal and wildcard branches,
duplicate and foreign rows, a three-element store and a nonsurjective shift remain
observable in the complete endpoints.

## Preserved boundaries

Existing evaluators, owner maps, resolution, lowering, checking, Core semantics,
data gates, six image interfaces, parser and diagnostics are unchanged. The new
laws do not make a data gate imply success and do not turn a raw derivation into
whole compilation without the original whole-stage premises.

No runtime typing or world/store validity, source-closure conversion, host/Core
dispatch, heap mutation, cost or fuel relation, failure classifier, whole-language
compilation, arbitrary mixed-environment Core image, inverse mapping, surjectivity
or unconditional termination is claimed. Unsupported or unresolved skipped syntax,
absent runtime IDs and nonimage payloads keep their existing separate boundaries.

Keep every proof file below 300 lines and every commit within 300 changed lines.
Verify exact import-only ports, public types, actual declaration ownership,
transitive dependency hashes, complete consumers and standard public axioms.
