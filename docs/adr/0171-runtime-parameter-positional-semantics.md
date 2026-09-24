# ADR-0171: Runtime parameter positional semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: proof-only connection from any source parameter position to checked execution

## Decision

Strengthen the existing canonical runtime parameter and explicit-entry proofs
without changing any executable adapter or supported source form. For an
independently bound parameter/argument list of length `n`, a parameter at source
index `k` and its supplied argument must correspond to declaration-local identity
`(owner, k)` and Core position `n - 1 - k`. Derive the necessary index bound from
the actual list lookup; do not interpret natural subtraction as permitting an
out-of-range index. Keep distinct arguments of the same type distinguishable.

Connect the existing ordered row and generated-identity facts to independent
name lookup, context/environment lookup, and positional lowering judgments.
The first-match rules require the already-proved unique parameter names and
identities; mere membership would not justify choosing a later duplicate.
Retain the exact source spelling and supplied argument type/value, including
arbitrary structurally typed closures and cell references. Do not introduce
runtime decoding, type coercion, allocation, or a new declaration identity policy.

## Semantic consumers

From the independent binding relation and matching source/argument lookups,
prove the canonical reference's exact resolution and elaboration to the Core
variable at `n - 1 - k`. Its independent value/store evaluation and source cost
return the supplied argument in one Core transition. Connect the same witness
through the single-return body and an explicit runtime entry whose independent
header return contract agrees with the argument type. Preserve all header,
arity, name, and type restrictions; a matching selected argument alone must
not accept an otherwise invalid declaration.

Expose exact fuel-zero initial-state behavior and one-transition completion,
or equivalent all-fuel bounds. The store is unchanged; structural cell-reference
typing does not establish allocation, and returning a closure does not apply it.
No general function-call cost or source local-variable mutability is decided.

## Validation

Use arbitrary-index independent proof consumers, mixed types, distinct same-type
values, and first/middle/last positions. Add generated complete-source regression
cases across several arities, checking every source index against actual Core
position, returned value, environment, and fuel boundary. These are finite tests
of the general theorem, not a new public program synthesis interface.

Audit all public declarations and register them, run focused and aggregate
builds, full tests, and kernel-policy and whitespace checks. Keep each new proof
file below 300 lines. Diagnostic proofs and all wire interfaces remain untouched.
