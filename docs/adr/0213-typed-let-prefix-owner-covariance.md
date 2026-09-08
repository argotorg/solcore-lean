# ADR-0213: Typed let-prefix owner covariance

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Fresh allocation, value-free provenance and full checked body results

## Decision

Simultaneously relabel declaration owners in a typed-prefix body adapter's
explicit inputs and in the owner supplied to the adapter. Use a globally
injective map of `Resolved.DeclarationId`; preserve every binder index, spelling,
type, row position and actual runtime value. The source body and caller's type
meanings are unchanged. Do not claim covariance of allocation under arbitrary
injective maps of complete local IDs, which may change binder indices.

First prove `freshLocalId` commutes with owner-only relabeling on any supplied
scope. The scope may have mixed owners, sparse indices and repeated IDs. No
distinctness or caller-supplied equality of fresh indices is needed. Prove this
inside `Resolved.FreshIdentity`, where the private maximum-index recursion is
available; expose no new allocator implementation detail or frontend dependency.

Use this fact in a separate body-level module to commute value-free
`LocalTypeInputs.bindFresh` with the existing owner-only ID map. Preserve the
complete extended input bundle without constructing runtime inhabitants. Keep
existing runtime-parameter owner contracts and their imports unchanged; body
modules must not depend on runtime-parameter or runtime-function modules.

Transport independent exact typed-prefix elaboration and whole typing. Every
initializer is checked in its old scope, and the remaining source uses the
mapped, freshly extended scope. The resulting positional Core and result type
are identical. Preserve the checker's complete optional result by recursion on
the original body, including failures. A non-surjective injective owner map is
allowed; do not assume an inverse or derive rejection preservation from only a
one-way transport of successful evidence.

Finally lift this result through the actual input bundle's static projection
to optional body checking and same-fuel execution. The actual ordered values
are unchanged, so every complete Core result and genuine checkpoint is exactly
equal when the store is fixed. This differs from store replay, where states
retain distinct stores. No raw/cost owner-transport API or runtime-entry
extension is needed for this unit.

## Boundaries and validation

Keep all parser, source-binding, type-inference, call, Core and Wire behavior
unchanged. No guarantee is provided for owner maps that merge declarations,
arbitrary index-changing maps, inconsistent one-sided ID changes or allocating
fresh identities outside the supplied scope. Static nominal inputs require no
inhabitants; checked runtime claims use only values actually supplied.

Use independent source and completely parsed consumers. Cover mixed-owner sparse
scopes, repeated raw IDs, non-surjective injective owner shifts, multiple fresh
bindings, exact noncommutative positional Core, nominal static-only inputs and
actual opaque values. Retain whole failures at all relevant fuel values, full
state equality and genuine resumption at fixed stores. Include allocator
counterexamples for owner collapse and arbitrary injective index shifts.

Audit old and new public contracts and consumers for standard axioms and exact
registration. Verify focused and aggregate builds, parsed execution, full tests,
kernel/metadata policy and acyclic dependency direction. Keep proof files below
300 lines and commits small; diagnostics remain paused and scratch stays inside
the repository.
