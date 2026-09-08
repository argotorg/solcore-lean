# ADR-0220: Owner covariance for recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Exact static provenance and whole optional results under owner maps

## Decision

Add owner-only covariance for ADR-0216/0218 in two separate proof modules.
A globally injective `DeclarationId` map relabels every supplied input identity
through the existing `ownerLocalIdMap` and maps the current allocator owner.
Keep the original syntax, type-name table, Core expression and return type fixed.
No runtime inhabitants are required to transport independent elaboration or
whole source typing, including nominal static input types.

Reuse the existing `freshLocalId_map_owner` and `bindFresh_mapOwner` laws on
complete supplied scopes. They account for mixed owners and sparse indices;
the fresh index is not input length. Single returns reuse their ID transport.
Each binding retains annotation meaning and unused-name evidence, relabels its
old-scope initializer and transports only its freshly extended tail. Each
conditional relabels its guard and both arms from the same original inputs.
Sibling fresh identities may coincide scope-locally; do not thread allocations
across siblings or impose a new global uniqueness or input-name assumption.

Prove complete optional checker equality by recursion on original syntax size,
including all rejected shapes and both branches. The owner map need not be
surjective; do not infer failure preservation from one-way success transport
or assume an inverse map. The annotation interpreter does not depend on owners.

Lift the full checker result through actual `LocalInputs.toTypeInputs` and
the existing identity-map projection laws. Actual ordered values, including
opaque cells and captured closures, are unchanged. At the same fuel and store,
the exact Core therefore gives identical whole optional runner results and
genuine checkpoints, not merely equal return values. This same-store guarantee
is distinct from ADR-0219's own-store observation equivalences.

## Boundaries and validation

An arbitrary injective `LocalId` map that changes indices need not commute with
fresh allocation; an owner-collapsing map is not admissible. Do not broaden
these claims to such maps, invent owner counters, add reverse maps or allocate
runtime values. Existing global owner/fresh-binding helpers remain unchanged.

No raw/cost owner API, new source bound/resumption law, runtime-entry integration,
parser/Core/Resolved/Wire change, type-name policy, inference, defaults or broader
binding/early-return policy is introduced. Existing entry owner laws remain
restricted to their existing outer-prefix profile.

Use independent arbitrary-depth alternating trees, mixed-owner/sparse scopes,
non-surjective owner shifts, sibling same-ID bindings and noncommutative
initializers. Separate nominal value-free typing from actual opaque runtime
values. Preserve full checker rejection for invalid unselected children and
full same-store results at every relevant fuel, including genuine conditional,
initializer and tail checkpoints resumed without resetting values or frames.
Contrast owner collapse and arbitrary index shifts at the allocator boundary.

Audit all five contracts and source/parsed consumers, standard axioms,
registration and dependency direction, focused/aggregate builds, actual parsed
execution, full tests and kernel/metadata/whitespace policy. Keep proof files
below 300 lines, commits small, diagnostics paused and scratch in the repository.
