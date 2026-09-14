# ADR-0313: Reflection of owner-mapped endpoints and exact depth cutoffs

## Status

Accepted.

## Context

ADR-0311 transports original successes forward through injective owner maps.
ADR-0312 proves a complete Option equation at each unchanged executable budget.
Neither published interface yet recovers the original result from an arbitrary
observed mapped endpoint, or explicitly relates original judgments both ways.
The map need not be onto, so an inverse owner permutation cannot be assumed.

## Decision

Recover complete preimages of every actual owner-mapped original expression and
body success. The conclusion supplies an original value and final store, their
original evaluation, and exact equalities mapping them to the observed endpoint.
The observed value and store are arbitrary: membership in the map's image is a
conclusion, not a premise. Initial owners, names, captures and stores are mapped
as before, while source syntax and spans remain literal.

For the reverse implication, apply eventual completeness to the actual mapped
original derivation. At that finite witness use the full Option equation, recover
a successful unmapped runner result, then apply the old soundness theorem. Use
existing forward transport for the other existential implication. Specialize to
explicit mapped value/store endpoints using complete runtime-value injectivity
and list-map injectivity. Do not construct or assume an inverse or surjective map.

Also recover actual finite successful endpoints at the same budget directly from
the Option equation. Prove same-budget absence in both directions without a
success premise. These statements retain complete final stores and every nested
saved closure field, including duplicate rows and foreign-owner local IDs.

For each successful original expression/body, preserve one positive exact depth
cutoff shared by both runners. Below it both return None; at or above it both
return their complete corresponding endpoints. Obtain the old cutoff witness
from the existing successful-derivation theorem, then transport its entire result
profile. The original-success premise is essential: this is neither an executable
minimum finder nor a universal termination or successful-depth existence claim.

## Independent checks

Symbolic consumers construct both old and mapped originals independently from
existing constructors. A fresh binding followed by n grouped references has exact
body depth n+3; a saved unary call using that body has exact expression depth n+4.
Independent runner recursions establish these profiles before reflection. Recover
original endpoints, compare full values/stores by old determinism, and identify
the shared cutoff using the independently known H success and H-1 absence.
All ten production interfaces are reached by the compiled symbolic consumers.
Mixed fixtures keep arbitrary annotations, opaque Core values, source/Core/source
captures, duplicate and foreign rows, occupied fresh slots and separate nonempty
creation/invocation stores. Public call premises expose actual shape and lookups.

Boundary consumers first prove old host/Core-call, wrong-tag, missing-name and
distinct self-application failures at every budget, then deny all finite original
successes. Reflection excludes every arbitrary mapped endpoint; None does not
identify a failure reason. Independent mapped creation, identity-call and return
constructors, plus direct old/mapped runs at depths one, three and two, provide
successful controls. A nonsurjective shift admits success and non-return controls.

Parsed tests compare three complete handwritten AST shapes, every span, EOF and
empty diagnostics. Eight typed/inferred, mixed-argument, nonempty-store contexts
exercise five profiles at four budgets, giving 160 mapped-first observations.
Actual mapped Some endpoints feed old soundness and both preimage interfaces;
recovered full endpoints are checked against independent originals and old runs.
Eighty additional old H-1/H observations identify the shared cutoff with H.
The actual saved closure, fresh IDs 100/101/102, typed then inferred shadowing,
callee store, argument result/store and saved-body endpoint remain connected.
No preselected mapped endpoint replaces an observed result in the IO helpers.

## Preserved boundaries

Existing evaluators, original rules, maps, selectors, gates, image proofs, parser
and diagnostics are unchanged. There is no runtime-world/typing invariant, host
or Core dispatch, cell mutation, fault classifier, cost preservation, source/Core
image transport or whole-program termination theorem. Cell locations stay literal.

Keep proofs below 300 lines and commits within 300 changed lines. Verify exact
import-only ports, shared premises, full builds/tests, actual module ownership
and standard public axioms. Retain all source versions and complete failures.
