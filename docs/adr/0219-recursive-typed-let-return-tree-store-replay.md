# ADR-0219: Store replay for recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Independent body-level store replay and own-store observations

## Decision

Add a separate store-properties module for ADR-0217/0218. Replay every raw
recursive tree path and cost at any replacement store, preserving the original
owner, name table, actual environment, source body, result value and exact cost.
The new final store equals the replacement initial store. Single returns reuse
their established replay law. A binding replays its old-scope initializer and
then the same extended tail with the same obtained value. A conditional replays
its condition and only the same selected arm in the original scope.

Raw replay requires no annotation meaning, unused name, whole acceptance,
runtime typing, ID alignment or store-validity premise. Fresh identities depend
on the unchanged owner and name table, not on store contents. Do not reconstruct
typed inputs, weaken Core, change sibling allocation or invent inhabitants.
Unknown annotations and rejected unselected children may still have replayable
raw paths without establishing whole-source acceptance.

State bidirectional raw and cost equivalences with the original
`finalStore = initialStore` conjunct retained. Dropping that equality would
wrongly admit arbitrary final stores. Lift the independent cost replay through
the existing checked-runner typed-cost characterizations: at the same inputs,
body and fuel, completed observations have the same type/value with their own
initial stores, and exhaustion exists on one store iff it exists on the other.
Whole checking remains mandatory and does not depend on the store.

## Boundaries

Do not identify complete results or checkpoints from different stores. Each
genuine checkpoint is resumed separately using ADR-0218 and retains its own
store. Do not add a redundant raw cost-bound, None, owner or resumption API.
No old adapter, entry, allocator, parser/Core/Resolved/Wire or scope-policy change.

The claims are not general Core store independence. A pending cell-load frame
can return different stored values, or fault on an empty store even with zero
remaining fuel while an allocated-store run exhausts. ADR-0217 paths under any
retained continuation reach their endpoints; they do not execute those frames
or justify arbitrary-continuation runner replay. Returning an opaque cell
reference or captured closure here still entails no allocation or invocation.

## Validation

Use independent arbitrary-depth raw paths/costs, actual typed inputs, asymmetric
selected branches, strict unused initialization and opaque existing values.
Test distinct stores and genuine conditional/initializer/tail checkpoints,
resuming each separately across insufficient/exact/surplus chunks. Include raw
success with whole rejection, explicit unequal complete results, final-store
equality necessity and a pending-load counterexample. Keep the source, owner,
inputs, exact Core and fuel fixed in each store comparison.

Audit all six public contracts and source/parsed consumers, standard axioms,
registration and acyclic body dependencies. Run focused/aggregate builds,
actual parsed execution, full tests, and kernel-policy and whitespace checks. Keep
proof files below 300 lines, commits small, diagnostics paused and scratch in
the repository.
