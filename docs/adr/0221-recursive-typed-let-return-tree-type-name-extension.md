# ADR-0221: Type-name extension for recursive typed let/return trees

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Preserve accepted recursive bodies under first-match meaning extension

## Decision

Add two separate proof modules for ADR-0216/0218, reusing the existing
`TypeNameTable.Extends` relation. Extension preserves every original first-match
meaning; it is not list inclusion and does not require unique keys. Keep source,
owner, supplied static or actual input bundle, exact Core and return type fixed.
Do not rebind parameters or synthesize values when the annotation table changes.

Transport independent exact elaboration and whole typing by their constructors.
A singleton return does not inspect the type-name table. A binding transports
its annotation meaning and recursive tail while retaining the old-scope
initializer, unused-name evidence, declared type and fresh identity. A terminal
conditional retains its guard and transports both recursive arms from the same
original input scope. An unselected invalid child is still a whole-body failure.
No runtime inhabitants are needed for static nominal types.

Derive preservation of successful exact checker pairs from independent
elaboration. With extension in both directions, prove equality of the full
optional checker result, including rejection, without equating the tables.
One-way extension alone does not preserve absence: a formerly unknown annotation
in either branch may gain a meaning and make the whole original body acceptable.

Lift both contracts through the unchanged `LocalInputs.toTypeInputs` adapter.
Preserve every successful complete optional runner pair at the same fuel and
store, including genuine suspended states, using the same positional values.
Mutual semantic extension gives full optional runner equality for arbitrary
source and fuel. Do not strengthen one-way preservation to full Option equality
or restrict the preserved payload to completed return values.

## Boundaries and validation

Preserving all original rows does not permit a prepended conflicting meaning:
lookup is first-match. Later conflicting duplicates can be harmless, and safe
same-meaning duplicates need not be fresh. Qualified component keys remain
component lists, not flattened strings. No new type-name lookup policy is added.

Keep all existing owner maps, allocator, raw/cost judgments, source bounds,
resumption contracts and function entries unchanged. The old entry still only
accepts its outer-prefix profile. No parser/Core/Resolved/Wire change, inference,
default initialization, shadowing, general calls or arbitrary-body policy.

Consume all eight new contracts with independent arbitrary-depth elaboration
and whole typing, mixed annotation meanings, scope-local sibling bindings,
noncommutative initializers and static nominal inputs without inhabitants.
Fully parsed original declarations retain the same input bundle before and
after extension. Check asymmetric exact costs, actual opaque values, every
relevant fuel and genuine conditional/initializer/tail checkpoints, including
own-checkpoint multi-chunk resumption. Exercise one-way repair of unknown
unselected annotations, mutual preservation of rejected shapes and names,
harmless duplicate rows, and conflicting first-match overrides.

Audit public and consumer axioms, registration and dependency direction; run
focused/aggregate builds, actual parsed execution, full tests, kernel checks and
whitespace checks. Keep proof files below 300 lines and commits
small. Diagnostics remain paused; all scratch stays in the repository.
