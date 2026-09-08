# ADR-0157: Typed local input construction and execution

- Status: Accepted
- Decision date: 2026-09-08
- Scope: bundled typed inputs for the canonical local-expression fragment

ADR-0158 extends the underlying local-expression adapter with Boolean
negation and extends the unused-name laws to its operand; the bundle and
checked runner keep their existing input/result representations.

## Decision

Provide a single explicit input bundle for ADR-0156's local-expression adapter.
Each row retains a caller-supplied spelling, structured local ID, Core type,
runtime value, and an independent `Core.ValueHasType` derivation. The bundle
requires distinct IDs. Ordered name, type-context, and runtime-environment
tables are projections of the same rows; their identity order and positional
typing agree by construction rather than by separate caller obligations.

Names need not be distinct. The first equal name selects its row, just as in
the existing ordered name table. Distinct IDs ensure that this row's identity
then retrieves its own type and value. This restriction is specific to the
convenience bundle; the older raw-table APIs retain their explicit behavior
for duplicate identities.

An empty bundle and a fresh-binding constructor preserve the ID invariant.
The latter uses the established `freshLocalId` allocator with a caller-supplied
declaration owner and all IDs currently in the bundle. Freshness is relative
to these inputs, not to an unexamined source program. A newly prepended binding
with an existing name hides the previous name entry; fresh identity alone does
not promise preservation of source expressions mentioning that spelling.

For the supported identifier/group/conditional fragment, an independent
avoidance judgment requires that no child use the newly added spelling.
Under this condition, fresh insertion preserves and reflects source typing
and evaluation. Checked Core free positions shift by one, while the type and
check-failure result are unchanged. Completed executions agree on type, value,
and both stores. This does not identify their fuel witnesses or suspended
states, and does not analyze free names in unsupported canonical constructors.

## Checked execution

Checking uses the existing canonical local-expression adapter and the derived
name/type tables. Execution first checks the expression, then runs the exact
returned Core expression in the derived runtime environment. It retains both
the checked type and the full stateful Core result.

An absent result means failure of this limited checker, not rejection by the
whole source language. In particular, insufficient fuel is a present
out-of-fuel result, not an absent check result. Core fuel still counts machine
transitions, not input construction, parsing, checking, or EVM gas.

Independent source typing characterizes successful checking. Checked inputs
have a typed source evaluation, preserve the store, return that value at every
sufficiently large fuel, and never machine-fault. A completed execution reflects
to the independent source evaluation and its assigned value type. The reverse
evaluation-to-execution direction retains source typing or successful checking:
raw evaluation alone can ignore a statically unsupported unselected branch.

## Boundary and validation

This is a proof-carrying Lean library input, not a decoder or a dynamic validator
for arbitrary external values. A structural value typing derivation does not
assert that a cell location is allocated or a store is well-typed. The current
fragment can return such a value without invoking or dereferencing it; future
effectful fragments must establish their own stronger environment conditions.

The bundle does not collect source declarations, resolve imports, fix mutable
source binding semantics, or allocate globally unique program IDs. Parser,
Core, Oracle, and frozen wire behavior remain unchanged. Tests cover automatic
identity alignment, exact row lookup, fresh repeated insertion, repeated-name
priority, check failure versus fuel exhaustion, selected branches, exact
results/stores, and the essential whole-expression static-check premise.
Public axioms, focused/aggregate builds, kernel policy, metadata, and the full
test suite are audited before publication.
Executable source-text regressions also pass parsed expressions through fresh
input construction, checking, and the stateful runner for both branch choices.
