# ADR-0195: Terminal conditional return-body semantics

- Status: Accepted
- Decision date: 2026-09-08
- Scope: separate explicit-table conditional-return-body adapter

## Decision

Add a nonrecursive adapter for a body containing exactly one canonical `if`
statement with an explicit `else`. Its two arms must each be accepted by the
existing singleton-return-body adapter: either `return;` or `return expression;`.
Check the condition as Bool, check both arms under the original table/context,
and require equal branch types. Lower directly to Core `ifE` without allocating
identities or inserting source bindings. Preserve the exact condition and arm
elaborations in an independent relation, separate from source typing.

Define raw source evaluation independently of checking, evaluating the condition
then only the selected return arm. Retain exact values and all stores. Define
exact cost as condition cost plus selected arm cost plus two Core transitions.
The structural fuel bound uses condition bound plus the maximum arm bound plus
two; unsupported whole-body shapes receive zero, not an acceptance certificate.
Prove typing/checking equivalence, exact elaboration uniqueness, raw determinism,
store preservation, type safety, cost erasure/existence/determinism, checked Core
evaluation correspondence, exact transition paths and fuel boundaries. Prove
completion at the structural bound and resumption from genuine suspended states.

Expose dedicated `LocalInputs.checkConditionalReturnBody?` and
`runConditionalReturnBody?` interfaces. Existing singleton `ReturnBody` and
runtime-function compiler/preparation APIs remain unchanged in this unit.
The separate adapter is a foundation for a later explicitly specified entry
integration, not a claim that current runtime-function compilation accepts it.

## Boundaries

Both written arms must check even when a condition is known to select one.
Raw success may skip an invalid other arm and does not imply whole acceptance.
Reject absent else, empty or multiple statements, nested statement conditionals,
statements before/after the conditional or arm return, mismatched return types,
non-Bool conditions and invalid expressions. Conditional *expressions* inside
an arm remain supported by the existing expression adapter.

No general early-return unwinding, sequential statements, mutable locals,
assignment, calls, loops, source recursion, parser change, Oracle/wire change
or diagnostic-proof work is included. Retain original identities and actual
runtime values; preserve existing runtime alignment premises. Completed-run
reflection does not gain a typed-runtime-environment premise.

## Validation

Independent consumers exercise both selected arms, exact Core shape and result
types, nonempty stores, existing Unit/Word/Bool/cell/closure return values,
unequal branch costs, all fuel thresholds, actual continuation checkpoints and
same-state resumption. Negative cases distinguish raw skipped-arm success from
whole checker failure and confirm the old singleton and entry APIs stay narrow.
Parsed consumers use complete canonical bodies and actual typed inputs, retain
spans/order and test all structural and type boundaries.

Audit every new public declaration for standard axioms only; run focused and
aggregate builds, full tests, kernel/metadata/forbidden-token/whitespace checks.
Keep new proof files below 300 lines, commits small and separated by role,
scratch repository-local and paused diagnostic files untouched.
