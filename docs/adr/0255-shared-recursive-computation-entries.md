# ADR-0255: Shared explicit entries for recursive computation bodies

Status: Accepted
Date: 2026-09-09

## Context

ADR-0254 integrates recursive single-argument expressions into original mixed
bodies, with separate child checking, typing, elaboration and raw/cost contracts.
The explicit entries of ADR-0252 still select the older nonrecursive child.
Repeating their whole-record and argument-erasure proofs for each expression
profile would duplicate unchanged header and parameter policy.

The primary reference remains Rust commit
`18fd9f75d290df0070e21ee56e0a5691f232596f`: infer/mod.rs records root parameter
types in source order and the expected return type; infer/stmt.rs checks original
initializers, ordered statements and returns against that context. Reuse the
existing restricted header/parameter interpretation. This is not a claim that
excluded syntax is invalid in the full language or that expected-type source
lambda checking has been implemented.

## Decision

Add generic compilation, preparation and running over the shared computation
body checker. Their only expression parameter is the child checker, which sees
the original name table, type context and expression, never actual values.
Add independent compilation and preparation records parameterized separately by
child elaboration. Whole provenance retains the exact original declaration,
header, parameter construction, body Core and declared return agreement.

Reuse the existing data-only compiled/prepared records and their type erasure.
A record alone supplies no provenance, typing or safety. Preparation uses the
same actual bound input record both for body checking through its type-only view
and for execution through its original environment. Keep all original names,
IDs, ordering, annotations, spans and body nodes. Do not reconstruct values from
a compiled record or assume every static type has a runtime inhabitant.

Provide five concrete specializations to the recursive child: two provenance
relations and compile/prepare/run operations. Existing pure, application and
ADR-0252 computation endpoints and all old definitions/signatures stay unchanged.
No new family of specialized proof aliases or independent source runner is added.

## Four shared laws

Two exact-record Some-iff laws need only the universally quantified child
checker/elaboration correspondence. Original parameter declaration and binding
remain distinct; preparation evidence retains its own actual inputs.

Two full-Option factorization laws hold for every child checker, without child
semantic correctness, typing, raw evaluation or runtime-world premises.
Preparation mapped to its compiled record equals compilation followed by the
ordered argument-type guard. This guard includes both arity and source order.
The running factorization additionally uses the original argument values,
reversed once, and the separately supplied store.

A private checker-graph instantiation of the generic exact-record laws may
support these operational proofs. Keep it private and do not present it as
independent source semantics. Concrete semantic consumers instead provide the
real recursive child elaboration evidence and its established correspondence.

Retain all present Core results: declared type tag, literal value/store, faults
and genuine suspended states. Same-typed value or capture swaps pass the type
guard but can change results. Structural argument evidence does not validate
the supplied store or imply runtime-world safety. Apply the shared body laws
and existing Core cost/resumption machinery directly; add no redundant fuel,
None, safety or totality wrappers.

## Validation and limits

Use independent original Header/Declare/Bind/body certificates and separately
fixed Core/type/value/store/cost expectations. Cover nested-call initializers,
typed/inferred lets, discards, branches, captured/returned callables and actual
memory effects. Distinguish whole header/return rejection from accepted bodies,
and compile success from argument count/type-order rejection. Nominal value-free
compilation must need no fabricated inhabitants; Unit/product arguments remain
single list elements. Preserve old successful cases and old nested-entry None.

Test same-typed actual/capture swaps, store-dependent values and wrong payloads,
missing-cell faults, full fuel outcomes and genuine checkpoint resumption.
Include an arbitrary deliberately invalid child checker only as an operational
factorization consumer, without claiming independent typing or evaluation.

Keep files and commits small, run focused/aggregate/full tests, public and
consumer standard-axiom audits, kernel-policy and whitespace checks, and independent
reviews. Source closure construction, recursion under other expression roots,
global function resolution, general early returns, source-only fuel bounds,
unfuelled execution and arbitrary-store safety remain outside this unit.
