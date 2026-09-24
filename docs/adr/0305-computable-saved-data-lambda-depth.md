# ADR-0305: Computable depth for lookup-known saved data lambdas

## Status

Accepted.

## Context

ADR-0304 bounds direct unmarked unary lambda applications from their syntax.
For a reference callee, the actual body belongs to the saved runtime closure,
not to the caller's expression. Caller and saved owners, names and capture rows
may differ; closure creation does not save a store snapshot for invocation.

## Decision

Define `savedDataLambdaDepthBound argument body` as one plus the maximum of
one, the data-expression argument bound and the actual saved data-body bound.
One is the positive depth required by the reference lookup. All call children
receive the same predecessor budget, so the bounds combine by maximum.

Require independent first-match caller name and capture lookup facts identifying
the complete `sourceClosure source savedOwner savedNames savedCaptured` datum.
Retain separate `SourceUnaryLambdaShape`, `ClosedSourceDataExpression` and
`ClosedSourceDataBody` premises. The callee is an identifier, not an arbitrary
expression; argument and body success are not admission premises. Unmarked
typed or inferred parameters and return annotations remain inert source syntax.

Invert an original call and compare its callee with an independent original
reference witness. Determinism fixes every actual saved field and callee store;
shape uniqueness fixes the actual parameter and body. The direct data bounds
apply to the caller argument and the freshly extended saved body, preserving
the actual intermediate stores, full mixed value and complete final store.
No eventual-completeness, threshold or image oracle supplies the bound.

Compose with existing evaluator soundness and success monotonicity to prove
exact success iff, whole Option stability above the bound, sufficient-depth None
iff no original successful endpoint, and bound None iff None at every budget.
The decision laws do not assume successful argument or body evaluation.

## Independent checks

A symbolic family first constructs original creation, first pickup, caller
argument and fresh saved-body witnesses. An independent runner recursion proves
the exact cutoff n+3 for arbitrary saved body nesting, with all annotations,
mixed captures and stores retained. Creation and invocation stores are separate.
For every proposed caller-syntax-only bound, a second theorem keeps the AST
`f(x)` and caller names fixed while choosing a deeper saved body. The proposed
budget fails although an original successful endpoint exists. This explains why
the new bound must depend on the saved datum, not merely the caller AST.

Negative consumers first exclude original success. An existing caller value
cannot fill a missing saved capture; an existing saved value cannot evaluate a
missing caller argument. A duplicate first non-Bool saved guard does not fall
through to a later Boolean row, including after the actual fresh extension.

Parsed consumers compare whole handwritten ASTs, all source spans, EOF and zero
diagnostics for saved parameter-return and free-value-return lambdas and fixed
`f(x)`. Actual evaluator-created source, owner, name and capture fields flow into
the caller's first pickup without replacement. Independently constructed lookup,
body and call witnesses precede the new laws; actual body and call endpoints
are compared in full. The 32 mixed-context cases include fresh parameter returns,
saved free-value returns, both lexical failures, duplicate rows and opaque source
and Core closures. Creation owner/store and invocation owner/store stay distinct.

## Preserved boundaries

No original evaluation rule, evaluator, data gate, primitive, selector, image
contract, lowering or typing definition changes. Existing image statements and
proofs remain untouched. This is not an unconditional bound for arbitrary saved
closures, general callees, nested calls or whole-language evaluation. It does
not establish runtime typing, Core costs, fault classification, effects or
closure conversion. Missing-callee classification remains a separate question.

Proof files stay below 300 lines. Require focused and full builds, complete tests,
kernel policy, whitespace, public axiom checks, exact import-only ports
and actual new-module ownership inspection before small commits. Only the
standard three proof axioms are permitted; all compiler-generated names and
flags are retained as observed, without prototype-generated-name equivalence.
