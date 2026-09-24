# ADR-0168: Canonical runtime parameters to typed local inputs

- Status: Accepted
- Decision date: 2026-09-08
- Scope: input preparation for the explicit monomorphic frontend

## Decision

Connect a canonical function-parameter list and an equally long list of
explicitly typed runtime arguments to `LocalInputs`, starting from empty inputs.
The caller supplies the declaration owner and ADR-0167's type-name table.
Each argument contains a Core type, a Core value, and `Core.ValueHasType`
evidence. Comparing `Value.type` alone would not validate a closure body or
its captured environment, so it cannot replace that evidence.

Accept exactly runtime `.typed none name annotation` parameters whose
annotation independently denotes the argument's type. Match parameters and
arguments in written order, require exact arity, and reject repeated parameter
spellings in this restricted profile. Comptime parameters, recovery nodes,
unmapped or unsupported annotations, type mismatch, and either arity mismatch
produce `none`. This does not declare those forms invalid in the full source
language and does not implement staging, inference, coercion, or overloads.

Use the existing scope-relative `LocalInputs.bindFresh` primitive after each
successful match. Source parameter zero receives owner/index zero, and each
subsequent parameter receives the next index. Because the primitive prepends,
the final binding tables are in reverse parameter order, but each parameter
retains exactly its corresponding argument's type and value. Names, context,
and environment share the same identity order. No source expression traversal
or globally unique declaration allocation is implied.

## Independent specification and observations

Define an inductive binding judgment with explicit initial and final inputs:
the empty paired lists retain the inputs; a runtime parameter requires
independent type-name meaning and absence of its spelling among earlier
inputs, then binds its argument and judges the remaining paired lists.
The public empty-start judgment specializes this relation. Existing fresh input
construction is a primitive of this specification; successful execution of the
new list adapter is not a premise of the independent judgment.

Prove executable success iff this judgment, failure iff no result satisfies it,
result uniqueness, exact list lengths, argument type/value order, generated ID
order, and duplicate-free output names. Provide an exact parameter/argument-row
correspondence, so reversal cannot silently permute same-typed values. Reuse
the existing input lookup, checking, and execution guarantees rather than
introducing another evaluator.

## Validation and exclusions

Consumers cover empty inputs; too few and too many arguments; adjacent and
separated duplicate names; arbitrary spelling ranges; aliases and mismatched
types; comptime and recovery nodes; unsupported annotations; and exact paired
order for multiple same-typed arguments. Include explicitly typed closure and
cell-reference inputs without claiming store allocation from structural typing.

Parse actual canonical parameter lists or signatures, bind their actual AST
parameters, and use the result with existing parsed local-expression checking
and execution. Check exact selected argument values, Core positions, nonempty
stores, failed checking, and fuel exhaustion/completion. Full function-call and
return behavior, modifiers, generics, constraints, function bodies, mutable
declarations, runtime argument decoding, and wire endpoints remain outside this
input-preparation adapter.

Audit all public declarations against the permitted standard kernel axioms,
run focused and aggregate builds and full tests, and verify kernel and
whitespace policies. Keep new proof files below 300 lines.
