# ADR-0253: Recursive local computation calls

Status: Accepted
Date: 2026-09-09

## Context

ADR-0250 admits either a pure expression or one root application whose two
children are pure. ADR-0251 and ADR-0252 use that deliberately nonrecursive
child in mixed bodies and explicit function entries. These endpoints do not
accept `f(g(x))`, `maker(x)(y)`, or a group containing an application.

The fixed Rust reference is `18fd9f75d290df0070e21ee56e0a5691f232596f`.
Its `crates/parser/src/parse/expr_pat.rs` builds recursive arguments and
left-associated postfix calls; grouping adds no expression evaluation.
`crates/hir-ty/src/infer/expr.rs` recursively checks non-name callees and
arguments against callable parameter/result types. This adapter still models
only the explicit monomorphic, single-runtime-argument Function subset, not
general Invokable constraints, overloaded operators or global resolution.

Source lambda generation is a separate boundary. The same reference's
`infer_lambda` returns a Function type under an expected type, but otherwise
uses a nominal closure type. Core lambda typing also requires well-formed
parameter/result types. Existing actual closure arguments do not justify
silently synthesizing or inserting source lambdas into this profile.

## Decision

Add a separate `RecursiveLocalComputation` profile with pure, group and
application cases. Keep all existing Core, Resolved and frontend endpoints
unchanged. The checker recurses on the original callee and singleton argument
of a call, and on the original child of a group; every other root delegates
to the existing pure checker. Recursion decreases the original AST size.

Independent typing and elaboration retain original AST nodes, spans, caller
name-table priority, positional scope, exact Core and exact result type.
Application requires a Function-typed callee and the matching argument type.
Grouping emits the exact child Core with no wrapper or hidden binding.
Pure/group evidence may overlap; private compatibility lemmas reconcile the
two derivations without adding a public non-group premise.

Independent successful raw and cost judgments use the same three cases.
A call evaluates its original callee, then its argument in the resulting
store, then the actual closure body with the actual argument consed onto
its actual captures. Actual closure tags are not inferred from static types.
Application cost is the two recursive child costs plus the supplied closed
actual-body path cost plus three transitions. Grouping has zero overhead.
No checker, runtime-world or typing evidence enters these raw judgments.
An old pure raw derivation may skip an unsupported subtree. Compatibility
uses only the absence of an old pure root-call rule, not global call-freedom.

Use a separate caller-Core predicate with only two constructors: an existing
pure local fragment, or application of two recursively admitted callers.
It excludes newly generated closures and direct cell primitives but does
not restrict closure values, captures, called bodies or their effects.
Prove weakening, literal raw insertion equivalence and paired uniform-cost
paths for this predicate. Each called body's closed path is chosen once
before quantifying over continuations. Caller checkpoints may differ.

## Shared contracts and module boundaries

Publish exactly fourteen proof kernels:

- exact checker Some iff, independent typing iff elaboration, and Core typing;
- raw iff existence of cost and joint value/store/cost determinism;
- same-ID raw/Core equivalence, supplied-cost paths before any continuation,
  and exact closed-path cost equivalence;
- unchanged-Core/type embedding of old computation elaboration and unchanged
  value/store/cost embedding of old computation cost evidence;
- caller-fragment weakening and source membership, raw insertion equivalence,
  and paired paths with one cost chosen before every continuation.

Separate static definitions, raw definitions, static proofs, raw proofs,
execution proofs, embeddings and caller-fragment foundations. Keep every new
proof or consumer file below 300 lines; split execution proofs if necessary.
Do not add None/uniqueness aliases, endpoint runners, source-only bounds or
parallel fuel/resumption/safety wrapper families.

## Validation and limits

Consumers start from original syntax and independent static/raw certificates
and fixed Core expectations. Include nested argument calls, computed callees,
arbitrarily nested groups, higher-order/nominal value-free cases, same typed
but different actual captures, ordered effects and nontrivial checkpoints.
Compare old successful cases one way; retain old nested-call rejection.
Use all new kernels, genuine out-of-fuel resumption, actual faults and tags,
pending continuations, and arbitrary inserted caller values without claiming
that intermediate states or resulting closures are related by type erasure.

Run focused builds, aggregate syntax/tests, the full suite, all public and
consumer standard-axiom audits, kernel-policy and whitespace checks, and
independent reviews before publication.

Calls underneath operators, tuples or conditionals are not made recursive
by this step; pure such subtrees remain valid leaves. Zero/multiple arguments,
source lambdas, global calls, recursive functions, general early returns,
whole mixed-body integration, unfuelled execution and arbitrary-store safety
remain separate. The fourteen kernels are the basis for subsequent body
integration; no existing stronger pure store or source-bound law transfers.
