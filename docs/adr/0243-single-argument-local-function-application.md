# ADR-0243: Static single-argument local function application

- Status: Accepted
- Decision date: 2026-09-09
- Scope: A separate opt-in canonical expression adapter

## Evidence and decision

The fixed Rust revision `18fd9f75d290df0070e21ee56e0a5691f232596f`
recognizes known Function signatures and checks call arity and argument types
in `crates/hir-ty/src/infer/expr.rs` (405–603, 736–744). Indirect calls also
generate an Invokable obligation. Its builtin Function instances are registered
without conditions in `crates/hir-ty/src/solver/env.rs` (429–448). The arity-one
argument representation is exactly the original element, without an extra Unit
or product layer (761–775; `infer/desugar_view.rs`, 57–69). Specialize only this
known Function case; do not pretend to implement general Invokable resolution.

Introduce a separate static adapter for an original canonical root
`.call callee arguments` with exactly one original argument. The callee and
argument must both belong to the existing monomorphic local-expression profile,
under the same caller-provided name table and positional context. Require the
callee type `Core.Ty.function parameterType resultType` and the argument type
`parameterType`. Retain the exact Core application of the two original child
lowerings, with the declared function result type.

Define independent whole-call typing from the two original child typing
derivations. Separately define exact elaboration using each child's independent
resolution, positional lowering and resolved typing. Neither judgment has an
executable checker premise. Soundness and completeness must retain this exact
Core, not replace it with any expression of the same type. Prove correspondence,
whole-type and exact-result uniqueness, Core typing, precise child decomposition
and rejection characterization. Source ranges need no validity premise.

## Boundaries

This is a root application profile, not a new recursive expression language.
Groups and conditionals within either pure child use their existing rules;
their complete source children must still check. Outer grouping around a call,
nested calls, fields, UFCS, constructor calls, global lookup, source lambdas,
overload selection and comptime invocation remain outside this initial adapter.

Exactly one source argument is supplied unchanged. A product or Unit argument
remains one argument: `f((x,y))` is distinct from `f(x,y)`, and `f(())` is distinct
from `f()`. Do not introduce currying, argument packing, default Unit insertion,
literal coercion, new local identities or reordered child evaluation.

No existing pure source/resolved expression grammar, checker, body adapter,
runtime entry or generic theorem changes. In particular, old whole entries
containing calls remain outside their existing profile. The new module is not
imported by those lower layers. No parser, diagnostic, Core, or Core Wire
definition changes are needed.

Static contexts may contain nominal parameter/result types without supplying
runtime inhabitants. Actual supplied closures separately need captured-value
and body typing. Structural value typing does not prove that referenced cells
are allocated. A Core application is not in the existing local Core fragment;
do not apply its store-preservation or source-only fuel bounds to the call.

This unit adds no source-call evaluation relation, checked call runner or
function-entry integration. Later dynamic proofs must retain the actual
closure body and captured environment, original function-then-argument order,
threaded stores and actual body cost. Their safety premises must account for
the runtime store; a static call result alone is not a no-fault guarantee.

## Validation

Independent source and complete parsed consumers retain original call/argument
ranges, sparse mixed-owner and first-match duplicate rows, original child Core,
nominal static types, Unit/products, conditional child checking and equally typed
wrong-Core contrasts. Whole parsed declarations retain their existing rejection
while their call component has the new independent provenance.

Existing Core paths on actual supplied closures illustrate identity, captured
values, allocated versus missing cell reads and allocation effects. They do not
stand in for a new source-call runtime theorem. Check real suspended call frames
and preserve the distinction between arbitrary-continuation endpoints and completion.

Run focused/aggregate builds and full tests, audit all public declarations and
consumers with standard axioms only, and perform kernel-policy and whitespace checks and
independent reviews. Keep new files below 300 lines and split design, definitions,
proofs, consumers and publication into small commits. Diagnostics remain paused.
