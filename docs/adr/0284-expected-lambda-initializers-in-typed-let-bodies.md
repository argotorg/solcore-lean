# ADR-0284: expected lambda initializers in typed-let bodies

## Status

Accepted; a standalone adapter for one original leading explicitly typed let
whose initializer is a unary lambda, followed by an unchanged shared computation
body. Canonical Rust remains fixed at
`18fd9f75d290df0070e21ee56e0a5691f232596f`. All old executable entry points,
source admission and literal insertion contracts remain unchanged.

## Canonical evidence and chosen scope

At the fixed pin, `crates/hir-ty/src/infer/stmt.rs:64–103` passes an explicit let
annotation as the initializer's expected type. In contrast, an ordinary let with
no annotation and a direct lambda initializer takes the inference path without
an expected type. The latter creates the separate nominal closure typing path
identified in ADR-0281; do not treat it as an annotated function-typed let.

`crates/hir/src/nameres/body_resolver.rs:40–55` resolves the annotation and
initializer before adding the new let binding. Its lambda rule at 166–184 opens
a separate parameter scope only inside the initializer. Thus an initializer's
reference to the let spelling sees an existing outer binding, or is unresolved
if none exists. It is not an implicitly recursive reference to the new let.
The new let binding is visible only in the original tail.

ADR-0281 through ADR-0283 already supply original expected lambda headers,
elaboration and source-only typing. Connect these to this explicit expected-type
boundary without replacing the existing general shared body checker or expanding
its recursive child interface. This is a real annotation-to-initializer connection,
not an extra wrapper around arbitrary successful whole-body checking.

A raw source-closure value universe is not introduced here. Existing raw child,
body, environment and store interfaces contain Core values, including Core bodies
inside external closures. A source-AST closure sum needs separate environment,
store and external-call interoperability relations; adding elaboration as a raw
creation premise would not solve this. Closure exclusion from typed cell payloads
does not justify changing raw stores, which allow arbitrary values. The fixed
backend's surviving-lambda rejection also remains distinct from frontend typing.

## Elaboration and checking

Add `ExpectedLambdaLetBody` for an original block whose first statement is
`let name : annotation = lambda;`, with exactly that explicit annotation and
initializer present. Preserve the original block/statement ranges, annotation,
initializer expression, and tail statements without rewriting or normalization.
Resolve the annotation using the unchanged outer first-match type-name table.
The annotation may name a table entry denoting a function type; it need not use
literal function-type syntax.

Define independent `ExpectedLambdaLetBodyElaborates` with the annotation's
structural meaning, an ADR-0282 initializer elaboration under the original outer
inputs at that expected type, and an original shared-tail elaboration under
exactly `initial.bindFresh owner name.value declaredType`. Return the literal
Core let containing the initializer Core and tail Core, with the tail's type.
The initializer judgment supplies the unary/runtime-lambda restriction and both
fixed-profile component well-formedness guards.

Expose `elaborateExpectedLambdaLetBody?`, parameterized by the existing fixed
child checker. Interpret the original annotation, invoke the existing expected
lambda checker on the original initializer in the old inputs, then invoke the
unchanged shared body checker on the original tail in the new let inputs.
Return the Core expression and inferred tail type. Other leading statement
shapes, inferred lets, missing initializers and non-lambda initializers are
outside this opt-in profile, not language-wide errors.

Prove exact checker/elaboration correspondence and absence using only the fixed
child's exact checker correspondence. Separately prove Core typing using only
child Core typing and the existing initializer/tail typing laws. Retain original
head/tail provenance and the exact fresh-row layout in an inversion theorem.
No checker law supplies child Core safety or runtime values.

The initializer parameter and outer let binder each start from the same original
input IDs in different scopes. They may therefore receive the same fresh ID
number, but never coexist as the same row in one scope. Do not thread the lambda's
inner parameter row into the outer tail or bind the outer let before checking
the initializer. Outer same-name shadowing remains allowed.

## Independent source typing

In a separate `ExpectedLambdaLetBodyTyping` module, define source-only typing
from the original annotation meaning, ADR-0283 initializer source typing in the
old inputs, and shared tail source typing in the new let inputs. Its definition
must not contain a Core expression, a checker graph or existential elaboration.
Prove typing iff elaboration existence from child typing correspondence, then
typing iff checker-result existence with the additional exact child checker law.
Include these three declarations in the same change rather than postponing the
source-only interpretation of the new body form.

## Consumers and validation

Construct original source typing/elaboration before invoking checker laws. Cover
explicit/inferred lambda parameters, annotation aliases and first-match priority,
old same-spelling captures versus the new tail binding, missing or wrongly typed
outer self references, owner-filtered sparse IDs and disjoint-scope fresh-ID reuse.
Exercise original tail calls, ordinary subsequent bindings, branches, returns and
returning the closure itself; the unchanged tail checker still rejects further
unsupported lambda initializers. Contrast inferred lets and non-lambda heads
with this restricted profile without declaring them invalid canonical programs.

Any tests of generated Core closure creation or invocation must retain actual
captures/stores and remain explicitly Core consumers. No source raw evaluation,
general canonical backend execution or new runtime-safety theorem is supplied.

Run focused and aggregate builds, full tests, exact standard-only public and
consumer axiom catalogs, independent reviews, old byte/header/import checks,
kernel-policy, EOF, and whitespace checks. Keep each implementation, proof, and consumer
file below 300 lines and use separately verified small commits.

## Non-goals

No old shared checker, recursive child or function-entry admission changes;
no inferred-let nominal closure inference, implicit recursion, general expected
propagation, automatic nesting of this adapter, raw source-closure conversion or
operational correspondence. Parser and diagnostic proofs remain paused.
